;;;
;;; Parse grammar descriptions into parsers.  This file contains code
;;; for translating user-visible grammars into the internal
;;; representation used by the (interrelated) compilation and parsing
;;; engines.  jezebel-compiler takes care of taking the rule
;;; definitions (RDs) we build here and turning them into
;;; intermediate-representation nodes (IRNs).  The compiler also
;;; contains the code to optimize the IRN graph and to generate a lisp
;;; functions that implement the parser described by the
;;; (optionally-optimized) IRN graph.
;;;

(require 'cl)
(require 'jezebel-util)
(require 'jezebel-engine)

(defconst jez-root-grammar
  '(
    ;; Sequence: match all forms in order.  Most of the time, a
    ;; primitive or rule that accepts a variable number of form
    ;; arguments combines these arguments into an implicit sequence.
    (:primitive : jez--primitive-sequence)

    ;; Repeat: Match given forms (which are enclosed in an implicit
    ;; sequence) zero or more times.
    (:primitive * jez--primitive-repeat)

    ;; Ordered choice: try matching all given forms, yielding the
    ;; first one that successfully matches.
    (:primitive / jez--primitive-ochoice)

    ;; Semantic action: from the perspective of the parsing engine, a
    ;; semantic action has zero width and always succeeds.  The given
    ;; lisp forms are evaluated in an implicit progn; the final value
    ;; is ignored.  The lisp code may have limited side effects; see
    ;; the manual for details.
    (:primitive ! jez--primitive-semantic-action)

    ;; Semantic predicate: all given lisp forms are evaluated in an
    ;; implicit progn, and iff the resulting form evaluates to nil,
    ;; the parser backtracks (or fails if we're out of choice points).
    ;; Predicates must be free of side effects; they may be repeated,
    ;; rearranged, or deleted entirely by the optimizer.
    (:primitive :satisfies jez--primitive-semantic-predicate)

    ;; Literal handling (note: the compiler transforms an RD X into
    ;; (literal X) if X is a string or (literal "X") if X is a
    ;; character.
    (:primitive :literal jez--primitive-literal)

    ;; Various built-in predicates.
    (:rule bob (:satisfies (bobp)))

    (:rule eob (:satisfies (eobp)))

    ;; One-or-more operator.
    (:macro +
            (lambda (&rest rules)
              `(: ,@rules (* ,@rules))))

    ;; Define an AST node.
    (:macro ast-node
            (lambda (name &rest rules)
              `(: (! (jez--push-ast-node state ',name))
                  ,@rules
                  (! (jez--pop-ast-node state)))))))

(define-functional-struct (jez-environment
                           (:constructor jez--make-environment)
                           (:conc-name jez-environment--))

  "A lexical environment used during rule compilation."

  ;; Hash table mapping each rule-name (a symbol) to a function
  ;; generating the primitive expansion of this rule.
  (rules (make-hash-table))

  ;; Hash table mapping each primitive name to a function generating
  ;; an IRN for a particular invocation of this primitive.
  (primitives (make-hash-table))

  ;; Hash table memozing the result of jez-compile-rd.
  (expansions (make-hash-table :test 'equal))

  ;; The parser for this environment
  (parser :read-only t :type jez-parser))


;; -------------
;; Rule compiler
;; -------------

(defun* jez--normalize-rd (rd)
  (etypecase rd
    (symbol     (jez--normalize-rd (list rd)))
    (character  (jez--normalize-rd (char-to-string rd)))
    (string     (jez--normalize-rd (list :literal rd)))
    (list       rd)))

(defun* jez-expand-rd-1 (env rd)
  "Expand a rule RD once in ENV.  Return a list (EXPANDED NEW-RD)
where EXPANDED is true if we we were able to expand the rule, and
NEW-RD is the expanded definition, or the original definition if
we were unable to expand."
  (let* ((norm-rd (jez--normalize-rd rd))
         (ruledef (gethash (car-safe norm-rd)
                           (jez-environment--rules env))))
    (if ruledef
        (list t (apply ruledef (rest norm-rd)))
      (list (not (eq rd norm-rd)) norm-rd))))

(defun* jez-compile-rd (env rd)
  "Return an intermediate node (IRN) for rule-definition RD.
Compile the rule if necessary.  We don't actually return an IRN
instance --- we return a \"promise\", concretely, a symbol, the
value-slot of which will eventually point to the corresponding IR
node."

  ;; First, look for RD in the cache.  If it's already there,
  ;; return the IRN.  Otherwise, try expanding the rule, and
  ;; if that works, recursively invoke jez-compile-rd on the
  ;; expansion.

  ;; If the rule wasn't expanded, we're either at a primitive or an
  ;; invalid rule.  If we're at an invalid rule, signal an error.
  ;; Otherwise, call the corresponding primitive handler to allocate a
  ;; symbol for the new state and set its `ir' property, then return
  ;; the state.

  (jez-with-slots (primitives expansions) (jez-environment env)
    (or
     ;; If we've already compiled this rule, return its state.
     (gethash rd expansions)

     ;; Check whether this rule definition can be expanded to a more
     ;; fundamental rule definition. If so, use the IRN for that
     ;; expansion.
     (destructuring-bind (expanded-p expanded-rd) (jez-expand-rd-1 env rd)
       (when expanded-p
         (jez-compile-rd env expanded-rd)))

     ;; We weren't able to expand the rule using a :rule/:macro
     ;; definition, so it must either be a primitive or an error.
     ;; If it's a primitive, let the primitive handler come up with
     ;; the IRN for the rule.  To break infinite recursion, return a
     ;; symbol naming the IRN instead of the IRN itself: we'll
     ;; resolve each of these symbols to a real IRN by the time we
     ;; finish building the graph.

     (let ((handler (or (gethash (car-safe rd) primitives)
                        (error "invalid rule %S: no primitive for %S"
                               rd (car-safe rd))))
           (irn-symbol (gensym "jez-irn-promise")))
       (puthash rd irn-symbol expansions)
       (set irn-symbol (apply handler env (rest rd)))))))

(defun* jez--grammar-:include (env other-grammar)
  ;; Incorporate the definitions in OTHER-GRAMMAR into ENV.
  (jez--slurp-grammar other-grammar env))
(put :include 'jez-grammar-clause-handler #'jez--grammar-:include)

(defun* jez--grammar-:primitive (env primitive-name handler)
  "Define a new kind of grammar primitive."
  (check-type primitive-name symbol)
  (check-type handler (or symbol function))
  (puthash primitive-name handler (jez-environment--primitives env)))
(put :primitive 'jez-grammar-clause-handler #'jez--grammar-:primitive)

(defun* jez--grammar-:alias (env old-name &rest new-names)
  "Define a new name for an existing rule."
  (loop for new-name in new-names
        do (jez--grammar-:macro env new-name
                                `(lambda (&rest args)
                                   `(,',old-name ,@args)))))
(put :alias 'jez-grammar-clause-handler #'jez--grammar-:alias)

(defun* jez--grammar-:macro (env macro-name &optional arglist &rest body)
  (unless (symbolp macro-name)
    (error "Rule/macro name must be symbol, not %S" macro-name))
  (when (keywordp macro-name)
    (error "Rule/macro name cannot be a keyword symbol"))
  (puthash macro-name
           (cond (;; Let users define a macro as (:macro name
                  ;; handler-function) to let them write macro
                  ;; definitions out-of-line.
                  (or (and arglist (symbolp arglist))
                      (eq (car-safe arglist) 'lambda))
                  (unless (null body)
                    (error "An out-of-line :macro cannot have a body: %S"
                           macro-name))
                  arglist)

                 ;; Otherwise, we build a lambda for the user.
                 (t
                  (or (listp arglist)
                      (error "Invalid arglist: %S" arglist))
                  `(lambda ,arglist ,@body) ))
           (jez-environment--rules env)))
(put :macro 'jez-grammar-clause-handler #'jez--grammar-:macro)

(defun* jez--grammar-:rule (env rule-name &rest body)
  "Define a plain grammar rule in the current namespace."

  ;; Every plain rule is actually a macro of no arguments that just
  ;; returns its definition.
  (let ((clause
         `(:macro ,rule-name () '(: ,@body))))
    (apply (get :macro 'jez-grammar-clause-handler) env (cdr clause))))
(put :rule 'jez-grammar-clause-handler #'jez--grammar-:rule)

(defvar jez--non-keyword-handler nil
  "This lexically-bound variable holds the name of the keyword
that jez--slurp-grammar prepends to grammar clauses that do not
themselves begin with keywords.  By changing this variable,
grammar clause handlers can divide a grammar description into
\"sections\"."  )

(defun* jez--slurp-grammar (grammar env)
  "Read rules from GRAMMAR into ENV.
GRAMMAR is a passive data structure that describes the rules for
building a parser."

  ;; Sometimes it's convenient to name a variable containing a grammar
  ;; instead of including it inline.
  (when (symbolp grammar)
    (setf grammar (symbol-value grammar)))

  ;; A grammar is a list of s-expressions.  The car of each expression
  ;; tells us how to process it: we require it to be a symbol and call
  ;; the function jez--grammar-SYMBOL to process the clause.  If no
  ;; such function exists, we assume we're looking at a rule.
  (loop
   with jez--non-keyword-handler = :rule
   for handler = jez--non-keyword-handler
   for clause in grammar do
   (progn
     (unless (consp clause)
       (error "each grammar clause must be a sexp"))

     ;; Every grammar clause must begin with a symbol.
     (unless (symbolp (car clause))
       (error "grammar clause must begin with symbol, not %S" clause))

     (when (keywordp (car clause))
       (setf handler (car clause))
       (setf clause (cdr clause)))

     (apply (or (get handler 'jez-grammar-clause-handler)
                (error "%S is not a known clause type" handler))
            env clause))))

(defun* jez-compile (grammar &optional (top-rd '(: top eob)))
  "Compiles GRAMMAR into a jez-parser. Return the new parser instance.
TOP-RD denotes with which the generated parser will begin
parsing; by default, we begin with the rule called `top'."

  ;; First, create an empty parser.  To this new grammar, add the
  ;; default rules, then the rules from the passive
  ;; grammar-description data structure GRAMMAR.  Now the parser has a
  ;; full set of parsed rules, but it still doesn't have an
  ;; intermediate state and so can't parse anything.

  ;;
  ;; At this point, we let the compiler take over by telling it to
  ;; generate an intermediate representation node (IRN) for the rule
  ;; definition TOP-RD.  This top IRN contains direct or indirect
  ;; references to all parser states reachable from the top.

  ;;
  ;; Now we have a valid IRN graph, but it's probably not a very good
  ;; one.  The next step is to give this IRN graph to the optimizer,
  ;; which will give us an IRN graph based on the input IRN graph.
  ;;

  ;;
  ;; Finally, we return the parser, which is now ready to use.
  ;;

  (let* ((parser (jez--make-parser))
         (env (jez--make-environment :parser parser))
         top-irn)
    (jez--slurp-grammar jez-root-grammar env)
    (jez--slurp-grammar grammar env)
    (setf top-irn (jez-compile-rd env top-rd))
    (setf (jez-parser--initial-state parser)
          (jez-irn-compile top-irn parser))
    parser))


;; ----------
;; PRIMITIVES
;; ----------
;;
;; These functions define the primitives from which users can build
;; their grammar rules.  Each of these primitives is associated with a
;; user-accessible name in jez-root-grammar above.  Grammars, with
;; care, can define their own primitives in order to support opaque
;; "white-box" parsers that might be useful for parsing specific
;; constructs.
;;
;; Each primitive-handler function takes an environment as its first
;; argument; the rest of the arguments are the ones supplied in the
;; rule-definition --- that is, the arguments are symbolic, not other
;; IR nodes.  A primitive-handler function is expected to call
;; jez-compile-rd to transform any argument rules to IRNs; the
;; compiler breaks the possible recursion that might result.
;;
;; Each primitive handler returns an IRN representing the state given
;; by its arguments.  Calls to primitive handler functions are
;; memoized.
;;

(defun* jez--primitive-sequence (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-sequence
     parser
     (loop for term in terms
           collect (jez-compile-rd env term)))))

(defun* jez--primitive-repeat (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-repeat
     parser
     (apply #'jez--primitive-sequence env terms))))

(defun* jez--primitive-ochoice (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-ochoice
     parser
     (loop for term in terms
           collect (jez-compile-rd env term)))))

(defun* jez--primitive-literal (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-sequence
     parser
     (loop for char across (mapconcat #'identity terms "")
           collect (jez--make-char parser char)))))

(defun* jez--primitive-semantic-predicate (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-predicate parser `(progn ,@terms))))

(defun* jez--primitive-semantic-action (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-action parser `(progn ,@terms))))

(provide 'jezebel-grammar)
