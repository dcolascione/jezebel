;;;
;;; Parse grammar descriptions into parsers.
;;;

(require 'cl)
(require 'jezebel-util)
(require 'jezebel-engine)

(define-functional-struct (jez-environment
                           (:constructor jez--make-environment)
                           (:conc-name jez-environment--))

  "A lexical environment used during rule compilation."

  ;; The parser for this environment
  (parser :read-only t :type jez-parser))

(defun* jez--normalize-rd (rd)
  (etypecase rd
    (symbol     (jez--normalize-rd (list rd)))
    (character  (jez--normalize-rd (char-to-string rd)))
    (string     (jez--normalize-rd (list 'literal rd)))
    (list       rd)))

(defun* jez-expand-rd-1 (env rd)
  "Expand a rule RD once in ENV.  Return a list (EXPANDED NEW-RD)
where EXPANDED is true if we we were able to expand the rule, and
NEW-RD is the expanded definition, or the original definition if
we were uanble to expand."

  (let* ((norm-rd (jez--normalize-rd rd))
         (ruledef (gethash (car-safe norm-rd)
                           (jez-parser--rules
                            (jez-environment--parser env)))))
    (if ruledef
        (list t (apply ruledef (rest norm-rd)))
      (list (not (eq rd norm-rd)) norm-rd))))

(defun* jez-compile-rd (env rd)
  "Return the jez-irn for rule-definition RD.
Compile the rule if necessary."

  ;; First, look for RD in the state cache.  If it's already there,
  ;; return the IRN.  Otherwise, try expanding the rule, and
  ;; if that works, recursively invoke jez-compile-rd on the
  ;; expansion.

  ;; Otherwise, if the rule wasn't expanded, we're either at a
  ;; primitive or an invalid rule.  If we're at an invalid rule,
  ;; signal an error.  Otherwise, call the corresponding primitive
  ;; handler to allocate a symbol for the new state and set its `ir'
  ;; property, then return the state.

  (jez-with-slots (parser) (jez-environment env)
    (jez-with-slots (expansions primitives) (jez-parser parser)

      (or
       ;; If we've already compiled this rule, return its state.
       (gethash rd expansions)

       ;; Check whether this rule definition can be expanded to a more
       ;; fundamental rule definition. If so, use the IRN for that
       ;; expansion.
       (destructuring-bind (expanded-p expanded-rd) (jez-expand-rd-1 env rd)
         (when expanded-p
           (jez-compile-rd env expanded-rd)))

       ;; We weren't able to expand the rule further. It is either a
       ;; primitive or not really a rule.
       (puthash
        rd
        (or (apply (or (gethash (car-safe rd) primitives)
                       (error "invalid rule %S: no primitive for %S"
                              rd (car-safe rd)))
                   env (rest rd))
            (error "primitive handler unexpectedly returned nil: %S"
                   (gethash (car-safe rd) primitives)))
        expansions)))))

(defun* jez--grammar-:include (parser other-grammar)
  (jez--slurp-grammar other-grammar parser))

(defun* jez--grammar-:macro (parser macro-name macro-definition)
  (check-type macro-name symbol)
  (check-type macro-definition function)
  (puthash macro-name macro-definition (jez-parser--rules parser)))

(defun* jez--grammar-:primitive (parser primitive-name handler)
  (check-type primitive-name symbol)
  (puthash primitive-name handler (jez-parser--primitives parser)))

(defun* jez--grammar-:alias (parser old-name &rest new-names)
  "Define a new name for an existing rule."
  (loop for new-name in new-names
        do (jez--grammar-:macro parser new-name
                                `(lambda (&rest args)
                                   `(,',old-name ,@args)))))

(defun* jez--slurp-grammar (grammar parser)
  "Read rules from GRAMMAR into PARSER and return PARSER."

  (when (symbolp grammar)
    (setf grammar (symbol-value grammar)))

  (dolist (clause grammar)
    ;; Every grammar clause must begin with a symbol.
    (unless (and (car-safe clause) (symbolp (car clause)))
      (error "invalid grammar clause %S" clause))

    ;; (X ...) is equivalent to (:rule X ...) if X is a non-keyword
    ;; symbol. This formulation alows users to express simple rules
    ;; simply.
    (unless (keywordp (car clause))
      (push :rule clause))

    ;; (:rule NAME ...) -> (:macro NAME (lambda () '(: ...))).
    (when (eq (car clause) :rule)
      (setf clause `(:macro ,(cadr clause)
                            (lambda () '(: ,@(cddr clause))))))

    ;; Call the function that processes this clause.
    (apply (or (intern-soft (format "jez--grammar-%s" (car clause)))
               (error "unknown clause type %S" (car clause)))
           parser
           (cdr clause)))
  parser)

(defun* jez-compile (grammar &optional (top-rd '(: top eob)))
  "Compiles GRAMMAR into a jez-parser. Return the new parser instance.
TOP-RD denotes with which the generated parser will begin
parsing; by default, we begin with the rule called `top'."

  ;; Start with an empty parser and empty lexical environment.
  (let* ((parser (jez--slurp-grammar grammar (jez--make-parser)))
         (env (jez--make-environment :parser parser))
         (top-irn (jez-compile-rd env top-rd)))

    (setf top-irn (jez--optimize parser top-irn))

    ;; Compile the IR nodes to real lisp functions.
    (setf (jez-parser--initial-state parser)
          (jez-irn-compile top-irn parser))

    ;; Parser is now ready to use.
    parser))

(defun* jez-describe-parser (parser &key force-macro)
  "Return the grammar parsed by PARSER."
  (jez-with-slots (rules primitives) (jez-parser parser)
    (let ((rule-names
           (loop for x being the hash-keys of rules
                 collect x))
          (primitive-names
           (loop for x being the hash-keys of primitives
                 collect x)))
      (setf rule-names (sort rule-names #'string<))
      (setf primitive-names (sort primitive-names #'string<))
      `(,@(loop for primitive-name in primitive-names
                for primitive = (gethash primitive-name primitives)
                collect `(:primitive ,primitive-name ,primitive))
        ,@(loop with inner
                for rule-name in rule-names
                for rule-def = (gethash rule-name rules)
                for (form-name args . def) = rule-def
                ;; If def looks like (lambda () '(: . X)) for some X,
                ;; generate (,rule-name ,X). Otherwise, use the more
                ;; general (:macro ,rule-name ,def) syntax. The former
                ;; syntax is what :rule produces.
                collect (if (and (not force-macro)
                                 (eq form-name 'lambda)
                                 (null args)
                                 (setf inner (car def))
                                 (null (cdr def))
                                 (eq (car-safe inner) 'quote)
                                 (setf inner (cdadr inner)))
                            `(,rule-name ,@inner)
                          `(:macro ,rule-name ,rule-def)))))))

(defun* jez--primitive-sequence (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-sequence parser
                        (loop for term in terms
                              collect (jez-compile-rd env term)))))

(defun* jez--primitive-repeat (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-repeat
     parser
     (apply #'jez--primitive-sequence env terms))))

(defun* jez--primitive-ochoice (env &rest terms)
  (jez--make-ochoice (jez-environment--parser env)
                 (loop for term in terms
                              collect (jez-compile-rd env term))))

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

(defconst jez-root-grammar
  '(

    ;; Fundamental combinators.

    ;; Sequence: match all forms in order.  Most of the time, a
    ;; sequence is implied when another rule takes a variable number
    ;; of forms.
    (:primitive : jez--primitive-sequence)
    (:alias ! and seq sequence)

    ;; Repeat: Match given forms (which are enclosed in an implicit
    ;; sequence) zero or more times.
    (:primitive * jez--primitive-repeat)

    ;; Ordered choice: try matching all given forms, yielding the
    ;; first one that successfully matches.
    (:primitive / jez--primitive-ochoice)
    (:alias / ochoice ordered-choice)

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

    ;; Literal handling (note: the compiler automagically transforms
    ;; an RD X into (literal X) if X is a string or (literal "X") if X
    ;; is a character.
    (:primitive literal jez--primitive-literal)

    ;; Various built-in predicates.
    (bob (:satisfies (bobp)))
    (:alias bob buffer-start)

    (eob (:satisfies (eobp)))
    (:alias eob buffer-end)

    ;; One-or-more operator.
    (:macro +
            (lambda (&rest rules)
              `(: ,@rules (* ,@rules))))
    
    ;; Define an AST node.
    (:macro ast-node
            (lambda (&rest rules)
              `(: (! (jez--push-ast-node state))
                  ,@rules
                  (! (jez--pop-ast-node state)))))

    ))

(provide 'jezebel-grammar)
