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

(defun* jez--grammar-:macro (parser macro-name args &rest body)
  (check-type macro-name symbol)
  (check-type args list)
  (puthash macro-name
           `(lambda ,args ,@body)
           (jez-parser--rules parser)))

(defun* jez--grammar-:primitive (parser primitive-name handler)
  (check-type primitive-name symbol)
  (puthash primitive-name handler (jez-parser--primitives parser)))

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

    ;; (:rule NAME ...) -> (:macro NAME () '(: ...)).
    (when (eq (car clause) :rule)
      (setf clause `(:macro ,(cadr clause) () '(: ,@(cddr clause)))))

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
                for (nil args . def) = (gethash rule-name rules)
                ;; If def looks like (lambda () '(: . X)) for some X,
                ;; generate (,rule-name ,X). Otherwise, use the more
                ;; general (:macro ,rule-name ,args ,@def) syntax. The
                ;; former syntax is what :rule produces.
                collect (if (and (not force-macro)
                                 (null args)
                                 (setf inner (car def))
                                 (null (cdr def))
                                 (eq (car-safe inner) 'quote)
                                 (setf inner (cdadr inner))) 
                            `(,rule-name ,@inner)
                          `(:macro ,rule-name ,args ,@def)))))))

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

(defun* jez--primitive-cut (env &rest terms)
  (jez--make-cut (jez-environment--parser env)
                 (loop for term in terms
                              collect (jez-compile-rd env term))))

(defun* jez--primitive-literal (env &rest terms)
  (jez-with-slots (parser) (jez-environment env)
    (jez--make-sequence
     parser
     (loop for char across (mapconcat #'identity terms "")
           collect (jez--make-char parser char)))))

(defun* jez--primitive-eob (env &rest terms)
  (when terms
    (error "eob takes no arguments"))
  (jez--make-predicate parser `(eobp)))

(defconst jez-root-grammar
  '(;; Fundamental combinators.
    (:primitive : jez--primitive-sequence)
    (:primitive * jez--primitive-repeat)
    (:primitive / jez--primitive-cut)
    
    ;; Literal handling (note: the compiler automagically transforms
    ;; an RD X into (literal X) if X is a string or (literal "X") if X
    ;; is a character.
    (:primitive literal jez--primitive-literal)

    ;; Built-in predicates
    (:primitive eob jez--primitive-eob)

    ))

(provide 'jezebel-grammar)
