(require 'cl)
(require 'eieio)

(defstruct (xp-rule
            (:constructor xp--make-rule)
            (:conc-name xp-rule--))
  "A rule in an xp grammar."
  
  name
  args
  definer-function)

(defstruct (xp-compiled-rule
            (:constructor xp--make-compiled-rule)
            (:conc-name xp-compiled-rule--))
  "A compiled rule in a particular parser."

  ;; the xp-parser for which we were compiled
  parser

  ;; function object that begins matching this rule
  matcher-function)

(defstruct (xp-grammar
            (:constructor xp--make-grammar)
            (:conc-name xp-grammar--))
  "An xp grammar for some language."
  
  ;; hash table mapping rule names (symbols) to xp-rule instances.
  rules)

(defstruct (xp-parser
            (:constructor xp--make-parser)
            (:conc-name xp-parser--))
  
  "A compiled parser that can be used to transform a series of 
tokens into an AST."

  ;; The grammar from which this parser was constructed
  grammar

  ;; The initial state of this parser
  initial-state

  ;; A map of rule expansions.
  ;;
  ;; The keys are lists in the form (rule-name arg_1 arg_2 ... arg_N),
  ;; and the hash table is a :test 'equal table.
  ;;
  ;; The values are symbols, the function slots of which contain a
  ;; function representing the given parse state.
  ;;
  states)

(defstruct (xp-state
            (:constructor xp--make-state)
            (:conc-name xp--state))
  
  "A particular state of a parse operation."

  ;; Reference to the parser that created us
  parser

  ;; Stack (lisp list) of backtracking alternatives. Each entry is an
  ;; xp-choice-point instance.
  choice-points

  ;; Stack (lisp list) of data values to use when we don't backtrack.
  data)

(defstruct (xp-environment
            (:constructor xp--make-environment)
            (:conc-name xp--environment))

  "A lexical environment used during rule compilation."

  
  
  )

(defun* xp-make-empty-grammar ()
  "Create a new empty grammar."
  (xp--make-grammar :rules (make-hash-table)))

(defmacro* xp-grammar-define-rule (grammar rule-name args &body body)
  "Define or redefine a rule in a grammar.

GRAMMAR gives the grammar in which to define the rule, identified
by symbol RULE-NAME.  If RULE-NAME already exists in the grammar,
its definition is discarded and this definition substituted.

ARGS is a normal CL-function lambda list describing the
arguments for this rule.  FORMS is a sequence of forms evaluated
under an implicit PROGN yielding a rule-definition as described
below when evaluated under ARGS.  The definition as a
whole is assumed to be a pure function of its arguments.

GRAMMAR is evaluated. The remaining arguments are not.

A rule-definition (RD) is a value having one of the following
forms:

  RULE-NAME

    RULE-NAME is a symbol: equivalent to (RULE-NAME)
  
  (: RD_1 RD_2 ... RD_N)

    Sequence: matches all given rule definitions in sequence.
    Each item in the sequence can be a general rule definition of
    the form presently being described.

    In addition, each element of the sequence can have 
    one of the following forms:

    (<- BINDING-NAME RD)

      Remember value: BINDING-NAME is a symbol and RD is a
      generic rule definition.  BINDING-NAME is bound to the
      result of RD for the remainder of the sequence and can be
      used in the definition of subsequent RDs.

    This form yields a list of all matched forms.

  (-> RD_1 RD_2 ... RD_N RESULT-FORM)

    Filtered sequence: like sequence above, but yield the value
    of RESULT-FORM instead.  The lexical environment of
    RESULT-FORM includes the symbol `all' which is the list of
    all results, and also any values bound with `<-'.

  (/ RD_1 RD_2 ... RD_N)

    Ordered choice: tries each rule definition in sequence until
    one matches, yielding that match.  Each rule is a general
    rule definition of the form presently being described.
    
  (* RD)

    Repetition: matches RD zero or more times, yielding a
    possibly-empty list of all results.  RD is a general rule
    definition of the form presently being described.

  (:when PREDICATE RD)

    Conditional: when PREDICATE evaluates evaluates to true, try
    to match RD, and if it succeeds, yield its value.  Otherwise,
    fail.

  ::

    Cut (also commonly known as commit): stop backtracking here.

  (RULE-NAME PARAM_1 PARAM_2 ... PARAM_N)

    Matches the definition of RULE-NAME.

  In addition, the symbol `prev-rule' anywhere in DEFINITION will
  be replaced by the previous definition of RULE-NAME in GRAMMAR.
"

  `(xp-grammar--%define-rule ,grammar ',rule-name ',args ',@body))

(defun* xp-grammar--%define-rule (grammar rule-name args &rest FORMS)
  "Implementation of `xp-grammar-define-rule'.

All the arguments have the same meaning."

  (assert (symbolp rule-name))
  (assert (listp args))

  (puthash rule-name
           `(lambda ,args ,@FORMS)
           (xp-grammar-rules grammar)))

(defun* xp-parser--compile-rule-1 (parser rd &optional environment)
  "Expand a rule RD once and return the expanded rule.

RD is any legal rule definition. Return another rule
definition (which will always be a list) or an xp-compiled-rule
instance. On failure, raise an error.
"

  ;; XXX: use environment

  (etypecase rd
    (symbol
     ;; A bare symbol, rule, is equivalent to (rule).
     (xp-parser--compile-rule-1 parser (list rd) environment))

    (xp-compiled-rule
     ;; We're done.
     rd)

    (list
     ;; Decode the rule
     (let* ((rule-def (gethash (car rd)
                               (xp-grammar--rules
                                (xp-parser--grammar parser)))))
       
       (when rule-def
         (setf rule-def
               (apply (xp-rule--definer-function rule-def)
                      (rest rd))))

       rule-def))))

(defun* xp-parser--compile-rule (parser rd
                                &rest
                                kw-args
                                &key
                                environment
                                stop)
  
  "Expand the rule definition RD in PARSER.

This function expands RD completely, yielding an xp-compiled-rule
instance. Throws on error.

If ENVIRONMENT is supplied, use it for lexical name lookups. It
defaults to the top-level lexical environment for PARSER's
grammar.

STOP is a predicate. It is called with one argument, the rule
we're about to expand. If it returns t, we return that rule
instead of further expanding it.

If ENVIRONMENT is present, use it to expand the value of RD.
"
  (setf rd (xp-parser--compile-rule-1 parser rd environment))

  (when (symbolp rd)
    ;; A bare symbol is equivalent to calling a rule definition with no
    ;; arguments.
    (setf rd (list rd)))
  
  (cond
   ((xp-compiled-rule-p rd)
    ;; We're done.
    rd)
   
   ((not (symbolp (car-safe rd)))
    ;; If we didn't finish compiling the rule, we should have gotten
    ;; another rule definition back.
    (error "Invalid generated rule %S" rd))
   
   ((funcall stop rd)
    rd)

   
   
   )
  
  (etypecase rd
    (xp-compiled-rule
     ;; We're done.
     rd)
             
    ((or symbol list)
     ;; We can still do more expansions here.
     (apply #'xp-parser--compile-rule parser rd kw-args))))

(put 'xp-grammar-define-rule 'lisp-indent-function 3)

(defun xp--:-rule (args)
  "Magic for sequences."

  ;; 
  
  )

(defun xp--*-rule (args)
  "Magic for repetition."
  
  )

(defun xp--/-rule (args)
  "Magic for prioritized choice."

  
  
  )

(defconst xp-root-grammar

  (let ((root (xp--make-grammar
               :rules (make-hash-table :test 'equal))))

    ;; Create magic
    
    (xp-grammar-define-rule root : (&rest args)
      (xp--:-rule args))

    (xp-grammar-define-rule root * (&rest args)
      (xp--*-rule args))
    
    (xp-grammar-define-rule root / (&rest args)
      (xp--/-rule args))
    
    root)
  

  "The grammar inherited by all other grammars.")


(defun* xp-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  
  )

(defun* xp-parser--precompile-rule (parser))

(defun* xp-grammar-create-parser (grammar top-rd)
  "Compiles grammar GRAMMAR into a xp-parser."

  ;; First, create a basic parser.
  
  (let* ((parser (xp--make-parser
                  :grammar grammar
                  :states (make-hash-table :test 'equal))))

    ;; Then, eagerly initialize the rule tree.
    (setf (xp-parser--initial-state parser)
          (xp-parser--compile-rule top-rd))
    
    ;; Parser is now ready to use to begin parsing
    parser))

(defun* xp-state++ (state)
  "Perform one step of a parse.

Update STATE by side effect, calling preconfigured callback
functions as needed.
"
  (funcall (pop (xp-state-control-stack state))
           state))

(xp-make-grammar 
  `((:import xp-base-grammar :as x)

    (hello-target
     (/ (x.keyword "world")
        (x.keyword "blarg")))
  
    (top 
     (-> (<- first-word (x.keyword "hello"))
         (syntactic-ws)
         (<- second-word hello-target)
         
         (concat first-word " " second-word)))))


(provide 'xp)
