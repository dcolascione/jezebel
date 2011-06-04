(require 'cl)

(defstruct (jez-rule
            (:constructor jez--make-rule)
            (:conc-name jez-rule--))
  "A rule in an jez grammar."

  ;; Symbol naming this rule.
  name

  ;; Function that expands this rule
  expander
  )

(defstruct (jez-compiled-rule
            (:constructor jez--make-compiled-rule)
            (:conc-name jez-compiled-rule--))
  "A rule compiled for a specific parser with specific arguments."

  ;; the uncompiled version of this rule
  rule

  ;; the parser for which the above rule was compiled
  parser

  ;; sexp that gets pushed onto the success-stack when we're about to
  ;; match this rule
  matcher
  
  )

(defstruct (jez-grammar
            (:constructor jez--make-grammar)
            (:conc-name jez-grammar--))
  "An jez grammar for some language."
  
  rules

  primitives

  )

(defstruct (jez-parser
            (:constructor jez--make-parser)
            (:conc-name jez-parser--))
  
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

(defstruct (jez-state
            (:constructor jez--make-state)
            (:conc-name jez--state))
  
  "A particular state of a parse operation."

  ;; Reference to the parser that created us
  parser

  ;; Stack (lisp list) of states to enter when backtracking
  or-stack

  ;; Stack (lisp list) of states to enter when successful
  success-stack

  ;; Stack (lisp list) of data values
  trail
  )

(defstruct (jez-environment
            (:constructor jez--make-environment)
            (:conc-name jez-environment--))

  "A lexical environment used during rule compilation."

  ;; The parser for this environment
  parser
  )

(defun* jez-make-empty-grammar ()
  "Create a new empty grammar."
  (jez--make-grammar :rules (make-hash-table)))

(defmacro* jez-grammar-define-rule (grammar rule-name args &body body)
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

  (= RD_1 RD_2 ... RD_N RESULT-FORM)

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

  `(jez-grammar--%define-rule ,grammar ',rule-name ',args ',@body))

(defun* jez-grammar--%define-rule (grammar rule-name args &rest FORMS)
  "Implementation of `jez-grammar-define-rule'.

All the arguments have the same meaning."

  (check-type rule-name symbol)
  (check-type args list)
  (puthash rule-name
           `(lambda ,args ,@FORMS)
           (jez-grammar--rules grammar)))

(defun* jez-grammar-define-primitive (grammar name definition)
  "Define a new primitive NAME for GRAMMAR.

DEFINITION is a function."

  (check-type name symbol)
  (check-type definition function)
  (puthash name definition (jez-grammar--primitives grammar)))

(defun* jez-expand-rule-1 (env rd)
  "Expand a rule RD once in ENV and return the expanded rule.

RD is any legal rule definition. Return a new rule definition or
nil if we were not able to expand this rule."

  ;; A bare symbol RULE is equivalent to (RULE).
  (when (symbolp rd)
    (setf rd (list rd)))

  (let* ((parser (jez-environment--parser env))
         (grammar (jez-parser--grammar parser))
         (rules (jez-grammar--rules grammar))
         (rule-name (car-safe rd))
         (ruledef (gethash rule-name rules)))

    (when ruledef
      (apply (jez-rule--expander ruledef) (rest rd)))))

(defun* jez-expand-rule (env rd)
  "Expand the rule definition RD in PARSER.
Return the expanded rule, which is always a list."

  (let ((new-rd (jez-expand-rule-1 env rd)))
    (if new-rd
        (jez-expand-rule env rd)
      rd)))

(defun* jez-compile-rd (env rd)
  "Return the matcher for the given rule-definition RD.
Compile the rule if necessary."

  (let* ((expanded-rd (jez-expand-rule env rd))
         (grammar (jez-parser--grammar parser))
         (parser (jez-environment--parser env))
         (states (jez-parser--states parser)))

    ;; If we already have a definition for this rule, use that.
    ;; Otherwise, compile a new instance.

    (or (gethash expanded-rd states)
        (let ((rule-sym (gensym "jez-compiled-rule-")))
          (puthash expanded-rd rule-sym states)
          (setf (symbol-function rule-sym)
                (apply (first expanded-rd) env (rest rd)))
          rule-sym))))

(put 'jez-grammar-define-rule 'lisp-indent-function 3)

(defun* jez--*-finish (state))

(defun* jez--:-compile (env terms)
  "Definition of sequence primitive."

  ;;
  ;; Consider (: A_0 A_1 ... A_N ). We have N + 1 states, denoted by
  ;; an integer i ranging over [0, N].  Either:
  ;;
  ;;   - we're about to parse A_i, 0 <= i < N
  ;;   - we've finished parsing, i = N
  ;;
  ;; When we're in state i and need to match A_i next, we need to pass
  ;; into the code for matching A_i enough information for it to then
  ;; try parsing A_(i+1), possibly many times if backtracking is
  ;; allowed.
  ;;

  ;; This function generates a function that can be pushed onto one of
  ;; our state stacks as the i=0 state.  The generated function
  ;; references other states functions that we compile for this
  ;; sequence.

  (let ((term (first terms))
        (terms (rest terms)))
    
    )

  (let ((compiled-terms
         (reverse
          (mapcar
           (lambda (term)
             (jez-compile-rd env term))
           terms))))
    
    (lambda (state)
      (jez--*-finish state ,(length terms))
      ,@(mapcar (lambda (compiled-term)
                  `(jez-push-success state ,compiled-term))))))


(defun* jez--* (env term)
  "Definition of repetition primitive."

  ;; if we're backtracking, one choice point for each
  ;; repetition. otherwise, similar to `:' above.
  
  )

(defun* jez--/ (env terms)
  "Definition of prioritized choice primitive."

  ;; choice point for each item
  
  )

(defconst jez-root-grammar
  (let ((root (jez--make-grammar
               :rules (make-hash-table :test #'eq)
               :primitives (make-hash-table :test #'eq))))

    ;; Initial semi-magical rules.
    
    (jez-grammar-define-primitive root ': #'jez--:)
    (jez-grammar-define-primitive root '* #'jez--*)
    (jez-grammar-define-primitive root '/ #'jez--/)
    root)
  "The grammar inherited by all other grammars.")


(defun* jez-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  
  )

(defun* jez-grammar-create-parser (grammar top-rd)
  "Compiles grammar GRAMMAR into a jez-parser."

  ;; First, create a basic parser.
  
  (let* ((parser (jez--make-parser
                  :grammar grammar
                  :states (make-hash-table :test 'equal))))

    ;; Then, eagerly initialize the rule tree.
    (setf (jez-parser--initial-state parser)
          (jez-parser--expand-rule top-rd))
    
    ;; Parser is now ready to use to begin parsing
    parser))

(defun* jez-state++ (state)
  "Perform one step of a parse.

Update STATE by side effect, calling preconfigured callback
functions as needed.
"
  (funcall (pop (jez-state-control-stack state))
           state))

;; '(jez-make-grammar 
;;   `((:import jez-base-grammar :as x)

;;     (hello-target
;;      (/ (x.keyword "world")
;;         (x.keyword "blarg")))
  
;;     (top 
;;      (<- first-word (x.keyword "hello"))
;;      (syntactic-ws)
;;      (<- second-word hello-target)
         
;;      )))


(provide 'jezebel)
