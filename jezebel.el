(require 'cl)

(defstruct (jz-rule
            (:constructor jz--make-rule)
            (:conc-name jz-rule--))
  "A rule in an jz grammar."
  
  name
  args
  definer-function)

(defstruct (jz-compiled-rule
            (:constructor jz--make-compiled-rule)
            (:conc-name jz-compiled-rule--))
  "A compiled rule in a particular parser."

  ;; the jz-parser for which we were compiled
  parser

  ;; function object that begins matching this rule
  matcher-function)

(defstruct (jz-grammar
            (:constructor jz--make-grammar)
            (:conc-name jz-grammar--))
  "An jz grammar for some language."
  
  ;; hash table mapping rule names (symbols) to jz-rule instances.
  rules)

(defstruct (jz-parser
            (:constructor jz--make-parser)
            (:conc-name jz-parser--))
  
  "A compiled parser that can be used to transform a series of 
tokens into an AST."

  ;; The grammar from which this parser was constructed
  grammar

  ;; The initial state of this parser
  initial-state

  ;; A map of rule ejzansions.
  ;;
  ;; The keys are lists in the form (rule-name arg_1 arg_2 ... arg_N),
  ;; and the hash table is a :test 'equal table.
  ;;
  ;; The values are symbols, the function slots of which contain a
  ;; function representing the given parse state.
  ;;
  states)

(defstruct (jz-state
            (:constructor jz--make-state)
            (:conc-name jz--state))
  
  "A particular state of a parse operation."

  ;; Reference to the parser that created us
  parser

  ;; Stack (lisp list) of backtracking alternatives. Each entry is an
  ;; jz-choice-point instance.
  choice-points

  ;; Stack (lisp list) of data values to use when we don't backtrack.
  data)

(defstruct (jz-environment
            (:constructor jz--make-environment)
            (:conc-name jz--environment))

  "A lexical environment used during rule compilation."

  
  
  )

(defun* jz-make-empty-grammar ()
  "Create a new empty grammar."
  (jz--make-grammar :rules (make-hash-table)))

(defmacro* jz-grammar-define-rule (grammar rule-name args &body body)
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

  `(jz-grammar--%define-rule ,grammar ',rule-name ',args ',@body))

(defun* jz-grammar--%define-rule (grammar rule-name args &rest FORMS)
  "Implementation of `jz-grammar-define-rule'.

All the arguments have the same meaning."

  (assert (symbolp rule-name))
  (assert (listp args))

  (puthash rule-name
           `(lambda ,args ,@FORMS)
           (jz-grammar-rules grammar)))

(defun* jz-parser--compile-rule-1 (parser rd &optional environment)
  "Ejzand a rule RD once and return the ejzanded rule.

RD is any legal rule definition. Return another rule
definition (which will always be a list) or an jz-compiled-rule
instance. On failure, raise an error.
"

  ;; XXX: use environment

  (etypecase rd
    (symbol
     ;; A bare symbol, rule, is equivalent to (rule).
     (jz-parser--compile-rule-1 parser (list rd) environment))

    (jz-compiled-rule
     ;; We're done.
     rd)

    (list
     ;; Decode the rule
     (let* ((rule-def (gethash (car rd)
                               (jz-grammar--rules
                                (jz-parser--grammar parser)))))
       
       (when rule-def
         (setf rule-def
               (apply (jz-rule--definer-function rule-def)
                      (rest rd))))

       rule-def))))

(defun* jz-parser--compile-rule (parser rd
                                &rest
                                kw-args
                                &key
                                environment
                                (stop-p #'ignore))
  
  "Ejzand the rule definition RD in PARSER.

This function ejzands RD completely, yielding an jz-compiled-rule
instance. Throws on error.

If ENVIRONMENT is supplied, use it for lexical name lookups. It
defaults to the top-level lexical environment for PARSER's
grammar.

STOP-P is a predicate function. It is called with one argument,
the rule we're about to ejzand. If it returns t, we return that
rule instead of further ejzanding it.

If ENVIRONMENT is present, use it to ejzand the value of RD.
"
  (setf rd (jz-parser--compile-rule-1 parser rd environment))

  (when (symbolp rd)
    ;; A bare symbol is equivalent to calling a rule definition with no
    ;; arguments.
    (setf rd (list rd)))
  
  (cond
   ((jz-compiled-rule-p rd)
    ;; We're done.
    rd)
   
   ((not (symbolp (car-safe rd)))
    ;; If we didn't finish compiling the rule, we should have gotten
    ;; another rule definition back.
    (error "Invalid generated rule %S" rd))
   
   ((funcall stop-p rd)
    ;; User told us to stop
    rd)
   
   (t
    ;; Ejzand the rule again
    (apply #'jz-parser--compile-rule parser rd kw-args))))

(put 'jz-grammar-define-rule 'lisp-indent-function 3)

(defun* jz--:-rule (env terms accum)
  "Compile sequences magically."

  ;; (XXX: We also need to handle annotating the parse tree with
  ;; attributes as we go, but we can do that later.  For now, let's
  ;; focus on the match.)
  ;;
  ;; We need to build up a sequence of states we enter when we match a
  ;; seqeuence so we can point subrules at the "next" state. For
  ;; example, consider (: a b c), which parses three terms.
  ;; 
  ;; We have four states:
  ;;
  ;;  1. before a
  ;;  2. after a, before b
  ;;  3. after b, before c
  ;;  4. after c
  ;;
  ;; When we're in state N and need to match term T next, we need to
  ;; pass into T enough information to enter state N+1 --- that way,
  ;; we can pick up where we left off if T succeeds or let T backtrack
  ;; if appropriate.
  ;; 
  ;; We model each state as a compiled function and build these states
  ;; recursively.  We keep track of the number of terms we have so
  ;; far.
  ;;
  (check-type terms list)
  (check-type accum integer)

  (let (next-state)
    
    (cond ((null terms)
           ;; We're the last term. accum contains the number of items
           ;; we've successfully parsed so far, which XXX will be the
           ;; number of items on the data stack?
           )

          (t
           ;; We have items left to parse
           (setf next-state (jz--:-rule env (rest terms) (1+ accum)))
           
           )
        
          ))

  )

(defun* jz--*-rule (env term)
  "Magic for repetition."
  
  )

(defun* jz--/-rule (env terms)
  "Magic for prioritized choice."

  
  
  )

(defconst jz-root-grammar

  (let ((root (jz--make-grammar
               :rules (make-hash-table :test 'equal))))

    ;; Create magic
    
    (jz-grammar-define-rule root : (&environment env &rest terms)
      (jz--:-rule env env terms 0))
    
    (jz-grammar-define-rule root * (&environment env term)
      (jz--*-rule env env term))
    
    (jz-grammar-define-rule root / (&environment env &rest terms)
      (jz--/-rule env env terms))
    
    root)
  

  "The grammar inherited by all other grammars.")


(defun* jz-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  
  )

(defun* jz-parser--precompile-rule (parser))

(defun* jz-grammar-create-parser (grammar top-rd)
  "Compiles grammar GRAMMAR into a jz-parser."

  ;; First, create a basic parser.
  
  (let* ((parser (jz--make-parser
                  :grammar grammar
                  :states (make-hash-table :test 'equal))))

    ;; Then, eagerly initialize the rule tree.
    (setf (jz-parser--initial-state parser)
          (jz-parser--compile-rule top-rd))
    
    ;; Parser is now ready to use to begin parsing
    parser))

(defun* jz-state++ (state)
  "Perform one step of a parse.

Update STATE by side effect, calling preconfigured callback
functions as needed.
"
  (funcall (pop (jz-state-control-stack state))
           state))

(jz-make-grammar 
  `((:import jz-base-grammar :as x)

    (hello-target
     (/ (x.keyword "world")
        (x.keyword "blarg")))
  
    (top 
     (-> (<- first-word (x.keyword "hello"))
         (syntactic-ws)
         (<- second-word hello-target)
         
         (concat first-word " " second-word)))))


(provide 'jezebel)
