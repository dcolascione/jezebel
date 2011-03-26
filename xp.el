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

  ;; A hash table mapping rule definitions to their expansions.  The
  ;; keys are lists in the form (rule-name arg_1 arg_2 ... arg_N), and
  ;; the hash table is a :test 'equal table.
  compiled-rules

  )

(defstruct (xp-parse-state
            (:constructor xp--make-parse-state)
            (:conc-name xp--parse-state))
  
  "A particular state of a parse operation."

  ;; Reference to the parser that created us
  parser

  ;; Explicit stack of parser-functions to execute.
  control-stack

  ;; Data for the parser-functions.
  data-stack)

(defun* xp-make-empty-grammar ()
  "Create a new empty grammar."
  (xp--make-grammar :rules (make-hash-table)))

(defun* xp-grammar-define-rule (grammar rule-name args &rest FORMS)
  "Define or redefine a rule in a grammar.

GRAMMAR gives the grammar in which to define the rule, identified
by symbol RULE-NAME.  If RULE-NAME already exists in the grammar,
its definition is discarded and this definition substituted.

ARGS is a normal CL-function lambda list describing the
arguments for this rule.  FORMS is a sequence of forms evaluated
under an implicit PROGN yielding a rule-definition as described
below when evaluated under ARGS.  The definition as a
whole is assumed to be a pure function of its arguments.

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

  (assert (symbolp rule-name))
  (assert (listp args))

  (puthash rule-name
           `(lambda ,args ,@FORMS)
           (xp-grammar-rules grammar)))

(defun* xp-parser--expand-rule-1 (parser rd &optional environment)
  "Expand a rule RD once and return the expanded rule.

RD is any legal rule definition. Return another rule
definition (which will always be a list) or an xp-compiled-rule
instance. On failure, raise an error."

  ;; XXX: use environment

  (etypecase rd
    (symbol
     (xp-parser--expand-rule-1 parser (list rd) environment))

    (xp-compiled-rule
     rd)

    (list
     (let ((rule-name (car rd)))
       
       )
     )
    
    ))

(defun* xp-parser--expand-rule (parser rd
                                &rest
                                kw-args
                                &key
                                environment leave-alone)
  
  "Expand the rule definition RD in PARSER.

This function expands RD completely, yielding an xp-compiled-rule
instance. Throws on error.

If ENVIRONMENT is supplied, use it for lexical name lookups. It
defaults to the top-level lexical environment for PARSER's
grammar.

If LEAVE-ALONE is present, it is a list of rule names to not
expand. This facility is used by a rule definition that knows how
to handle some kinds of sub-rule specially.

If ENVIRONMENT is present, use it to expand the value of RD.
"
  (setf rd (xp-parser--expand-rule-1 parser rd environment))
  
  (etypecase rd
    (xp-compiled-rule
     ;; We're done
     rd)
             
    ((or symbol list)
     ;; We can still do more expansions here. Recurse 1) to
     ;; put limit on accidental backtracking, and 2) enable
     ;; user to see rule chain in backtrace.
     (apply #'xp-parser--expand-rule parser rd kw-args))))

(defun* xp-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  
  )

(defun* xp-parser--precompile-rule (parser))

(defun* xp-grammar-create-parser (grammar)
  "Compiles grammar GRAMMAR into a xp-parser."

  ;; First, create a basic parser.
  
  (let* ((parser (xp--make-parser
                  :grammar grammar
                  :compiled-rules (make-hash-table :test 'equal))))

    ;; Then, eagerly initialize all top-level rules to catch errors as
    ;; early as possible. We can only eagerly initialize rules with no
    ;; arguments, naturally.

    (maphash (lambda (rule-name rule)
               (unless (xp-rule--args rule)
                 ;; Call for side effect - xp-parser--expand-rule will
                 ;; update cache.
                 (xp-parser--expand-rule rule-name)))
             (xp-grammar--rules grammar))

    ;; Parser is now ready to use to begin parsing
    parser))

(defun* xp-parse-state-step (parse-state)
  "Perform one step of a parse.

Update PARSE-STATE by side effect, calling preconfigured callback
functions as needed.
"
  (funcall (pop (xp-parse-state-control-stack parse-state))
           parse-state))

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
