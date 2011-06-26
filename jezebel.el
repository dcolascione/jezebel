(require 'cl)
(require 'jezebel-util)

;; (declare (optimize (speed 3) (safety 0)))

(defstruct (jez-grammar
            (:constructor jez--make-grammar)
            (:copier nil)
            (:conc-name jez-grammar--))
  "A jez grammar for some language."
  (rules (make-hash-table :test 'equal))
  (primitives (make-hash-table :test 'equal)))

(defstruct (jez-parser
            (:constructor jez--make-parser)
            (:copier nil)
            (:conc-name jez-parser--))
  
  "A compiled parser that can be used to transform a series of 
tokens into an AST."

  ;; The grammar from which this parser was constructed
  grammar

  ;; The initial state of this parser
  initial-state

  ;; Maps action forms (jez--do-* args...) to compiled functions.
  ;;
  (state-funcs (make-hash-table :test 'equal))

  ;; A map of rule expansions.
  ;;
  ;; The keys are lists in the form (rule-name arg_1 arg_2 ... arg_N).
  ;; The values are symbols, the function slots of which contain a
  ;; function representing the given parse state.
  ;;
  (states (make-hash-table :test 'equal)))

(defun* jez-parser--make-state-func (parser function &rest args)
  "Return a callable lisp function for the given primitive form."

  (let ((sf `(,function jez--current-state ,@args)))

    (or
     (gethash sf (jez-parser--state-funcs parser))
     (puthash sf (byte-compile
                  `(lambda (jez--current-state)
                     ,@sf))
              (jez-parser--state-funcs parser)))))

(defstruct (jez-state
            (:constructor jez--make-state)
            (:copier nil)
            (:conc-name jez-state--))
  
  "A particular state of a parse operation.  Pure functional
data structure."

  ;; The parse tree we've constructed so far, a jez-tree instance
  ast

  ;; Reach (buffer position)
  (reach 0)

  ;; Stack states to enter when backtracking
  (or-stack (make-vector 1024 nil))
  (or-stack-pos 0)

  ;; Stack of states to enter when successful
  and-stack

  ;; Reference to the parser that created us (which is immutable)
  parser)

(define-functional-struct (jez-environment
                           (:constructor jez--make-environment)
                           (:conc-name jez-environment--))

  "A lexical environment used during rule compilation.  Pure
functional data structure."

  ;; The parser for this environment
  parser)

(when nil
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

    `(jez-grammar--%define-rule ,grammar ',rule-name ',args ',@body)))

(defun* jez-expand-rd-1 (env rd)
  "Expand a rule RD once in ENV.  Return a cons (EXPANDED . NEW-RD) 
where EXPANDED is true if we we were able to expand the
rule, and NEW-RD is the expanded definition (or the original
definition if we were uanble to expand."

  ;; A bare symbol RULE is equivalent to (RULE).
  (when (symbolp rd)
    (setf rd (list rd)))

  ;; A character is equivalent to a length-1 string.
  (when (characterp rd)
    (setf rd (char-to-string rd)))

  ;; A bare string "foo" is equivalent to (literal "foo").
  (when (stringp rd)
    (setf rd (list 'literal rd)))

  (let* ((parser (jez-environment--parser env))
         (grammar (jez-parser--grammar parser))
         (rules (jez-grammar--rules grammar))
         (rule-name (car-safe rd))
         (ruledef (gethash rule-name rules)))

    (if ruledef
        (cons t (apply ruledef (rest rd)))
      (cons nil rd))))

(defun* jez-expand-rd (env rd)
  "Fully Expand the rule definition RD in ENV.
Return the expanded rule, which is always a list."

  (loop for (expanded . new-rd) = (cons t rd)
        then (jez-expand-rd-1 env new-rd)
        while expanded
        finally return new-rd))

(defun* jez-compile-rd (env rd)
  "Return the matcher for the given rule-definition RD.
Compile the rule if necessary."

  (let* ((expanded-rd (jez-expand-rd env rd))
         (parser (jez-environment--parser env))
         (grammar (jez-parser--grammar parser))
         (states (jez-parser--states parser))
         (rd-sym (gethash expanded-rd states)))

    (unless rd-sym
      (setf rd-sym (gensym
                    (format "jez-state-func-%s" (car-safe expanded-rd))))
      (put rd-sym 'rd rd)
      (put rd-sym 'expanded-rd expanded-rd)
      (setf (symbol-function rd-sym)
            (apply (or (gethash (car-safe expanded-rd)
                                (jez-grammar--primitives grammar))
                       (error "invalid rule %S" expanded-rd))
                   env
                   (rest expanded-rd))))

    rd-sym))

(defun* jez--double-vector (vec &optional init)
  "Return a copy of vector VEC of twice its length.  The additional
elements are set to INIT."
  (loop
   with new-vec = (make-vector (* (length vec) 2) init)
   for i from 0 to (length vec)
   do (setf (aref new-vec i) (aref vec i))
   finally return new-vec))

(defmacro jez--push-vector (vec-place pos-place item)
  "Add ITEM to the extensible vector given by VEC-PLACE and
POS-PLACE, expanding the vector if appropriate.

N.B VEC-PLACE and POS-PLACE may be evaluated more than once.
"
  `(progn
     (when (<= (length ,vec-place) ,pos-place)
       (assert (= (length ,vec-place) ,pos-place))
       (setf ,vec-place (jez--double-vector ,vec-place)))
     (setf (aref ,vec-place
                 (prog1 ,pos-place (incf ,pos-place)))
           ,item)))

(defmacro jez--pop-vector (vec-place pos-place)
  "Return and remove the value at the end of the extensible
vector given by VEC-PLACE and POS-PLACE."
  `(prog1
     (aref ,vec-place (decf ,pos-place))
     (assert (>= ,pos-place 0))))

(defun* jez-state-reach-forward (state new-reach)
  (symbol-macrolet ((reach (jez-state--reach state)))
    (assert (>= reach (point-min)))
    (assert (>= new-reach (point-min)))
    (setf reach (max reach new-reach))))

(defun* jez-state-backtrack (state)
  "Back up to most recent choice point in STATE."
  (symbol-macrolet ((os (jez-state--or-stack state))
                    (osp (jez-state--or-stack-pos state)))
    (assert (> osp 0))
    (while (not (funcall (aref os (decf osp)) state)))))

(defun* jez-state-add-undo-1 (state item)
  "Add an undo record to STATE.  

To backtrack, we pop the first item from STATE's or-stack and
call it as a function.  If this function returns nil, we repeat
the process.  The called function may pop additional values from
the or-stack."
  (jez--push-vector (jez-state--or-stack state)
                    (jez-state--or-stack-pos state)
                    item))

(defun* jez-state-add-undo (state &rest items)
  "Add ITEMS to STATE's undo stack.  The last item will be at the
top of the stack."
  (dolist (item items)
    (jez-state-add-undo-1 state item)))

(define-compiler-macro jez-state-add-undo (state &rest items)
  `(symbol-macrolet ((os (jez-state--or-stack state))
                     (osp (jez-state--or-stack-pos state)))
     (when (<= (+ osp ,(length items)) (length os))
       (setf os (jez--double-vector os)))
     ,@(loop for item in items
             collect `(aset os (incf osp) ,item))))
(put 'jez-state-add-undo 'lisp-indent-function 1)

(defun* jez-state-pop-undo (state)
  (jez--pop-vector (jez-state--or-stack state)
                   (jez-state--or-stack-pos state)))

(defun* jez--undo-handle-choice-point (state)
  (goto-char (jez-state-pop-undo state))
  (setf (jez-state--and-stack state) (jez-state-pop-undo state))
  t)

(defun* jez-state-add-choice-point (state state-func)
  "Add a choice point to STATE."
  
  (jez-state-add-undo state
    (if state-func
        (cons state-func (jez-state--and-stack state))
        (jez-state--and-stack state))
    (point)
    #'jez--undo-handle-choice-point))

(defun* jez-state-do-next (state state-func)
  "Add STATE-FUNC to STATE and-stack."
  (push state-func (jez-state--and-stack state)))

(defun* jez-state-finish-current (state)
  (pop (jez-state--and-stack state)))

(defun* jez--do-sequence (state child-state next-state)
  "Parse-func implementing sequence operations."
  (jez-state-finish-current state)
  (jez-state-do-next state child-state)
  (jez-state-do-next state next-state))

(defun* jez--preprocess-sequence (env terms)
  "Return a list of (TERM . BINDING) pairs for the given terms.
Values are returned in reversed order."
  (reverse
   (loop for term in terms
         collect (if (eq (car-safe term) '<-)
                     (error "XXX implement <-")
                   (cons term nil)))))

(defun* jez-compile-sequence (env terms)
  "Compile a sequence of terms.  Return the state-func used to
begin matching the terms."

  ;; This function generates a function that can be pushed onto one of
  ;; our state stacks as the i=0 state.  The generated function
  ;; references other states functions that we compile for this
  ;; sequence.

  ;;
  ;; Consider (: A_0 A_1 ... A_N ). We have N + 1 states, denoted by
  ;; an integer i ranging over [0, N].  Either:
  ;;
  ;;   - we're about to parse A_i, 0 <= i < N
  ;;   - we've finished parsing, i = N
  ;;
  ;; When we're in state i and need to match A_i next, we need to pass
  ;; into the code for matching A_i enough information for that code
  ;; to then try parsing A_(i+1), possibly many times if backtracking
  ;; is allowed.
  ;;
  ;; We communicate this information by pushing an item onto
  ;; success-stack.
  ;;
  ;; We also allow users to bind values of sub-rules to names using
  ;; the <- operator. These names need to be available during matching
  ;; of sub-rules in order to support predicates --- i.e., each bound
  ;; sub-rule's value needs to be available just after it's matched,
  ;; and not just at the end of the overall rule.
  ;;
  
  
  ;; Loop forward through all terms, accumulating information about
  ;; which ones bind variables. We don't compile the terms right
  ;; away because each one needs to know its successor.
  
  ;; Having build up intermediate information about the meaning of
  ;; each term, compile the terms in reverse order.
  
  (loop 
   for (term . binding) in (jez--preprocess-sequence env terms)
   for state-func = nil
   then (jez-parser--make-state-func
         (jez-environment--parser env)
         'jez--do-sequence
         (jez-compile-rd env term)
         state-func)
   finally return state-func))

(defun* jez--do-repetition (state child-state)
  ;; We don't remove ourselves from the and-stack --- we just match
  ;; the child state over and over until we eventually fail, at which
  ;; point we backtrack and we're done.
  (jez-state-add-choice-point state nil)
  (jez-state-do-next state child-state))

(defun* jez--compile-repetition (env &rest terms)
  (jez-parser--make-state-func
   (jez-environment--parser env)
   'jez--do-repetition
   (jez-compile-sequence env terms)))

(defun* jez--do-choice (state child-state next-alternative-state)
  (jez-state-finish-current state)
  (when next-alternative-state
    (jez-state-add-choice-point state next-alternative-state))
  (jez-state-do-next state child-state))

(defun* jez--compile-choice (env terms)
  "Compile prioritized choice primitive."

  ;; Just as for sequence, compile terms in reverse order so each can
  ;; refer to the next.  The difference is that we put terms on the
  ;; backtracking stack so that we only try to match the (N+1)th term
  ;; if the Nth term fails.

  (let ((parser (jez-environment--parser env))
        state-func)
    
    (dolist (term (reverse terms))
      (setf state-func
            (jez-parser--make-state-func
             parser
             'jez--do-choice
             (jez-compile-rd env term)
             state-func)))

    ;; The state compiled last is logically first.  Return it.
    state-func))

(defun* jez--do-literal (state str)
  (jez-state-finish-current state)
  (let ((qstr (concat "\\'" (regexp-quote str))))
    (jez-state-reach-forward state (length str))
    (unless (re-search-forward qstr nil t)
      (jez-state-backtrack state))))

(defun* jez--compile-literal (env &rest terms)
  (jez-parser--make-state-func
   (jez-environment--parser env)
   #'jez--do-literal
   (mapconcat #'identity terms "")))

(defun* jez--update-hash (dest src)
  "Copy all entries in hash SRC into DEST."
  (maphash (lambda (key value)
             (puthash key value dest))
           src))

(defun* jez-grammar-compile (grammar &optional (top-rd 'top))
  "Compiles GRAMMAR into a jez-parser, which is then returned.
TOP-RD refers to the rule we use to begin parsing; by default, it
is `top'."

  ;; First, create a basic parser.
  
  (let* ((parser (jez--make-parser
                  :grammar grammar))
         (env (jez--make-environment
               :parser parser)))

    ;; Then, eagerly initialize the rule tree.
    (setf (jez-parser--initial-state parser)
          (jez-compile-rd env top-rd))
    
    ;; Parser is now ready for use.
    parser))

(defun* jez--pseudostate-done (state)
  'done)

(defun* jez--psuedostate-fail (state)
  'fail)

(defun* jez-begin-parse (parser)
  "Create a new parse state."
  (let ((state (jez--make-state :parser parser
                                :reach (point-min))))

    ;; If we try to backtrack past a choice point, there is no
    ;; possible way to continue.  Arrange to transition to a state
    ;; that fails forever in this case.
    (jez-state-add-choice-point state 'jez--pseudostate-fail)

    ;; After we're successfully parsed everything, transition to a
    ;; state that succeeds forever.
    (jez-state-do-next state 'jez--pseudostate-done)

    ;; Begin parsing in the initial state.
    (jez-state-do-next state (jez-parser--initial-state parser))

    ;; Parser is now ready for use.
    state))

(defun* jez-advance (state)
  "Update parse state STATE.  Return the symbol `done' if we are
at the end of input, `fail' if we are at an error state, or nil
otherwise."
  (funcall (or (car (jez-state--and-stack state))
               #'jez--pseudostate-done)
           state))

(defun* jez-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  (jez--update-hash (jez-grammar--primitives grammar)
                    (jez-grammar--primitives other-grammar))
  (jez--update-hash (jez-grammar--rules grammar)
                    (jez-grammar--rules other-grammar)))

(defun* jez-grammar-define-primitive (grammar name definition)
  (check-type name symbol)
  (check-type definition function)
  (puthash name definition (jez-grammar--primitives grammar)))

(defun* jez-grammar-define-rule-macro (grammar rule-name args &rest def)
  (check-type rule-name symbol)
  (check-type args list)
  (puthash rule-name
           `(lambda ,args ,@def)
           (jez-grammar--rules grammar)))

(defun* jez-grammar-define-rule (grammar rule-name &rest def)
  (apply #'jez-grammar-define-rule-macro
         grammar rule-name () def))

(defun* jez-grammar-define-include (grammar other-grammar-symbol)
  (jez-grammar-include grammar (symbol-value other-grammar-symbol)))

(defun* jez-make-grammar-from-description (description)
  (let ((grammar (jez--make-grammar)))
    (dolist (cmd description)
      (apply (intern (format "jez-grammar-define-%s" (car cmd)))
             grammar
             (rest cmd)))
    grammar))

(defmacro* jez-make-grammar (&rest description)
  `(jez-make-grammar-from-description ',description))

(defconst jez-root-grammar
  (jez-make-grammar
   ;; Define fundamental rule combinators.
   (primitive : jez-compile-sequence)
   (primitive * jez--compile-repetition)
   (primitive / jez--compile-choice)
     
   ;; Define how to handle literals (note: the compiler
   ;; automagically transforms bare strings and characters into
   ;; calls to the literal primitive).
   (primitive literal jez--compile-literal)))

(provide 'jezebel)
