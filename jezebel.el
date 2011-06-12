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

  ;; Maps action forms (jez--do-* args...) to compiled functions.
  ;;
  ;; The value is an EQUAL hash
  ;;
  state-funcs

  ;; A map of rule expansions.
  ;;
  ;; The keys are lists in the form (rule-name arg_1 arg_2 ... arg_N),
  ;; and the hash table is a :test 'equal table.
  ;;
  ;; The values are symbols, the function slots of which contain a
  ;; function representing the given parse state.
  ;;
  states)

(defun jez-parser--make-state-func (p &rest sf)
  "Return a callable lisp function for the given primitive form."

  (or
   (gethash sf (jez-parser--state-funcs p))
   (puthash sf (byte-compile
                `(lambda (s)
                   ,@sf)))))

(defstruct (jez-state
            (:constructor jez--make-state)
            (:conc-name jez-state--))
  
  "A particular state of a parse operation."

  ;; Reference to the parser that created us (which is immutable)
  parser

  ;; Stack (lisp list) of states to enter when backtracking
  or-stack

  ;; Stack (lisp list) of states to enter when successful
  and-stack

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

;;
;; Purely functional AST built incrementally by parsing.
;;

(defstruct (jez-tree-node
            (:constructor jez--make-tree-node)
            (:copier nil)
            (:conc-name jez-tree-node--))
  "Node of an N-ary purely-functional zippered tree."

  ;; Each node has a notion of "current child". The current child is
  ;; the first entry in left-children.
  
  ;; Children of this node up to and including the current
  ;; child. Stored in reverse order.
  left-children

  ;; Children of this node after the current child. Stored in forward
  ;; order.
  right-children)

(defstruct (jez-tree
            (:constructor jez--make-tree)
            (:copier nil)
            (:conc-name jez-tree--))
  "View into a jez-tree."

  current-node
  ancestors)

(defun* jez-tree--replace-ancestors (replacement remainder-path)
  "Copy nodes along the given path, replacing the current node
with a copy so that the old tree structure persists."

  ;; Build a new node, substituting REPLACEMENT for the current child
  ;; of CUR-NODE, then process the next item in REMAINDER-PATH
  ;; replacing _its_ current child with the node we just created.

  (when remainder-path
    (let* ((cur (first remainder-path))
           (new (jez--make-tree-node
                 :left-children
                 (list* replacement
                        (rest (jez-tree-node--left-children cur)))
                 :right-children
                 (jez-tree-node--right-children cur))))

      (list* new
             (jez-tree--replace-ancestors new (rest remainder-path))))))

(defun* jez-make-empty-tree ()
  "Create a brand-new empty tree."
  (jez--make-tree
   :current-node (jez--make-tree-node)))

(defun* jez-tree-add-child (tree)
  "Add a child node to TREE's current node.  Return a new tree
with the current node being the just-added node.  Requires time
proportional to the current height of the tree."

  (let* ((cur (jez-tree--current-node tree))
         (new (jez--make-tree-node))
         (new-parent (jez--make-tree-node
                      :left-children
                      (list* new
                             (jez-tree-node--left-children cur))
                      :right-children
                      (jez-tree-node--right-children cur))))

    ;; Build a new cursor that refers to a persistently new tree that
    ;; shares structure with the old.

    (jez--make-tree
     :current-node new
     :ancestors (list* 
                 new-parent
                 (jez-tree--replace-ancestors
                  new-parent
                  (jez-tree--ancestors tree))))))

(defun* jez-tree-child-left (tree)
  "Set current node's current child to previous child.  Return a
new cursor.  Raise error if there is no previous child.  Time
required is proportional to the depth of the tree."
  (let* ((cur (jez-tree--current-node tree))
         (l (or (jez-tree-node--left-children cur)
                (error "already at leftmost child")))
         (r (jez-tree-node--right-children cur))
         (new (jez--make-tree-node
               :left-children
               (rest l)
               :right-children
               (list* (first l) r))))

    (jez--make-tree
     :current-node new
     :ancestors (jez-tree--replace-ancestors
                   new
                   (jez-tree--ancestors tree)))))

(defun* jez-tree-child-right (tree)
  "Set current node's current child to next child.  Return a new
cursor.  Raise error if there is no next child.  Time required is
proportional to the depth of the tree."
  (let* ((cur (jez-tree--current-node tree))
         (l (jez-tree-node--left-children cur))
         (r (or (jez-tree-node--right-children cur)
                (error "already at rightmost child")))
         (new (jez--make-tree-node
               :left-children
               (list* (first r) l)
               :right-children
               (rest r))))

    (jez--make-tree
     :current-node new
     :ancestors (jez-tree--replace-ancestors
                 new
                 (jez-tree--ancestors tree)))))

(defun* jez-tree-up (tree)
  "Move cursor to parent of current node.  Return a new cursor.
Raise error if the current node is the top node.  Constant time."
  
  )

(defun* jez-tree-down (tree)
  "Move cursor to current child.  Return a new cursor.  Raise
error if the current node has no children.  Constant time."

  
  
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

(defun* jez--do-: (s child-state next-state)
  ;; XXX: implement me properly. The lines below are junk.
  (push child-state (jez-state--and-stack s))
  (push next-state (jez-state--and-stack s)))

(defun* jez--compile-: (env terms)
  "Compile sequence primitive."

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
  
  (let ((parser (jez-environment--parser env))
        binding rbindings rterms state-func)
    
    ;; Loop forward through all terms, accumulating information about
    ;; which ones bind variables. We don't compile the terms right
    ;; away because each one needs to know its successor.
    (dolist (term terms)
      (setf binding nil)
      
      (when (eq (car-safe term) '<-)
        (pop term)
        (setf binding (pop term)))

      (push term rterms)
      (push binding rbindings))

    ;; Compile the terms in reverse order so that each one references
    ;; the next.

    (while rterms
      (setf binding (pop rbindings))
      (setf state-func
            (jez-parser--make-state-func
             parser
             `(jez-do-: s                        ; anaphoric `s'
                        ,(jez-compile-rd env (pop rterms))
                        ,state-func))))
    
    ;; The term we compiled last is the one that is logically
    ;; first. Return it to our caller as the "compiled" rule.
    state-func))

(defun* jez--do-* (s child-state)
  ;; XXX: non-backtracking alternative.
  
  )

(defun* jez--do-*-first (s child-state)
  ;; push item onto data stack.

  
    
  )

(defun* jez--do-*-last (s)
  ;; clean up list on data stack and build AST node for it.
  )

(defun* jez--compile-* (env backtrack term)
  "Compile repetition primitive."
  
  ;; Match TERM as many times as we can, backtracking after each one.

  (let* ((parser (jez-environment--parser env))
         (last (jez-parser--make-state-func
                parser `(jez--do-*-last s)))
         (nth (jez-parser--make-state-func
                parser `(jez--do-*-nth s ,last)))
         (first (jez-parser--make-state-func
                 (jez-parser--make-state-func
                parser `(jez--do-*-first s ,nth ,last))))

         

         )))

(defun* jez--do-/ (s child-state next-alternative-state)
  ;; XXX: non-backtracking alternative. Even possible?
  
  (when next-alternative-state
    (push next-alternative-state (jez--state--or-stack s)))
  (push child-state (jez--state--and-stack s)))

(defun* jez--compile-/ (env terms)
  "Compile prioritized choice primitive."

  ;; Just as for sequence, compile terms in reverse order so each can
  ;; refer to the next.  The difference is that we put terms on the
  ;; backtracking stack so that we only try to match the N+1th term if
  ;; the Nth term fails.

  (let ((parser (jez-environment--parser env))
        state-func)
    
    (dolist (term (reverse terms))
      (setf state-func
            (jez-parser--make-state-func
             parser
             `(jez--do-/
               s                        ; anaphoric `s'
               ,(jez-compile-rd env term)
               state-func))))

    ;; The state compiled last is logically first. Return it.
    state-func))

(defconst jez-root-grammar
  (let ((root (jez--make-grammar
               :rules (make-hash-table :test #'eq)
               :primitives (make-hash-table :test #'eq))))

    ;; Initial semi-magical rules.
    
    (jez-grammar-define-primitive root ': #'jez--compile-:)
    (jez-grammar-define-primitive root '* #'jez--compile-*)
    (jez-grammar-define-primitive root '/ #'jez--compile-/)
    root)
  "The grammar inherited by all other grammars.")


(defun* jez-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  (assert nil nil "IMPLEMENT ME XXX")
  )

(defun* jez-create-parser (grammar top-rd)
  "Compiles grammar GRAMMAR into a jez-parser."

  ;; First, create a basic parser.
  
  (let* ((parser (jez--make-parser
                  :grammar grammar
                  :state-funcs (make-hash-table :test 'equal)
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
