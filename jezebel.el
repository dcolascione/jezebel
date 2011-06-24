(require 'cl)
(require 'jezebel-util)

(defstruct (jez-rule
            (:constructor jez--make-rule)
            (:copier nil)
            (:conc-name jez-rule--))
  
  "A rule in an jez grammar."

  ;; Symbol naming this rule.
  name

  ;; Function that expands this rule
  expander)

(defstruct (jez-grammar
            (:constructor jez--make-grammar)
            (:copier nil)
            (:conc-name jez-grammar--))
  "A jez grammar for some language."
  rules
  primitives)

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

(defun jez-parser--make-state-func (parser function &rest args)
  "Return a callable lisp function for the given primitive form."

  (let ((sf `(,function jez--current-state ,@args)))

    (or
     (gethash sf (jez-parser--state-funcs p))
     (puthash sf (byte-compile
                  `(lambda (jez--current-state)
                     ,@sf))))))

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

(defstruct (jez-environment
            (:constructor jez--make-environment)
            (:conc-name jez-environment--))

  "A lexical environment used during rule compilation.  Pure
functional data structure."

  ;; The parser for this environment
  parser
  )

;;
;; Purely functional AST built incrementally by parsing.
;;

(define-functional-struct
 (jez-tree-node
  (:constructor jez--make-tree-node)
  (:copier nil)
  (:conc-name jez-tree-node--))
  "Node of an N-ary purely-functional zippered tree.  Pure
functional data structure."

  ;; List of children of this node; updated lazily. jez-tree-node's
  ;; zippered list for this node is authoritative when it exists.
  children

  ;; plist of properties of this node
  properties)

(define-functional-struct
 (jez-tree
  (:constructor jez--make-tree)
  (:copier nil)
  (:conc-name jez-tree--))
  "View into a jez-tree.  Pure functional data structure."

  ;; Current jez-tree-node
  current

  ;; Is the current node dirty?
  dirty

  ;; Children of parent to the left of current; stored in reverse
  ;; order
  left

  ;; Children of parent to the right of current; stored in forward
  ;; order
  right
  
  ;; Parent jez-tree (not jez-tree-node!) or nil if we're at top
  parent
  )

(defun* jez-make-empty-tree ()
  "Create a brand-new empty tree."
  (jez--make-tree
   :current (jez--make-tree-node)))

(defun* jez-tree-prepend-child (tree)
  "Add a child to the beginning of TREE's child list.  Return a
new cursor pointing at the new child.  Constant time."
  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :dirty t
   :left nil
   :right (jez-tree-node--children (jez-tree--current tree))
   :parent tree))

(defun* jez-tree-append-child (tree)
  "Add a child to the end of TREE's child list.  Return a new
cursor pointing at the new child.  Takes time proportional to the
number of children in TREE's current node."
  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :dirty t
   :left (reverse
          (jez-tree-node--children (jez-tree--current tree)))
   :right nil
   :parent tree))

(defun* jez-tree-up (tree)
  "Move cursor to parent of current node.  Return a new cursor
pointing at the parent.  Raise error if already at top of tree.
Constant time if tree has not been modified; otherwise, takes
time proportional to the number of children in the parent."

  ;; If the current node isn't dirty, all we have to do is return the
  ;; cursor we saved when we went down into the current node.

  ;; Otherwise, life becomes trickier. We return a new cursor that
  ;; points at a new tree node. This new node is just like our parent,
  ;; except that its child list is reconstructed from TREE's zippered
  ;; child list, which takes into account any modifications we made.

  (let ((old-parent (jez-tree--parent tree)))
    (unless old-parent
      (error "already at top of tree"))
    (if (jez-tree--dirty tree)
        (copy-and-modify-jez-tree old-parent
         ;; Make new child to stand in for (jez-tree--current
         ;; old-parent).  The new child incorporates any changes we've
         ;; made since we branched from parent.
         :current (jez--make-tree-node
                   :children (append (reverse (jez-tree--left tree))
                                     (list (jez-tree--current tree))
                                     (jez-tree--right tree))
                   :properties (jez-tree-node--properties
                                (jez-tree--current old-parent)))

         ;; The new cursor is dirty because we need to propagate changes
         ;; all the way up to the top of the tree.
         :dirty t)

      ;; Not dirty. Return original parent cursor unchanged.
      old-parent)))

(defun* jez-tree-first-p (tree)
  "Return non-nil if current node of TREE has a previous sibling.
Constant time."
  (jez-tree--left tree))

(defun* jez-tree-last-p (tree)
  "Return non-nil if current node of TREE has a next sibling.
Constant time."
  (jez-tree--right tree))

(defun* jez-tree-children-p (tree)
  "Return non-nil if current node of TREE has children.  Constant
time."
  (jez-tree-node--children
   (jez-tree--current tree)))

(defun* jez-tree-root-p (tree)
  "Return non-nil if current node of TREE is the root.  Constant
time."
  (not (jez-tree--parent tree)))

(defun* jez-tree-prev-sibling (tree)
  "Return a new cursor pointing to the previous sibling of the
current node.  Raise error if there is no previous sibling.
Constant time."
  (let* ((old-left (jez-tree--left tree)))
    (copy-and-modify-jez-tree tree
     :current (or (first old-left)
                  (error "already at leftmost child"))
     :left (rest old-left)
     :right (list* (jez-tree--current tree)
                   (jez-tree--right tree)))))

(defun* jez-tree-next-sibling (tree)
  (let* ((old-right (jez-tree--right tree)))
    (copy-and-modify-jez-tree tree
     :current (or (first old-right)
                  (error "already at rightmost child"))
     :left (list* (jez-tree--current tree)
                  (jez-tree--left tree))
     :right (rest old-right))))

(defun* jez-tree-first-child (tree)
  "Return a cursor pointing to the first child of the current
node.  Raise error if the current node has no children.  Constant
time."
  (let ((children (jez-tree-node--children
                   (jez-tree--current tree))))
    (copy-and-modify-jez-tree tree
     :current (or (first children)
                  (error "current node has no children"))
     :dirty nil
     :left nil
     :right (rest children)
     :parent tree)))

(defun* jez-tree-last-child (tree)
  "Return a cursor pointing to the last child of the current
node.  Raise error if the current node has no children.  Time
proportional to number of children in current node."
  (let ((rchildren (reverse (jez-tree-node--children
                             (jez-tree--current tree)))))

    (copy-and-modify-jez-tree tree
     :current (or (first rchildren)
                  (error "current node has no children"))
     :dirty nil
     :left (rest rchildren)
     :right nil
     :parent tree)))

(defun* jez-tree-insert-sibling-before (tree)
  "Insert a sibling before current node.  Return a cursor
pointing to the new node.  Raise error if current node is the
root node.  Constant time."

  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :dirty t
   :left (jez-tree--left tree)
   :right (list* (jez-tree--current tree)
                 (jez-tree--right tree))
   :parent (or (jez-tree--parent tree)
               (error "root node cannot have siblings"))))

(defun* jez-tree-insert-sibling-after (tree)
  "Insert a sibling after current node.  Return a cursor pointing
to new node.  Raise error if current node is the root node.
Constant time."

  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :dirty t
   :left (list* (jez-tree--current tree)
                (jez-tree--left tree))
   :right (jez-tree--right tree)
   :parent (or (jez-tree--parent tree)
               (error "root node cannot have siblings"))))

(defun* jez-tree-get (tree prop)
  "Return the value of PROP in the current node of TREE.  Time
proportional to number of existing properties."

  (plist-get
   (jez-tree-node--properties (jez-tree--current tree))
   prop))

(defun* jez-tree-put (tree prop val)
  "Set PROP to VAL in the current node of TREE.  Return a new
cursor pointing to the modified node.  Time proportional to
number of existing properties."

  (copy-and-modify-jez-tree tree
    :current (copy-and-modify-jez-tree-node orig
               :properties (plist-put (copy-sequence orig)
                                      prop val))
    :dirty t))

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

(put 'jez-grammar-define-rule 'lisp-indent-function 3)

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

(defun jez--double-vector (vec)
  "Return a copy of vector VEC of twice its length.  The additional
elements are set to nil."
  (loop
   with new-vec = (make-vector (* (length vec) 2))
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
     (setf (aref ,vec-place (incf ,pos-place)) ,item)))

(defmacro jez--pop-vector (vec-place pos-place)
  "Return and remove the value at the end of the extensible
vector given by VEC-PLACE and POS-PLACE."
  `(prog1
     (aref ,vec-place (decf ,pos-place))
     (assert (>= ,pos-place 0))))

(defun* jez-state-backtrack (state)
  "Back up to most recent choice point in STATE."
  (loop until (funcall (aref (jez-state--or-stack state)
                             (decf (jez-state--or-stack-pos state)))
                       state)))

(defun* jez-state-add-undo-1 (state item)
  "Add an undo record to STATE.  

To backtrack, we pop the first item from STATE's or-stack and
call it as a function.  If this function returns nil, we repeat
the process.  The called function may pop additional values from
the or-stack."
  (jez--push-vector (jez-state--or-stack state)
                    (jez-state--or-stack-pos state)))

(defun* jez-state-add-undo (state &rest items)
  "Add ITEMS to STATE's undo stack.  The last item will be at the
top of the stack."
  (dolist (item items)
    (jez-state-add-undo-1 state item)))

(define-compiler-macro jez-state-add-undo (state &rest items)
  (let ((nr (length items)))
    `(symbol-macrolet ((os (jez-state--or-stack state))
                       (osp (jez-state--or-stack-pos state)))
       (when (<= (+ osp ,nr) (length os))
         (setf os (jez--double-vector os)))
       ,@(loop for item in items
               (aset os (incf osp) ,item)))))

(defun* jez-state-pop-undo (state)
  (jez--pop-vector (jez-state--or-stack state)
                   (jez-state--or-stack-pos state)))
(put 'jez-state-add-undo* 'lisp-indent-function 1)

(defun* jez--undo-handle-choice-point (state)
  (goto-char (jez-state-pop-undo state))
  (setf (jez-state--and-stack state) (jez-state-pop-undo state))
  t)

(defun* jez-state-add-choice-point (state state-func)
  "Add a choice point to STATE."
  
  (jez-state-add-undo* state
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
  (jez-state-add state child-state))

(defun* jez--compile-repetition (env &rest terms)
  (jez-parser--make-state-func
   (jez-environment--parser env)
   'jez--do-repetition
   (jez-compile-sequence env terms)))

(defun* jez--do-choice (state child-state next-alternative-state)
  (jez-state-finish-current state)
  (jez-state-add-choice-point state next-alternative-state)
  (jez-state-do-next state child-state))

(defun* jez--compile-choice (env terms)
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
             'jez--do-choice
             (jez-compile-sequence env term)
             state-func)))

    ;; The state compiled last is logically first.  Return it.
    state-func))

(defun* jez--do-literal (state str)
  (jez-state-finish-current state)
  (let ((qstr (concat "\\'" (regexp-quote str))))
    (jez-state-reach-forward (length str))
    (unless (re-search-forward qstr nil t)
      (jez-state-backtrack state))))

(defun* jez--compile-literal (env terms)
  (jez-parser--make-state-func
   (jez-environment--parser env)
   #'jez--do-literal
   (mapconcat #'identity terms "")))

(defconst jez-root-grammar
  (let ((root (jez--make-grammar
               :rules (make-hash-table :test #'eq)
               :primitives (make-hash-table :test #'eq))))

    ;; Initial semi-magical rules.
    
    (jez-grammar-define-primitive root ': #'jez-compile-sequence)
    (jez-grammar-define-primitive root '* #'jez--compile-repetition)
    (jez-grammar-define-primitive root '/ #'jez--compile-choice)

    ;; The grammar compiler has a special case that transforms literal
    ;; strings and characters into forms like (literal "foo").
    (jez-grammar-define-primitive root 'literal #'jez--compile-literal)
    root)
  "The grammar inherited by all other grammars.")

(defun* jez--update-hash (dest src)
  "Copy all entries in hash SRC into DEST."
  (maphash (lambda (key value)
             (puthash key value dest))
           src))

(defun* jez-grammar-include (grammar other-grammar)
  "Copy rules from OTHER-GRAMMAR into GRAMMAR."
  (jez--update-hash (jez-grammar--primitives grammar)
                    (jez-grammar--primitives other-grammar))
  (jez--update-hash (jez-grammar--rules grammar)
                    (jez-grammar--rules other-grammar)))

(defun* jez-create-parser (grammar top-rd)
  "Compiles grammar GRAMMAR into a jez-parser."

  ;; First, create a basic parser.
  
  (let* ((parser (jez--make-parser
                  :grammar grammar)))

    ;; Then, eagerly initialize the rule tree.
    (setf (jez-parser--initial-state parser)
          (jez-parser--expand-rule top-rd))
    
    ;; Parser is now ready for use.
    parser))

(defun* jez-step-state (state)
  "Update parse state STATE by one step and return the new parse
state.  This operation preserves the old value of STATE."
  (funcall (pop (jez-state--and-stack state)) state))


(provide 'jezebel)
