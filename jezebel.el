(require 'cl)

(defmacro* jez-define-functional-struct (name &rest orig-slots)
  "`defstruct' specialized for pure functional data structures.
A structure is defined just as `defstruct' would, except that an
additional copy-and-modify function is defined.  

This copy-and-modify function permits copying and modifying an
instance of the structure in one step.  If the structure is
defined to be a list, then unmodified parts of the structure may
be shared.  List structures benefit from having their fields
arranged from most to least frequently modified.

This function supports a new :copymod struct option.  If present,
its argument will be used as the name of copy-and-modify macro to
generate.  The name defaults to copy-and-modify-NAME.

"
  (let (name-symbol
        filtered-options
        (copymod-name 'jez--unknown)
        struct-type
        named
        slots)
    
    ;; Normalize name and extract the struct name symbol
    (when (symbolp name)
      (setf name (list name)))
    (setf name-symbol (first name))

    ;; Parse struct options and filter out anything we know
    ;; `defstruct' proper does not understand.
    (dolist (option (rest name))
      (let (filter-out)
        (when (symbolp option)
          (setf option (list option)))
        (case (car-safe option)
          (:named
           (setf named t))
          (:type
           (setf struct-type (second option)))
          (:copymod
           (setf copymod-name (second option))
           (setf filter-out t)))
        (unless filter-out
          (push option filtered-options))))
    (setf name (list* name-symbol filtered-options))

    ;; Compute defaults

    (when (eq copymod-name 'jez--unknown)
      (setf copymod-name
            (intern (format "copy-and-modify-%s" name-symbol))))

    (when (and (null named) (null struct-type))
      (setf named (intern (format "cl-struct-%s" name-symbol))))
    
    (setf struct-type
          (ecase struct-type
            ((vector nil) 'vector)
            (list 'list)))
    
    ;; Parse slots, first adding a dummy slot for the name if
    ;; necessary.
    
    (when named
      (push 'jez--name-slot slots))
    
    (dolist (slot orig-slots)
      (when (not (stringp slot))
        (push (intern
               (format ":%s" (if (symbolp slot) slot (car slot))))
              slots)))
    
    (setf slots (reverse slots))
    
    `(progn
       (defstruct ,name ,@orig-slots)
       ,@(when copymod-name
           (list
            `(defmacro* ,copymod-name
                 (inst &rest modifiers &environment env)
               (,(if (eq struct-type 'list)
                     'jez--copymod-list
                   'jez--copymod-vector)
                inst modifiers
                ',slots ',named
                env))
            `(put ',copymod-name 'lisp-indent-function 1))
           ))))

(defun* jez--copymod-check-modifiers (modifiers slots)
  "Signal error if MODIFIERS not valid for SLOTS.  Used in
implementation of jez--copymod-*."
  (loop for modifier-key = (pop modifiers)
        for modifier-form = (pop modifiers)
        until (null modifier-key)
        unless (and (keywordp modifier-key)
                    (memq modifier-key slots))
        do (error "invalid modifier: %s" modifier-key)))

(defun* jez--copymod-vector (inst modifiers slots named env)
  "Implement copymod macro for vector structures."
  ;; TODO: benchmark and tune. Might we want to just build a vector if
  ;; we have a large enough number of modifiers?
  (jez--copymod-check-modifiers modifiers slots)
  (let ((tmp-sym (gensym "jez--copymod-tmp")))
    (cond (modifiers
           `(let ((,tmp-sym (copy-sequence ,inst)))
              ,@(loop for idx upfrom 0
                      for slot in slots
                      for form = (plist-member modifiers slot)
                      when form collect
                      `(aset ,tmp-sym
                             ,idx
                             ;; anaphoric `orig'
                             (symbol-macrolet
                                 ((orig (aref ,tmp-sym ,idx)))
                               ,(second form))))
              ,tmp-sym))
          (t
           inst))))

(defvar jez--need-orig)
(defmacro jez--need-orig-hack (sym)
  (setf jez--need-orig t)
  sym)

(defun* jez--copymod-list (inst modifiers slots named env)
  "Implement copymod macro for list structures."
  ;; TODO: benchmark and tune performance.
  (jez--copymod-check-modifiers modifiers slots)
  (if (null modifiers)
      inst
    (let* ((tmp-sym (gensym "jez--copymod-tmp"))
           (orig-sym (gensym "jez--copymod-orig"))
           (nr-modifiers (/ (length modifiers) 2))
           jez--need-orig
           need-orig-sym
           (body
            (loop
             for slot = (car slots)
             for form = (plist-member modifiers slot)
             while (> nr-modifiers 0)
             do (pop slots)
             when form do (decf nr-modifiers)
             collect
             (if form
                 ;; we have a form
                 (let* ((jez--need-orig)
                        (inner (cl-macroexpand-all
                                `(symbol-macrolet
                                     ((orig (jez--need-orig-hack
                                             ,orig-sym)))
                                   ,(second form))
                                env)))
                 
                   (if jez--need-orig
                       ;; form used orig
                       (progn
                         (setf need-orig-sym t)
                         `(progn
                            (setf ,orig-sym (pop ,tmp-sym))
                            ,inner))
                     ;; form didn't use orig
                     `(progn
                        (setf ,tmp-sym (rest ,tmp-sym))
                        ,inner)))
             
               ;; don't have a form for this slot; use previous value
               `(pop ,tmp-sym)))))

      `(let ((,tmp-sym ,inst) ,@(when need-orig-sym `(,orig-sym)))
         (,(if slots 'list* 'list)
          ,@body
          ,@(if slots (list tmp-sym)))))))

(jez-define-functional-struct
  (jez-rule
   :named
   (:type list)
   (:constructor jez--make-rule)
   (:conc-name jez-rule--))
  
  "A rule in an jez grammar."

  ;; Symbol naming this rule.
  name

  ;; Function that expands this rule
  expander
  )

(jez-define-functional-struct
 (jez-grammar
  (:constructor jez--make-grammar)
  (:conc-name jez-grammar--))
  "An jez grammar for some language."
  
  rules

  primitives

  )

(jez-define-functional-struct
 (jez-parser
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

(defun jez-parser--make-state-func (parser function &rest args)
  "Return a callable lisp function for the given primitive form."

  (let ((sf `(,function jez--current-state ,@args)))

    (or
     (gethash sf (jez-parser--state-funcs p))
     (puthash sf (byte-compile
                  `(lambda (jez--current-state)
                     ,@sf))))))

(jez-define-functional-struct
 (jez-state
  (:constructor jez--make-state)
  (:copier nil)
  (:conc-name jez-state--))
  
  "A particular state of a parse operation."

  ;; The parse tree we've constructed so far, a jez-tree instance
  ast

  ;; Reach (buffer position)
  reach

  ;; Current position
  point

  ;; Stack (lisp list) of states to enter when backtracking
  or-stack

  ;; Stack (lisp list) of states to enter when successful
  and-stack

  ;; Reference to the parser that created us (which is immutable)
  parser)

(jez-define-functional-struct
 (jez-environment
  (:constructor jez--make-environment)
  (:conc-name jez-environment--))

  "A lexical environment used during rule compilation."

  ;; The parser for this environment
  parser
  )

;;
;; Purely functional AST built incrementally by parsing.
;;

(jez-define-functional-struct
 (jez-tree-node
  (:constructor jez--make-tree-node)
  (:copier nil)
  (:conc-name jez-tree-node--))
  "Node of an N-ary purely-functional zippered tree."

  ;; List of children of this node; updated lazily. jez-tree-node's
  ;; zippered list for this node is authoritative when it exists.
  children

  ;; plist of properties of this node
  properties
  )

(jez-define-functional-struct
 (jez-tree
  (:constructor jez--make-tree)
  (:copier nil)
  (:conc-name jez-tree--))
  "View into a jez-tree."

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
  (jez--make-tree
   :current (jez--make-tree-node)
   :dirty t
   :left nil
   :right (jez-tree-node--children (jez-tree--current tree))
   :parent tree))

(defun* jez-tree-append-child (tree)
  "Add a child to the end of TREE's child list.  Return a new
cursor pointing at the new child.  Takes time proportional to the
number of children in TREE's current node."
  (jez--make-tree
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
        (jez--make-tree
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
         :dirty t

         ;; We can use the original parent's left and right entries
         ;; unchanged.
         :left (jez-tree--left old-parent)
         :right (jez-tree--right old-parent)
         :parent (jez-tree--parent old-parent))

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
    (jez--make-tree
     :current (or (first old-left)
                  (error "already at leftmode child"))
     :dirty (jez-tree--dirty tree)
     :left (rest old-left)
     :right (list* (jez-tree--current tree)
                   (jez-tree--right tree))
     :parent (jez-tree--parent tree))))

(defun* jez-tree-next-sibling (tree)
  (let* ((old-right (jez-tree--right tree)))
    (jez--make-tree
     :current (or (first old-right)
                  (error "already at rightmode child"))
     :dirty (jez-tree--dirty tree)
     :left (list* (jez-tree--current tree)
                  (jez-tree--left tree))
     :right (rest old-right)
     :parent (jez-tree--parent tree))))

(defun* jez-tree-first-child (tree)
  "Return a cursor pointing to the first child of the current
node.  Raise error if the current node has no children.  Constant
time."
  (let ((children (jez-tree-node--children
                   (jez-tree--current tree))))
    (jez--make-tree
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

    (jez--make-tree
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

  (jez--make-tree
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

  (jez--make-tree
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

  (let ((old-current (jez-tree--current tree)))
    (jez--make-tree
     :current (jez--make-tree-node
               :children (jez-tree-node--children old-current)
               :properties (plist-put (copy-sequence
                                       (jez-tree-node--properties old-current))
                                      prop val))
     :dirty t
     :left (jez-tree--left tree)
     :right (jez-tree--right tree)
     :parent (jez-tree--parent tree))))

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

(defun* jez-state--push-and (s &rest items)
  (copy-and-modify-jez-state s
    :and-stack (append items orig)))

(defun* jez-state--push-or (s &rest items)
  (copy-and-modify-jez-state s
    :or-stack (append items orig)))

(defun* jez--do-sequence (s child-state next-state)
  "Parse-func implementing sequence operations."
  (jez-state--push-and s (list child-state next-state)))

(defun* jez--preprocess-sequence (env terms)
  "Return a list of (TERM . BINDING) pairs for the given terms.
Values are returned in reversed order."
  (reverse
   (loop for term in terms
         collect (if (eq (car-safe term) '<-)
                     (error "XXX implement <-")
                   (cons term nil)))))

(defun* jez--compile-sequence (env terms)
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
             'jez--do-/
             (jez-compile-rd env term)
             state-func)))

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


(provide 'jezebel)
