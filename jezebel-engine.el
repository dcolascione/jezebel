(require 'cl)
(require 'jezebel-util)

;; (declare (optimize (speed 3) (safety 0)))


;;;
;;; Parser infrastructure
;;; ---------------------
;;;
;;; Starting with a grammar description list, we create a jez-parser
;;; using JEZ-COMPILE.  The returned parser is a compressed and
;;; optimized representation of the input grammar, and it is logically
;;; immutable.  To parse a buffer using this parser, we create a
;;; jez-state instance using JEZ-BEGIN-PARSE.  We then call
;;; JEZ-ADVANCE on this parser state until it returns non-nil,
;;; indicating that we reached a terminal state.  The resulting AST,
;;; generated by side effect, may be extracted from the jez-state
;;; instance using JEZ-GET-AST.
;;;

(defstruct (jez-parser
            (:constructor jez--make-parser)
            (:copier nil)
            (:conc-name jez-parser--))
  
  "Compiled representation of a grammar that can be used to
create jez-state that, in turn, parse buffers."

  ;; Rules extracted from the grammar description with which this
  ;; parser was created.
  (rules (make-hash-table))

  ;; Primitives extracted from the grammar description with which this
  ;; parser was created.
  (primitives (make-hash-table))

  ;; Holds initial state symbol for this parser.
  (initial-state nil)

  ;; Maps rule invocations to their resulting state symbols. Every
  ;; value in this hash is also a value in states.
  (expansion-cache (make-hash-table :test 'equal))

  ;; Maps IR nodes to IR nodes so that we always return EQ-identical
  ;; IR nodes for EQUAL-identical IR nodes (breaking infinite
  ;; recursion).
  (pstates (make-hash-table :test 'equal)))

(defstruct (jez-state
            (:constructor jez--make-state)
            (:copier nil)
            (:conc-name jez-state--))
  
  "State of an ongoing parse."

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
  (jez-with-slots (reach) (jez-state state)
    (assert (>= reach (point-min)))
    (assert (>= new-reach (point-min)))
    (setf reach (max reach new-reach))))

(defun* jez-backtrack (state)
  "Back up to most recent choice point in STATE."
  (symbol-macrolet ((os (jez-state--or-stack state))
                    (osp (jez-state--or-stack-pos state)))
    (assert (> osp 0))
    (while (not (funcall (aref os (decf osp)) state)))))

(defun* jez-add-undo-1 (state item)
  "Add an undo record to STATE.  

To backtrack, we pop the first item from STATE's or-stack and
call it as a function.  If this function returns nil, we repeat
the process.  The called function may pop additional values from
the or-stack."
  (jez--push-vector (jez-state--or-stack state)
                    (jez-state--or-stack-pos state)
                    item))

(defun* jez-add-undo (state &rest items)
  "Add ITEMS to STATE's undo stack.  The last item will be at the
top of the stack."
  (dolist (item items)
    (jez-add-undo-1 state item)))

(define-compiler-macro jez-add-undo (state &rest items)
  `(symbol-macrolet ((os (jez-state--or-stack state))
                     (osp (jez-state--or-stack-pos state)))
     (when (<= (+ osp ,(length items)) (length os))
       (setf os (jez--double-vector os)))
     ,@(loop for item in items
             collect `(aset os (incf osp) ,item))))
(put 'jez-add-undo 'lisp-indent-function 1)

(defun* jez-state-pop-undo (state)
  (jez--pop-vector (jez-state--or-stack state)
                   (jez-state--or-stack-pos state)))

(defun* jez--undo-handle-choice-point (state)
  (goto-char (jez-state-pop-undo state))
  (setf (jez-state--and-stack state) (jez-state-pop-undo state))
  t)

(defun* jez-add-choice-point (state state-sym)
  "Add a choice point to STATE."
  (check-type state-sym symbol)
  (jez-add-undo state
    (if state-sym
        (cons state-sym (jez-state--and-stack state))
        (jez-state--and-stack state))
    (point)
    #'jez--undo-handle-choice-point))

(defun* jez-do-next (state state-sym)
  "Add NEXT-STATE to STATE and-stack."
  (check-type state-sym symbol)
  (push state-sym (jez-state--and-stack state)))

(defun* jez-state-finish-current (state)
  (pop (jez-state--and-stack state)))

;;;
;;; Intermediate representation.
;;; ----------------------------
;;;
;;; When we compile a grammar using JEZ-COMPILE, we first transform
;;; the input into a graph of jez-irn instances.  Each node represents
;;; a possible state our parser (or more specifically, its jez-state
;;; instance) may take on during parsing.  Each edge is a transition.
;;; Each node is associated with a Lisp function that, when called
;;; with a given jez-state instance, selects on appropriate transition
;;; and updates the jez-state accordingly.
;;;
;;; After building the parse-state graph, we apply transformations to
;;; simplify and optimize it.
;;;
;;; After optimizing the state graph, we walk all states reachable
;;; from the initial state, and for each one, we generate a unique
;;; symbol; to this symbol's function slot we assign a byte compiled
;;; state function responsible for implementing the action represented
;;; by the corresponding IR node.  (See below for details of the
;;; operation of these parse functions.)  We generate this function by
;;; calling JEZ-IRN-COMPILE on the IR node, which in turn calls the
;;; function given by the `compile-func' slot of the node instance.
;;; 
;;; This final transformation allows us to transition from one state
;;; to the next via a simple FUNCALL, giving us maximum efficiency.
;;;
;;; Parsing Details
;;; ---------------
;;;
;;; The state machine embedded in a jez-state instance is essentially
;;; a backtracking pushdown automaton with two stacks: the and-stack
;;; and the or-stack.  The and-stack holds states that we plan to
;;; match in case of success; the or-stack holds a mixture of undo
;;; records and choice points.  When we advance a parse with
;;; JEZ-ADVANCE, we pop a state function off the and-stack and call
;;; it.  (A brand-new jez-state has one entry on its and-stack.)
;;;
;;; On success, the state function updates the parse state: any
;;; modification to the parse state other than pushing an item onto
;;; the and-stack (which should be done using JEZ-DO-NEXT) must be
;;; paired with an undo function pushed onto the or-stack using
;;; JEZ-ADD-UNDO.  When a parse can proceed in more than one way, the
;;; state function uses JEZ-ADD-CHOICE-POINT to make a note of this
;;; situation: if the parse selected using the chosen path fails, we
;;; instead try the path specified in the call to
;;; JEZ-ADD-CHOICE-POINT.  The top of the and-stack in the returned
;;; state is the new state of the parse.
;;; 
;;; On failure, the state function calls JEZ-BACKTRACK on the input
;;; state and returns its result.  JEZ-BACKTRACK essentially returns
;;; to the state of the parse at the last call to
;;; JEZ-ADD-CHOICE-POINT.  Specifically, it pops entries from the
;;; or-stack, calling these entries to undo global state changes,
;;; until it's popped a choice point.  The choice point contains a new
;;; state to push on to the and-stack.
;;;
;;; N.B. All functions may destructively modify input parse states.
;;;
;;; Reach
;;; -----
;;; 
;;; Each jez-state maintains a field called "reach" which holds the
;;; greatest buffer examined during the parse.  Unlike most other
;;; fields, reach is _not_ saved and restored during backtracking.
;;; Preserving it allows higher-level code to reliably cache jez-state
;;; instances so that only part of a buffer needs to be re-parsed
;;; after a modification.
;;;

(defstruct (jez-irn
            (:conc-name jez-irn--)
            (:constructor nil)
            (:copier nil))
  "Abstract base for an IR node in a parse-state graph."
  
  ;; Function that builds a parse function for this IRN.  The return
  ;; value must be a lambda of one argument, which, when called with
  ;; an existing jez-state instance, returns a new jez-state.
  (compile-func nil :read-only t :type function)

  ;; Unique symbol for this state; initially nil; symbol created and
  ;; assign here by JEZ-IRN-COMPILE.  If this slot is non-nil, the
  ;; function slot of its value is the state function.
  (symbol nil :type symbol))

(deftype jez-irn-list ()
  '(jez-list-of-type jez-irn))

(defun* jez--new-pstate (parser candidate)
  (check-type (jez-irn--compile-func candidate) function)
  (jez-with-slots (pstates) (jez-parser parser)
    (or (gethash candidate pstates)
        (puthash candidate candidate pstates))))

(defun* jez-irn-compile (irn parser)
  "Return the state symbol for IRN.  The returned symbol's
function slot contains the symbol function for IRN.  If IRN has
not previously been compiled, do that during this call."
  (jez-with-slots (symbol compile-func) (jez-irn irn)
    (unless symbol
      (setf symbol (gensym "jez-irn"))
      (fset symbol (funcall compile-func irn parser symbol)))
    (assert (fboundp symbol))
    symbol))

(defstruct (jez-sequence
            (:conc-name jez-sequence--)
            (:constructor jez--%make-sequence)
            (:include jez-irn)
            (:copier nil))
  "IR node that matches a sequence of states."
  (pstates nil :read-only t :type jez-irn-list))

(defun* jez-sequence--compile (irn parser self)
  `(lambda (state)
     ,@(loop for irn in (reverse (jez-sequence--pstates irn))
             collect `(jez-do-next state ',(jez-irn-compile irn parser)))))

(defun* jez--make-sequence (parser states)
  "Make a jez-sequence instance."
  (jez--new-pstate parser
                   (jez--%make-sequence
                    :compile-func #'jez-sequence--compile
                    :pstates (jez-the jez-irn-list states))))

(defstruct (jez-cut
            (:conc-name jez-cut--)
            (:constructor jez--%make-cut)
            (:include jez-irn)
            (:copier nil))
  "IR node that tries matching each in a sequence of states."
  (choices nil :read-only t :type jez-irn-list))

(defun* jez-cut--compile (irn parser self)
  (jez-with-slots (choices) (jez-cut irn)
    (cond ((null choices)
           ;; Base case: always backtrack since we didn't match
           ;; anything.  (This state exists to make sure that there's
           ;; always a choice point saved when an ordered choice
           ;; succeeds, allowing users to use backtracking control to
           ;; kill it in all cases instead of making them create a
           ;; special case for the last choice point.)
           `(lambda (state)
              (jez-backtrack state)
              nil))
          (t
           ;; Try the first of our choices, and if that fails,
           ;; backtrack to an ordered choice of the rest of our
           ;; states.
           `(lambda (state)
              (jez-do-next state ',(jez-irn-compile (car choices) parser))
              (jez-add-choice-point state
                                    ',(jez-irn-compile
                                       (jez--make-cut parser (cdr choices))
                                       parser))
              )))))

(defun* jez--make-cut (parser states)
  "Make a jez-cut instance."
  (jez--new-pstate parser
                   (jez--%make-cut
                    :compile-func #'jez-cut--compile
                    :pstates (jez-the jez-irn-list states))))

(defstruct (jez-repeat
            (:conc-name jez-repeat--)
            (:constructor jez--%make-repeat)
            (:include jez-irn)
            (:copier nil))
  "IR node that matches a given state zero or more times."
  (state nil :read-only t :type jez-irn))

(defun jez-repeat--compile (irn parser self)
  `(lambda (state)
     ;; We first pop the and-stack and try to match the thing we're
     ;; trying to repeat.  If successful, we return to this state and
     ;; do it over and over again.
     (jez-do-next state self)
     (jez-do-next state ',(jez-repeat--state irn))

     ;; If we weren't successful, return to whatever was next on the
     ;; and-stack.
     (jez-add-choice-point state nil)))

(defun* jez--make-repeat (parser state)
  "Make an IR node matching STATE zero or more times."
  (jez--new-pstate parser
                   (jez--%make-repeat
                    :compile-func #'jez-repeat--compile
                    :state (jez-the jez-irn state))))

(defstruct (jez-char
            (:conc-name jez-char--)
            (:constructor jez--%make-char)
            (:include jez-irn)
            (:copier nil))
  "IR node that matches a single character in the buffer."
  (char nil :read-only t :type character))

(defun* jez-char--compile (irn parser self)
  `(lambda (state)
     (if (eql (char-after) (jez-char--char))
         (forward-char)
       (jez-backtrack state))))

(defun* jez--make-char (parser char)
  "Make an IR node matching a character."
  (jez--new-pstate parser
                   (jez--%make-char
                    :compile-func #'jez-char--compile
                    :char (jez-the character char))))

(provide 'jezebel-engine)
