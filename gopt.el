;; -*- lexical-binding: t -*-
;; Global optimizer for elisp forms

(require 'macroexp)
(require 'bytecomp)
(eval-when-compile (require 'cl-lib))
(eval-when-compile (require 'cl))

(defmacro gopt-awhen (cond &rest body)
  `(let ((it ,cond))
     (when it ,@body)))

(defmacro gopt-postinc (place &optional x)
  "Like `cl-incf', but post-, not pre-increment."
  (gv-letplace (get set) place
    `(prog1 ,get ,(funcall set `(1+ ,get)))))

(eval-and-compile
  (cl-defun gopt-abstract-eval (form &optional default env)
    "If FORM has a value known at compile time, return it.  Otherwise,
return DEFAULT."
    (unless (eq env t)
      (setf form (macroexpand-all form env)))
    (cond ((and (memq (car-safe form) '(quote function))
                (consp (cdr form))
                (not (cddr form)))
           (cadr form))
          ((typep form '(or integer character vector string keyword))
           form)
          ((memq form '(nil t))
           form)
          (t default))))

(eval-and-compile
  (cl-defun gopt-get-slot-info (type slot)
    "For struct TYPE, return (IDX . INFO) for SLOT."
    (loop
       for (slot-name . opts) in (get type 'cl-struct-slots)
       for idx upfrom 0
       when (eq slot-name slot)
       return (list* idx slot-name opts)
       finally return nil)))

(cl-defun gopt-slot-value (type inst slot)
  "Return the value of SLOT in struct INST of TYPE."
  (let* ((struct-type (get type 'cl-struct-type))
         (slot-info (gopt-get-slot-info type slot)))
    (unless slot-info
      (error "struct %s has no slot %s" type slot))
    (unless (cl-typep inst type)
      (signal 'wrong-type-argument (list type inst)))
    (assert (cl-typep inst type))
    (ecase (car struct-type)
      (vector (aref inst (car slot-info)))
      (list (nth (car slot-info) inst)))))

(cl-defun gopt-set-slot-value (type inst slot value)
  "Set the value of SLOT in struct INST of TYPE to VALUE."
  (let* ((struct-type (get type 'cl-struct-type))
         (slot-info (gopt-get-slot-info type slot)))
    (unless slot-info
      (error "struct %s has no slot %s" type slot))
    (unless (cltypep inst type)
      (signal 'wrong-type-argument (list type inst)))
    (ecase (car struct-type)
      (vector (setf (aref inst (car slot-info)) value))
      (list (setf (nth (car slot-info) inst) value)))))

(defsetf gopt-slot-value gopt-set-slot-value)

(define-compiler-macro gopt-slot-value (&whole orig type inst slot)
  (let* ((slot (gopt-abstract-eval slot 0 macroexpand-all-environment))
         (type (gopt-abstract-eval type 0 macroexpand-all-environment)))
    (if (and (symbolp type) (symbolp slot))
        (let ((idx (car (gopt-get-slot-info type slot))))
          (unless idx
            (error "struct %s has no slot %s" type slot))
          (ecase (car (get type 'cl-struct-type))
            (vector `(aref ,inst ,idx))
            (list `(nth ,idx ,inst))))
      orig)))

(define-compiler-macro gopt-set-slot-value (&whole orig type inst slot value)
  (let* ((slot (gopt-abstract-eval slot 0 macroexpand-all-environment))
         (type (gopt-abstract-eval type 0 macroexpand-all-environment)))
    (if (and (symbolp type) (symbolp slot))
        (let ((idx (car (gopt-get-slot-info type slot))))
          (unless idx
            (error "struct %s has no slot %s" type slot))
          (ecase (car (get type 'cl-struct-type))
            (vector `(setf (aref ,inst ,idx) ,value))
            (list `(setf (nth ,idx ,inst) ,value))))
      orig)))

(defmacro* gopt-with-slots (spec-list (type inst) &body body)
  "Like WITH-SLOTS, but for structs."
                                                                                                         (if (macroexp-copyable-p inst)
                                                                                                             `(symbol-macrolet
                                                                                                                  ,(loop for spec in spec-list
                                                                                                                      collect `(,spec (gopt-slot-value ',type ,inst ',spec)))
                                                                                                                ,@body)
                                                                                                           (let ((inst-symbol (cl-gensym "with-struct-slots")))
                                                                                                             `(let ((,inst-symbol ,inst))
                                                                                                                (gopt-with-slots
                                                                                                                 ,spec-list (,type ,inst-symbol) ,@body)))))

(put 'gopt-with-slots 'lisp-indent-function 2)

(defmacro* gopt-slotcase (form &rest specs)
  "Match FORM against SPECS and bind slots.
Each SPECS is a list ((TYPE SLOT1 SLOT2...SLOTN) . BODY), where
TYPE is a struct type and the rest of the elements are slot
names.  If FORM matches a given type, we bind all slots as if
with `gopt-with-slots', then evaluate BODY.  Instead of a list of
type and slots, the first element of a spec may be `t', which
operates as a catch-all."
                                                                                                                      (let ((formsym (cl-gensym "slotcase")))
                                                                                                                        `(let ((,formsym ,form))
                                                                                                                           (cond
                                                                                                                             ,@(loop for (test . body) in specs
                                                                                                                                  collect (if (eq test t) `(t ,@body)
                                                                                                                                            (let ((type (car test))
                                                                                                                                                  (slots (cdr test)))
                                                                                                                                              `((,(intern (format "%s-p" type)) ,formsym)
                                                                                                                                                (gopt-with-slots ,slots (,type ,formsym)
                                                                                                                                                                 ,@body)))))))))
(put 'gopt-slotcase 'lisp-indent-function 1)

(defun gopt-trace (format-string &rest arguments)
  (let ((string (apply #'format format-string arguments)))
    (princ string standard-output)
    (princ "\n" standard-output)
    (car arguments)))

(defun gopt-list-of-type-p (value type)
  (loop for x in value always (typep x type)))


;;; Types

(deftype gopt-list-of-type (type)
  `(and list (satisfies (lambda (v) (gopt-list-of-type-p v ',type)))))
(defun gopt-var-name-p (x)
  (and (symbolp x)
       (not (memq x '(nil t)))
       (not (keywordp x))))
(deftype gopt-var-name () `(satisfies gopt-var-name-p))
(deftype gopt-func-name () `(satisfies gopt-var-name-p))

(defconst gopt-prognlike
  '(save-current-buffer inline progn save-restriction save-excursion track-mouse)
  "Special forms that we can treat as `progn' for optimization purposes")

(defun gopt-prognlike-p (x)
  (memq x gopt-prognlike))

;; Our intermediate representation is essentially N-address code (like
;; 3-address code, but with more operands).  A basic block is a
;; sequence of function calls, each possibly assigning its result to a
;; variable, followed by either a branch or a direct jump.

(defstruct (gopt-binding
             (:constructor gopt-%make-binding))
  (var nil :type (or null gopt-var-name)))
(defstruct (gopt-function)
  (name nil :type gopt-func-name)
  (arglist nil :type list)
  (initial-lexenv nil :type list)
  (bindings nil :type (gopt-list-of-type gopt-binding))
  (free-variables nil :type (gopt-list-of-type gopt-var-name))
  (constant-binding-values (make-hash-table :test 'eq :weakness 'key))
  (first-block nil :type gopt-block)
  (return-block nil :type gopt-block))
(defstruct (gopt-block)
  "Basic block."
  (predecessors nil :type (gopt-list-of-type gopt-block))
  (ops nil :type (gopt-list-of-type gopt-op))
  (next nil :type gopt-next))
(defstruct (gopt-next (:constructor nil)))
(defstruct (gopt-if (:include gopt-next))
  (condvar nil :type gopt-binding)
  (yes nil :type gopt-instruction)
  (no nil :type gopt-instruction))
(defstruct (gopt-goto
             (:include gopt-next)
             (:constructor make-gopt-goto (where)))
  (where nil :type gopt-block))
(defstruct (gopt-goto-backward
             (:include gopt-goto)
             (:constructor make-gopt-goto-backward (where))))
(defstruct (gopt-unreachable (:include gopt-next)))
(defstruct (gopt-op) "One operation in a basic block.")
(defstruct (gopt-op-mutator (:include gopt-op))
  (store nil :type (or null gopt-binding)))
(defstruct (gopt-op-funcall (:include gopt-op-mutator))
  "Function call in basic block."
  (name nil :type gopt-binding)
  (arguments nil :type (gopt-list-of-type gopt-binding)))
(defstruct (gopt-op-constant (:include gopt-op-mutator))
  "Compile-time constant."
  (value nil :type t))
(defstruct (gopt-op-var-copy (:include gopt-op-mutator))
  (from-where nil :type gopt-binding))
(defstruct (gopt-op-return (:include gopt-op))
  "Return from function."
  (value nil :type gopt-binding))
(defstruct (gopt-op-varbind (:include gopt-op))
  (symbol nil :type gopt-var-name)
  (value nil :type gopt-binding))
(defstruct (gopt-op-unbind (:include gopt-op))
  (howmuch nil :type integer))


;; Code

(defun gopt-make-binding (func &optional name)
  "Make a new binding in FUNC."
  (let ((nb (gopt-%make-binding :var (cl-gensym (symbol-name name)))))
    (push nb (gopt-function-bindings func))
    nb))

(defun gopt-find-binding (func lexenv symbol)
  "Check if SYMBOL refers to existing binding.  If so,
return it.  Otherwise, symbol is dynamic; return t."
  (let ((lex-binding (assq symbol lexenv)))
    (if (consp lex-binding) (cdr lex-binding)
      (or lex-binding
          (pushnew symbol
                   (gopt-function-free-variables func)))
      t)))

(defun gopt-binding-set-constant-value (binding func value)
  "Associate a binding with a constant value."
  (puthash binding
           value
           (gopt-function-constant-binding-values func)))

(defun gopt-binding-get-constant-value (binding func &optional default)
  (gethash binding
           (gopt-function-constant-binding-values func)
           default))

(defun gopt-transform-1-funcall (head tail func var lexenv next)
  "Transform a function application into an IR basic block."
  (check-type head gopt-func-name)
  (check-type tail list)
  (check-type func gopt-function)
  (check-type var (or null gopt-binding))
  (check-type lexenv list)
  (check-type next gopt-next)
  (let (bindings primitive-arguments name-binding)
    (setf name-binding (gopt-make-binding func :fname))
    (push (cons name-binding (list 'quote head)) bindings)
    ;; Evaluate arguments
    (dolist (arg tail)
      (let ((ns (gopt-make-binding func :argtmp)))
        (push (cons ns arg) bindings)
        (push ns primitive-arguments)))
    ;; Make the actual funcall block, then wrap it in any binding
    ;; forms we need.  We'll combine all these blocks during the basic
    ;; block simplification phase.
    (let* ((funcall (make-gopt-block
                     :ops (list (make-gopt-op-funcall
                                 :store var
                                 :name name-binding
                                 :arguments (nreverse primitive-arguments)))
                     :next next))
           (cur funcall))
      (dolist (binding bindings)
        (setf cur  (gopt-transform-1
                    (cdr binding)
                    func
                    (car binding)
                    lexenv
                    (make-gopt-goto cur))))
      cur)))

(defun gopt-transform-1-let (op bindings body func var lexenv next)
  "Transform a binding form into IR."
  (check-type op (member let let*))
  (check-type bindings list)
  (check-type func gopt-function)
  (check-type var gopt-binding)
  (check-type lexenv list)
  (check-type next gopt-next)
  (let ((new-lexenv lexenv) procbd cur (unbind-count 0))
    ;; Create bindings and a new lexical environment, but don't yet
    ;; transform the code that assigns values to these bindings.
    (dolist (binding bindings)
      (let* ((name (or (car-safe binding) binding))
             (value (car (cdr-safe binding)))
             (fb (cdr (assq name new-lexenv))))
        (if (or (eq fb t)
                (not lexical-binding)
                (special-variable-p name))
            (progn
              (push (cons name t) new-lexenv)
              (push (cons name value) procbd)
              (incf unbind-count))
          (let ((bo (gopt-make-binding func name)))
            (push (cons name bo) new-lexenv)
            (push (cons bo value) procbd)))))
    ;; If we bound any special variables, remember to unbind them
    ;; after we finish running the body.
    (when (> unbind-count 0)
      (setf next
            (make-gopt-goto
             (make-gopt-block
              :ops (list (make-gopt-op-unbind :howmuch unbind-count))
              :next next))))
    ;; Compile the body in the new environment
    (setf cur (gopt-transform-1 body func var new-lexenv next))
    ;; Wrap body in bindings, now compiling the forms that actually
    ;; produce the bindings.
    (while procbd
      (let* ((item (pop procbd))
             (bo (car item))
             (value-form (cdr item)))
        (pop new-lexenv)
        (setq cur
              (if (symbolp bo)
                  (let ((tmp (gopt-make-binding func :lextmp)))
                    (gopt-transform-1
                     value-form
                     func
                     tmp
                     (if (eq op 'let) lexenv new-lexenv)
                     (make-gopt-goto
                      (make-gopt-block
                       :ops (list (make-gopt-op-varbind
                                   :symbol bo
                                   :value tmp))
                       :next (make-gopt-goto cur)))))
                (gopt-transform-1
                 value-form
                 func
                 bo
                 (if (eq op 'let) lexenv new-lexenv)
                 (make-gopt-goto cur))))))
    ;; The result is either a direct function call or something that
    ;; will set a binding.
    cur))

(defun gopt-transform-1 (form func var lexenv next)
  "Transform FORM into an IR basic block.
The basic block will store the value of the lisp form into VAR,
and control will flow to NEXT.  If VAR is `nil', FORM is being
evaluated for effect, and we store no value.  LEXENV is a list of
containing lexical environments."
  (check-type func gopt-function)
  (check-type var (or null gopt-binding))
  (check-type lexenv list)
  (check-type next gopt-next)
  (while
      (progn
        (setf
         form
         (pcase form
           ;; Refer to variables.
           ((and symbol (guard (typep symbol 'gopt-var-name)))
            (let ((binding (gopt-find-binding func lexenv symbol)))
              (if (eq binding t)
                  `(symbol-value ',symbol)
                (make-gopt-block
                 :ops (list (make-gopt-op-var-copy
                             :store var
                             :from-where binding))
                 :next next))))
           ;; Everything else that's not a sexp is a constant.
           ((pred atom)
            (make-gopt-block
             :ops (list (make-gopt-op-constant :store var :value form))
             :next next))
           ;; Decompose `and' and `or' into `let' bindings and `if'.
           (`(and) t)
           (`(or) nil)
           (`(,(or `and `or) ,val1) val1)
           (`(and ,val . ,rest)
             `(if ,val (and ,@rest)))
           (`(or ,val . ,rest)
             (let ((orsym (cl-gensym "gopt-or-")))
               `(let ((,orsym ,val))
                  (if ,orsym ,orsym (or ,@rest)))))
           ;; Simplify catch
           (`(catch ,_tag . ,_bodyforms)
             (error "XXX support catch"))
           ;; We automatically place `let' bindings during
           ;; optimization.  At this stage, `let' bindings only matter
           ;; for renaming variable references.
           (`(,(and (or `let* `let) op) ,bindings . ,body)
             (gopt-transform-1-let
              op bindings (macroexp-progn body) func var lexenv next))
           ;; Decompose `cond's into `if's.
           (`(cond) nil)
           (`(cond nil) nil)
           (`(cond (,pred) . ,rest) `(or ,pred  (cond ,@rest)))
           (`(cond (,pred . ,prest) . ,rest)
             `(if ,pred  ,(macroexp-progn prest)
                (cond ,@rest)))
           ;; Break up multi-variable `setq's.
           (`(setq) nil)
           (`(setq ,var) `(setq ,var nil))
           (`(setq ,(and (pred symbolp) var) ,value)
             (let ((binding (gopt-find-binding func lexenv var)))
               (if (eq binding t)
                   `(set ',var ,value)
                 (gopt-transform-1 value func
                                   (gopt-find-binding func lexenv var)
                                   lexenv
                                   next))))
           (`(setq ,var ,value . ,rest)
             `(progn
                (setq ,var ,value)
                (setq ,@rest)))
           ;; `if'.
           (`(if ,pred ,yes . ,nos)
             (let ((condvar (gopt-make-binding func :condvar)))
               (gopt-transform-1
                pred func condvar lexenv
                (make-gopt-if
                 :condvar condvar
                 :yes (gopt-transform-1
                       yes func var lexenv next)
                 :no (gopt-transform-1
                      (macroexp-progn nos)
                      func var lexenv
                      (copy-gopt-next next))))))
           ;; Share structure after `quote'
           (`(quote ,value)
             (make-gopt-block
              :ops (list (make-gopt-op-constant :store var :value value))
              :next next))
           ;; Munge `condition-case'.
           (`(condition-case ,_var ,_body . ,_handlers)
             (error "XXX support condition-case"))
           ;; Convert `prog2' to `prog1'
           (`(prog2 ,a ,b . ,rest)
             `(prog1 (progn ,a ,b) ,@rest))
           ;; Implement `prog1' with a `let'-binding
           (`(prog1 ,a . ,rest)
             (let ((prog1sym (cl-gensym "gopt-prog1-")))
               `(let ((,prog1sym ,a))
                  ,@rest
                  ,prog1sym)))
           ;; Transform `progn' and similar.
           (`(,(pred gopt-prognlike-p)) nil)
           (`(progn ,body1) body1)
           (`(progn ,body1 .,rest)
             (gopt-transform-1
              body1 func
              nil ; Evaluate for effect
              lexenv
              (gopt-make-goto
               (gopt-transform-1
                (macroexp-progn rest)
                func var lexenv next))))
           ;; Normalize `while'
           (`(while ,cond . ,body)
             (let* ((condvar (gopt-make-binding func :loopvar))
                    (loop-recur (make-gopt-block))
                    (lb (gopt-transform-1
                         cond func condvar lexenv
                         (make-gopt-if
                          :condvar condvar
                          :yes (gopt-transform-1
                                (macroexp-progn body)
                                func
                                nil      ; Evaluate body for effect
                                lexenv
                                (make-gopt-goto loop-recur))
                          :no (gopt-transform-1 nil func var lexenv next)))))
               (setf (gopt-block-next loop-recur) (make-gopt-goto-backward lb))
               lb))
           ;; `unwind-protect'
           (`(unwind-protect ,_bodyform . ,_unwindforms)
             (error "XXX support unwind-protect"))
           ;; Any remaining application of a special form is an error
           (`(,(pred special-form-p) . ,_)
             (error "unrecognized special form: %S" form))
           ;; Normal function application.
           ((and `(,head . ,tail) (guard (symbolp head)))
            (gopt-transform-1-funcall
             head tail func var lexenv next))
           ;; Anything we don't understand is an error.
           (_ (error "invalid form: %S" form))))
        (not (gopt-block-p form))))
  form)

(defun gopt-transform-to-ir (name arglist body)
  "Transform defun into IR.
NAME is a symbol naming the transformed function.  If `nil', the
function is anonymous.  ARGLIST is a normal elisp argument list.
BODY is a form.  Return a `gopt-function' instance.  The returned
function is not yet optimized."
  (check-type name (or null gopt-func-name))
  (check-type arglist list)
  (let ((func (make-gopt-function :name name :arglist arglist))
        (return-variable nil))
    (gopt-with-slots (initial-lexenv
                      return-block
                      first-block)
                     (gopt-function func)
                     (setf return-variable (gopt-make-binding func :return))
                     (setf return-block (make-gopt-block
                                         :ops (list (make-gopt-op-return
                                                     :value return-variable))
                                         :next (make-gopt-unreachable)))
                     (setf initial-lexenv
                           (loop for arg in arglist
                              if (not (memq arg '(&optional &rest)))
                              collect (cons arg (gopt-make-binding func arg))))
                     (setf first-block
                           (gopt-transform-1 body
                                             func
                                             return-variable
                                             initial-lexenv
                                             (make-gopt-goto return-block)))
                     (gopt-update-predecessors func)
                     (gopt-merge-basic-blocks func)
                     func)))

(defun gopt-map-reachable-blocks (func enumerator)
  "Call ENUMERATOR for each block reachable in FUNC.
ENUMERATOR is called with one argument, the block.  Each block
may be visited more than once."
  (let ((worklist (list (gopt-function-first-block func))))
    (while worklist
      (let ((block (pop worklist)))
        (funcall enumerator block)
        (gopt-slotcase (gopt-block-next block)
                       ((gopt-goto-backward) nil)
                       ((gopt-unreachable) nil)
                       ((gopt-goto where) (push where worklist))
                       ((gopt-if yes no)
                        (push yes worklist)
                        (push no worklist))
                       (t (error "unknown edge type: %S" (gopt-block-next block))))))))
(put 'gopt-map-reachable-blocks 'lisp-indent-function 1)

(defun gopt-map-successors (block func)
  (gopt-slotcase (gopt-block-next block)
                 ((gopt-goto where) (funcall func where))
                 ((gopt-if yes no) (funcall func yes) (funcall func no))
                 ((gopt-unreachable) nil)
                 (t (error "unknown edge: %S" (gopt-block-next block)))))

(defun gopt-map-edges (func enumerator)
  "Call ENUMERATOR for each reachable CFG edge in FUNC.
ENUMERATOR is called with two arguments, the predecessor
and the successor.  This routine does not depend on predecessor
information being up-to-date."
  (gopt-map-reachable-blocks func
                             (lambda (block)
                               (gopt-map-successors block
                                                    (lambda (next)
                                                      (funcall enumerator block next))))))
(put 'gopt-map-edges 'lisp-indent-function 1)

(defun gopt-update-predecessors (func)
  "Update basic block predecessor information in FUNC."
  (gopt-map-reachable-blocks func
                             (lambda (block)
                               (check-type block gopt-block)
                               (setf (gopt-block-predecessors block) nil)))
  (gopt-map-edges func
                  (lambda (from to)
                    (pushnew from (gopt-block-predecessors to)))))

(defun gopt-block-merge-get-safe-successor (block)
  "Check if safe to merge BLOCK into its successor.
If unsafe, return `nil'.  Otherwise, return the successor."
  (let ((next (gopt-block-next block)))
    (and (gopt-goto-p next)
         (not (gopt-goto-backward-p next))
         (let* ((to (gopt-goto-where next))
                (to-predecessors (gopt-block-predecessors to)))
           (and (eq (car to-predecessors) block)
                (not (cdr to-predecessors))
                to)))))

(defun gopt-fix-predecessors (block old new)
  "In BLOCK, replace OLD with NEW in predecessor list."
  (loop for cell on (gopt-block-predecessors block)
     when (eq (car cell) old)
     do (setcar cell new)))

(put 'gopt-map-successors 'lisp-indent-function 1)

(defun gopt-merge-single-block (block)
  "Merge one basic block with its successors if possible."
  (let ((cur block) (op-lists nil))
    ;; Follow the successors of this block until we can't find one
    ;; which can be merged into it.
    (while (let ((cand (gopt-block-merge-get-safe-successor cur)))
             (when cand
               (setf cur cand)
               (push (gopt-block-ops cur) op-lists))))
    ;; Combine the various parts of that block with the current block.
    ;; Because part of the merge-safe condition is that a block has
    ;; only one successor, we only need to update predecessor
    ;; information for the successors of the last block.
    (when op-lists
      (setf (gopt-block-ops block)
            (apply #'append
                   (gopt-block-ops block)
                   (nreverse op-lists)))
      (setf (gopt-block-next block)
            (gopt-block-next cur))
      (gopt-map-successors block
                           (lambda (successor)
                             (gopt-fix-predecessors successor cur block))))))

(defun gopt-merge-basic-blocks (func)
  "Combine mergeable basic blocks in FUNC.
Predecessor information must be up-to-date."
  (gopt-map-reachable-blocks func #'gopt-merge-single-block))

(defun gopt-map-set-bindings (func enumerator)
  (gopt-map-reachable-blocks func
                             (lambda (block)
                               (dolist (op (gopt-block-ops block))
                                 (gopt-slotcase op
                                                ((gopt-op-mutator store) (funcall enumerator store))
                                                ((gopt-op) nil))))))
(put 'gopt-map-set-bindings 'lisp-indent-function 1)
(defun gopt-compute-liveness (func)
  "Compute live-variable information."
  (let ((binding->nr (make-hash-table :test 'eq)))
    (gopt-map-set-bindings func
                           (lambda (binding)
                             (or (gethash binding binding->nr)
                                 (puthash binding (hash-table-count binding->nr)
                                          binding->nr))))
    binding->nr))

(defun gopt-emit (string &rest objects)
  "Like `format', but writes to `standard-output'."
  (princ (apply #'format string objects)))

(defun gopt-arglist-bounds (arglist)
  "Parse a lambda-list.
Return a cons (MIN . MAX).  MIN is an integer giving
the minimum number of arguments ARGLIST accepts.  MAX
is either an integer giving the maximum arguments ARGLIST accepts
or the string \"MANY\" if ARGLIST accepts unlimited arguments."
  (let ((minargs 0) (maxargs 0) saw-&optional saw-&rest)
    (dolist (arg arglist)
      (cond ((eq arg '&rest)
             (setf saw-&rest t))
            ((eq arg '&optional)
             (setf saw-&optional t))
            (saw-&rest
             (setf maxargs "MANY"))
            (saw-&optional
             (incf maxargs))
            (t
             (incf minargs)
             (incf maxargs))))
    (cons minargs maxargs)))


;; Emit C code.

(defun gopt-c-sanitize-name (symbol)
  "Construct a legal C identifier name from a symbol or string."
  (replace-regexp-in-string
   "^$\\|^[0-9]"
   "v\\&"
   (replace-regexp-in-string
    "[^a-zA-Z0-9_]" ""
    (replace-regexp-in-string
     "-" "_"
     (if (stringp symbol) symbol (symbol-name symbol))
     t t)
    t t)
   t t))

(defstruct gopt-c-vardb
  (obj->name (make-hash-table :test 'eq))
  (suffix 0 :type integer)
  (name->obj (make-hash-table :test 'equal)))

(defun gopt-c-intern (vardb obj &optional suggested-name)
  "Create legal C name for an object."
  (let ((obj->name (gopt-c-vardb-obj->name vardb))
        (name->obj (gopt-c-vardb-name->obj vardb)))
    (or (gethash obj obj->name)
        (let ((name (gopt-c-sanitize-name suggested-name)))
          ;; If we collide with an existing mapping, generate a new,
          ;; suffixed name.
          (when (gethash name name->obj)
            (setq name
                  (loop for suffix-nr upfrom (1+ (gopt-c-vardb-suffix vardb))
                     for sname = (format "%s%d" name suffix-nr)
                     while (gethash sname name->obj)
                     finally return (progn
                                      (setf (gopt-c-vardb-suffix vardb) suffix-nr)
                                      sname))))
          (puthash name obj name->obj)
          (puthash obj name obj->name)))))

(defun gopt-c-intern-soft (vardb obj)
  (gethash obj (gopt-c-vardb-obj->name vardb)))

(defun gopt-c-escape (str)
  "Return a C constant for a lisp string.
Omits the opening and closing double-quotes."
  (replace-regexp-in-string
   "[\n\r\"\\]"
   (lambda (s)
     (ecase (aref s 0)
       (?\n "\\n")
       (?\r "\\r")
       (?\" "\\\"")
       (?\\ "\\\\")))
   str t t))

(defvar gopt-c-decl-spot nil)
(defvar gopt-c-vardb nil)

(defun gopt-c-get-binding-name (binding &optional create)
  (check-type binding gopt-binding)
  (let ((name (gopt-c-intern-soft gopt-c-vardb binding)))
    (unless name
      (unless create
        (error "attempt to use binding %S before assignment"
               binding))
      (setf name (gopt-c-intern
                  gopt-c-vardb
                  binding
                  (format "var_%s" (gopt-binding-var binding))))
      (save-excursion
        (goto-char gopt-c-decl-spot)
        (gopt-emit "  Lisp_Object %s;\n" name)))
    name))

(defun gopt-c-get-symbol-name (symbol)
  (let ((name (gopt-c-intern-soft gopt-c-vardb symbol)))
    (unless name
      (setf name (gopt-c-intern
                  gopt-c-vardb
                  symbol (format "sym_%s" symbol)))
      (save-excursion
        (goto-char gopt-c-decl-spot)
        (gopt-emit "  Lisp_Object %s = intern_1 (\"%s\", %d);\n"
                   name
                   (gopt-c-escape (symbol-name symbol))
                   (length (symbol-name symbol)))))
    name))

(defun gopt-c-emit-funcall-expr (name arguments)
  (check-type name gopt-binding)
  (check-type arguments (gopt-list-of-type gopt-binding))
  (let* ((nargs (length arguments)) (post ")"))
    (if (<= nargs 7)
        (gopt-emit "call%d (%s" nargs (gopt-c-get-binding-name name))
      (gopt-emit "apply1 (%s, listn (CONSTYPE_HEAP, %d"
                 (gopt-c-get-binding-name name)
                 nargs)
      (setf post "))"))
    (dolist (arg arguments)
      (gopt-emit ", ")
      (gopt-emit "%s" (gopt-c-get-binding-name arg)))
    (gopt-emit "%s" post)))

(defun gopt-c-emit-constant (value)
  (pcase value
    ((pred integerp)
     (gopt-emit "make_number (%d)" value))
    (`(,head . ,tail)
      (gopt-emit "Fcons (")
      (gopt-c-emit-constant head)
      (gopt-emit ", ")
      (gopt-c-emit-constant tail)
      (gopt-emit ")"))
    ((pred symbolp)
     (gopt-emit
      "%s"
      (gopt-c-get-symbol-name value)))
    (_ (error "don't know how to emit %S in C" value))))

(defun gopt-c-emit-op (op)
  (gopt-emit "  ")
  (gopt-slotcase op
                 ((gopt-op-funcall store name arguments)
                  (when store
                    (gopt-emit "%s = " (gopt-c-get-binding-name store t)))
                  (gopt-c-emit-funcall-expr name arguments))
                 ((gopt-op-var-copy store from-where)
                  (when store
                    (gopt-emit "%s =" (gopt-c-get-binding-name store t)))
                  (gopt-emit "%s" (gopt-c-get-binding-name from-where)))
                 ((gopt-op-constant store value)
                  (gopt-emit "%s = " (gopt-c-get-binding-name store t))
                  (gopt-c-emit-constant value))
                 ((gopt-op-unbind howmuch)
                  (gopt-emit "unbind_to (SPECPDL_INDEX () - %d, Qnil)" howmuch))
                 ((gopt-op-return value)
                  (gopt-emit "return %s" (gopt-c-get-binding-name value)))
                 ((gopt-op-varbind symbol value)
                  (gopt-emit "specbind (%s, %s)"
                             (gopt-c-get-symbol-name symbol)
                             (gopt-c-get-binding-name value)))
                 (t (error "unknown op: %S" op)))
  (gopt-emit ";\n"))

(defun gopt-c-get-block-label (block)
  (gopt-c-intern gopt-c-vardb block "block"))

(defun gopt-c-emit-block (block)
  (gopt-emit "  %s:\n" (gopt-c-get-block-label block))
  (mapc #'gopt-c-emit-op (gopt-block-ops block))
  (gopt-slotcase (gopt-block-next block)
                 ((gopt-goto where) (gopt-emit
                                     "  goto %s;\n"
                                     (gopt-c-get-block-label where)))
                 ((gopt-if condvar yes no)
                  (gopt-emit "  if (NILP (%s))\n    goto %s;\n  else\n    goto %s;\n"
                             (gopt-c-get-binding-name condvar)
                             (gopt-c-get-block-label yes)
                             (gopt-c-get-block-label no)))
                 ((gopt-unreachable))
                 (t (error "invalid block next: %S")
                    (gopt-block-next block)))
  (gopt-emit "\n"))

(defun gopt-ir-to-c-1 (func)
  (gopt-with-slots
   (name arglist first-block initial-lexenv)
   (gopt-function func)
   ;; Write function header.
   (let ((arginfo (gopt-arglist-bounds arglist))
         (idname (replace-regexp-in-string "-" "_" (symbol-name name) t t)))
     (gopt-emit "DEFUN (\"%s\", F%s, S%s, %s, %s, 0, doc: /**/)\n"
                name idname idname (car arginfo) (cdr arginfo)))
   ;; Write arglist and opening brace.
   (let ((gopt-c-vardb (make-gopt-c-vardb))
         (seen-blocks (make-hash-table :test 'eq)))
     (gopt-emit "  (")
     (dolist (item initial-lexenv)
       (let ((name (car item)) (binding (cdr item)))
         (gopt-emit
          "%sLisp_Object %s"
          (if (eq item (car initial-lexenv)) "" ", ")
          (gopt-c-intern gopt-c-vardb binding name))))
     (gopt-emit ")\n")
     (gopt-emit "{\n")
     (gopt-emit "\n")
     (let ((gopt-c-decl-spot (save-excursion (backward-char)
                                             (point-marker))))
       (set-marker-insertion-type gopt-c-decl-spot t)
       (gopt-map-reachable-blocks func
                                  (lambda (block)
                                    (unless (gethash block seen-blocks)
                                      (puthash block t seen-blocks)
                                      (gopt-c-emit-block block)))))
     (gopt-emit "}\n")
     nil)))

(defun gopt-ir-to-c (func out)
  "Write a C translation of FUNC to OUT.
OUT is a stream --- see `standard-output'."
  (if (buffer-live-p out)
      (with-current-buffer out
        (let ((standard-output (current-buffer)))
          (gopt-ir-to-c-1 func)))
    (with-temp-buffer
      (let ((standard-output (current-buffer)))
        (gopt-ir-to-c-1 func))
      (princ (buffer-substring (point-min) (point-max)) out))))


;; Emit Emacs bytecode

(defvar gopt-lap-trace nil)

(defmacro gopt-lap-trace (&rest args)
  `(when gopt-lap-trace
     (gopt-trace ,@args)))

(defvar gopt-lap-block-tags nil
  "Hash table mapping blocks to their lapcode tags.")

(defvar gopt-lap nil
  "List of instructions currently being emitted.")

(defvar gopt-lap-stack-map nil
  "List representing stack contents.  Items are bindings or nil for
temporaries. ")

(defvar gopt-lap-constants nil
  "Alist of constants.")

(defvar gopt-lap-stack-depth nil)
(defvar gopt-lap-max-stack-depth nil)

(defun gopt-lap-intern-block (block)
  "Find or create tag for block."
  (or (gethash block gopt-lap-block-tags)
      (puthash block (cons 'TAG (cons (cl-gensym "block") nil))
               gopt-lap-block-tags)))

(defun gopt-lap-intern-constant (value)
  (or (assq value gopt-lap-constants)
      (car (push (cons value :unknown-const-index)
                 gopt-lap-constants))))

(defun gopt-lap-emit-block-tag (block)
  (push (gopt-lap-intern-block block) gopt-lap))

(defun gopt-lap-emit (op arg)
  "Emit a LAP instruction.
OP is a byte-FOO symbol naming the operand to emit.  ARG is the
operand's argument, the type of which depends on OP."
  (gopt-lap-trace " | %S" op)
  (push (cons op arg) gopt-lap))

(defun gopt-lap-stack-offset (target-binding &optional no-error)
  "Find the offset on the current stack for binding."
  (loop for binding in gopt-lap-stack-map
     for offset upfrom 0
     if (eq binding target-binding)
     return offset
     finally return
       (if no-error nil
         (error "no stack entry for %S" target-binding))))

(defun gopt-lap-note-push (item)
  "Remember that we stored an item on the stack."
  (check-type item (or (member t) gopt-binding))
  (push item gopt-lap-stack-map)
  (gopt-lap-trace " + @%d %S" (1- (length gopt-lap-stack-map)) item)
  (incf gopt-lap-stack-depth)
  (when (> gopt-lap-stack-depth gopt-lap-max-stack-depth)
    (setf gopt-lap-max-stack-depth gopt-lap-stack-depth)))

(defun gopt-lap-note-pop (&optional n)
  "Discard N entries from the stack map.
Does NOT emit stack discard operations --- use this function to reflect
emissions of instructions that discard stack on their own."
  (setf n (or n 1))
  (loop for item in gopt-lap-stack-map
     for i below n
     do (gopt-lap-trace " - @%d %S" (- (length gopt-lap-stack-map) i 1) item))
  (setf gopt-lap-stack-map (nthcdr n gopt-lap-stack-map))
  (decf gopt-lap-stack-depth n))

(defun gopt-lap-emit-var-ref (binding &optional copy-to)
  "Emit code to put the value of BINDING at TOS.
Also update the stack map to indicate that we've done so."
  (let ((offset (gopt-lap-stack-offset binding)))
    (if (zerop offset)
        (gopt-lap-emit 'byte-dup nil)
      (gopt-lap-emit 'byte-stack-ref offset)))
  (gopt-lap-note-push (or copy-to binding)))

(defun gopt-lap-emit-constant (value)
  "Emit code to put a constant at TOS.
Also update the stack map to indicate that we've done so."
  (gopt-lap-emit 'byte-constant (gopt-lap-intern-constant value))
  (gopt-lap-note-push t))

(defun gopt-list-prefix-p (prefix list)
  "Check whether PREFIX is a prefix of LIST."
  (loop while prefix
     for i-prefix = (pop prefix)
     for i-list = (pop list)
     if (not (eq i-prefix i-list))
     return nil
     finally return t))

(defun gopt-lap-emit-funcall (store name arguments)
  (check-type store (or null gopt-binding))
  (check-type name gopt-binding)
  (check-type arguments (gopt-list-of-type gopt-binding))
  ;; XXX: check whether name is a constant
  ;; If the stack map begins with exactly the set of variables that we
  ;; need, we don't have to do anything.  Otherwise, we need to push
  ;; these variables ourselves.
  (unless (gopt-list-prefix-p (reverse (cons name arguments))
                              gopt-lap-stack-map)
    (gopt-lap-emit-var-ref name)
    (dolist (arg arguments)
      (gopt-lap-emit-var-ref arg)))
  (gopt-lap-emit 'byte-call (length arguments))
  (gopt-lap-note-pop (1+ (length arguments)))
  (if store
      (gopt-lap-note-push store)
    (gopt-lap-emit 'byte-discard nil)))

(defun gopt-lap-emit-op (op)
  "Emit an IR operation as zero or more LAP operations."
  (gopt-slotcase op
                 ((gopt-op-funcall store name arguments)
                  (gopt-lap-emit-funcall store name arguments))
                 ((gopt-op-var-copy store from-where)
                  (if store
                      (gopt-lap-emit-var-ref from-where store)
                    (gopt-lap-emit-var-ref from-where)
                    (gopt-lap-emit 'byte-discard nil)
                    (gopt-lap-note-pop)))
                 ((gopt-op-constant store value)
                  (gopt-lap-emit 'byte-constant (gopt-lap-intern-constant value))
                  (gopt-lap-note-push store))
                 ((gopt-op-unbind howmuch)
                  (gopt-lap-emit 'byte-unbind howmuch))
                 ((gopt-op-return value)
                  (gopt-lap-emit-var-ref value)
                  (gopt-lap-emit 'byte-return nil))
                 ((gopt-op-varbind symbol value)
                  (gopt-lap-emit-var-ref value)
                  (gopt-lap-emit 'byte-varbind (gopt-lap-intern-constant symbol))
                  (gopt-lap-note-pop 1))
                 (t (error "unknown op: %S" op))))

(defun gopt-lap-emit-stack-restore (old-depth)
  "Emit code to restore stack to OLD-DEPTH."
  (assert (>= gopt-lap-stack-depth old-depth))
  (assert (= (length gopt-lap-stack-map) gopt-lap-stack-depth) t)
  (gopt-lap-trace " | [clean: %d]" (- gopt-lap-stack-depth old-depth))
  (let ((old-stack (nthcdr
                    (- gopt-lap-stack-depth old-depth)
                    gopt-lap-stack-map)))
    (while (> gopt-lap-stack-depth old-depth)
      (let (entry old-offset already-set)
        (setf entry (car gopt-lap-stack-map))
        (cond ((eq entry t) ; Not actually a binding
               nil)
              ((memq entry already-set)
               ;; Already set a more recently bound value, so discard
               ;; this one.
               (gopt-lap-emit 'byte-discard 1))
              ((setf old-offset
                     (let ((gopt-lap-stack-map old-stack))
                       (gopt-lap-stack-offset entry t)))
               ;; Value is on the target stack map, so set it there,
               ;; in the process removing an entry from the current
               ;; stack.
               (gopt-lap-emit 'byte-stack-set
                              (+ gopt-lap-stack-depth
                                 (- old-depth)
                                 old-offset))
               (push entry already-set))
              (t
               ;; Value isn't needed, so just discard it.
               (gopt-lap-emit 'byte-discard 1)))
        (gopt-lap-note-pop))))
  (assert (= (length gopt-lap-stack-map) gopt-lap-stack-depth) t "post"))

(defun gopt-lap-emit-block (block)
  ;; If this block ends in a conditional, the conditional jump
  ;; instruction at the end will need to pop its test value from the
  ;; stack, so allocate a variable for it here before main code
  ;; emission.
  (gopt-lap-trace "[begin sd:%d] block: %S"
                  (length gopt-lap-stack-map)
                  (gopt-block-ops block))
  (gopt-lap-emit-block-tag block)
  (gopt-slotcase (gopt-block-next block)
                 ((gopt-if condvar)
                  (gopt-lap-emit-var-ref condvar)))
  (let ((old-depth gopt-lap-stack-depth))
    (mapc #'gopt-lap-emit-op (gopt-block-ops block))
    (gopt-lap-emit-stack-restore old-depth))
  (gopt-slotcase (gopt-block-next block)
                 ((gopt-if yes no)
                  (gopt-lap-emit 'byte-goto-if-not-nil (gopt-lap-intern-block yes))
                  (gopt-lap-note-pop 1)
                  (gopt-lap-emit 'byte-goto (gopt-lap-intern-block no)))
                 ((gopt-unreachable))
                 ((gopt-goto where)
                  (gopt-lap-emit 'byte-goto (gopt-lap-intern-block where)))
                 (t (error "unknown edge: %S" (gopt-block-next block))))
  (gopt-lap-trace "[end sd:%d]" (length gopt-lap-stack-map)))

(defun gopt-ir-to-byte-code (func &optional no-opt)
  "Compile IR to a `byte-code' object."
  (let ((gopt-lap-block-tags (make-hash-table :test 'eq))
        (gopt-lap-constants)
        (gopt-lap)
        (gopt-lap-stack-depth 0)
        (gopt-lap-max-stack-depth 0)
        (gopt-lap-stack-map))
    ;; Push all bindings onto the stack.
    (let (already-pushed)
      ;; These are arguments and come pre-pushed.  Just update the
      ;; stack map directly.
      (loop for item in (gopt-function-initial-lexenv func)
         for binding = (cdr item)
         do (progn
              (push binding already-pushed)
              (gopt-lap-note-push binding)))
      ;; Push actual constants for remaining bindings.
      (loop for binding in (gopt-function-bindings func)
         unless (memq binding already-pushed)
         do (progn
              (gopt-lap-emit 'byte-constant
                             (gopt-lap-intern-constant nil))
              (gopt-lap-note-push binding))))
    ;; Emit basic blocks.
    (let ((seen (make-hash-table :test 'eq)))
      (gopt-map-reachable-blocks func
                                 (lambda (block)
                                   (unless (gethash block seen)
                                     (puthash block t seen)
                                     (gopt-lap-emit-block block)))))
    ;; Compiled --- now assemble.  N.B. Create cvec before calling
    ;; `byte-compile-lapcode' --- creating cvec updates our lapcode by
    ;; side effect.
    (setf gopt-lap (nreverse gopt-lap))
    ;; (unless no-opt
    ;;   (setf gopt-lap (byte-optimize-lapcode gopt-lap)))
    (let ((cvec (apply #'vector
                       (loop for const-cell in gopt-lap-constants
                          for i upfrom 0
                          do (setcdr const-cell i)
                          and collect (car const-cell)))))
      (make-byte-code
       (let ((arglist (gopt-function-arglist func)))
         (if lexical-binding (byte-compile-make-args-desc arglist) arglist))
       (byte-compile-lapcode gopt-lap)
       cvec
       gopt-lap-max-stack-depth))))


;; End

(provide 'gopt)
