;; -*- lexical-binding: t -*-

(require 'cl-lib)

;; (declare (optimize (speed 3) (safety 0)))


;;;; Misc.

(cl-defmacro jez-the (&environment env type form)
  "Like `the', except that we assert that FORM is a TYPE."
  (setf form (macroexpand-all form env))
  (list 'the
        type
        (if (cl--simple-expr-p form)
            `(progn
               (check-type ,form ,type)
               ,form)
          (let ((value-sym (cl-gensym "jez-the")))
            `(let ((,value-sym ,form))
               (check-type ,value-sym ,type)
               ,value-sym)))))

(deftype jez-list-of-type (item-type)
  "A type representing a Lisp list of ITEM-TYPE."
  `(satisfies (lambda (list)
                (loop for val in list
                   always (cl-typep val ',item-type)))))

(defun jez-delete-function (fun)
  (interactive "aFunction to delete: ")
  (fmakunbound fun))

(cl-defun jez--update-hash (dest src)
  "Copy all entries in hash SRC into DEST."
  (maphash (lambda (key value)
             (puthash key value dest))
           src))

(eval-and-compile
  (cl-defun jez--abstract-eval (form &optional default env)
    "If FORM has a value known at compile time, return it.  Otherwise,
return DEFAULT."
    (setf form (macroexpand-all form env))
    (cond ((and (memq (car-safe form) '(quote function))
                (consp (cdr form))
                (not (cddr form)))
           (cadr form))
          ((cl-typep form '(or integer character vector string keyword))
           form)
          ((memq form '(nil t))
           form)
          (t default))))


;;; Struct access functions and macros.  N.B. These work properly only
;;; if a struct STRUCT has a type predicate STRUCT-P, which is the
;;; default.

(cl-defun jez--get-slot-info (type slot)
  "For struct TYPE, return (IDX . INFO) for SLOT."
  (loop
     for (slot-name . opts) in (get type 'cl-struct-slots)
     for idx upfrom 0
     when (eq slot-name slot)
     return (list* idx slot-name opts)
     finally return nil))

(cl-defun jez-slot-value (type inst slot)
  "Return the value of SLOT in struct INST of TYPE."
  (let* ((struct-type (get type 'cl-struct-type))
         (slot-info (jez--get-slot-info type slot)))
    (unless slot-info
      (error "struct %s has no slot %s" type slot))
    (unless (cl-typep inst type)
      (signal 'wrong-type-argument (list type inst)))
    (assert (cl-typep inst type))
    (ecase (car struct-type)
      (vector (aref inst (car slot-info)))
      (list (nth (car slot-info) inst)))))

(cl-defun jez-set-slot-value (type inst slot value)
  "Set the value of SLOT in struct INST of TYPE to VALUE."
  (let* ((struct-type (get type 'cl-struct-type))
         (slot-info (jez--get-slot-info type slot)))
    (unless slot-info
      (error "struct %s has no slot %s" type slot))
    (unless (cl-typep inst type)
      (signal 'wrong-type-argument (list type inst)))
    (ecase (car struct-type)
      (vector (setf (aref inst (car slot-info)) value))
      (list (setf (nth (car slot-info) inst) value)))))

(defsetf jez-slot-value jez-set-slot-value)

(define-compiler-macro jez-slot-value (&whole orig type inst slot)
  (let* ((slot (jez--abstract-eval slot 0 macroexpand-all-environment))
         (type (jez--abstract-eval type 0 macroexpand-all-environment)))
    (if (and (symbolp type)
             (symbolp slot))
        (let ((idx (car (jez--get-slot-info type slot))))
          (unless idx
            (error "struct %s has no slot %s" type slot))
          (ecase (car (get type 'cl-struct-type))
            (vector `(aref (jez-the ,type ,inst) ,idx))
            (list `(nth ,idx (jez-the ,type ,inst)))))
      orig)))

(define-compiler-macro jez-set-slot-value (&whole orig type inst slot value)
  (let* ((slot (jez--abstract-eval slot 0 macroexpand-all-environment))
         (type (jez--abstract-eval type 0 macroexpand-all-environment)))
    (if (and (symbolp type)
             (symbolp slot))
        (let ((idx (car (jez--get-slot-info type slot))))
          (unless idx
            (error "struct %s has no slot %s" type slot))
          (ecase (car (get type 'cl-struct-type))
            (vector `(setf (aref (jez-the ,type ,inst) ,idx) ,value))
            (list `(setf (nth ,idx (jez-the ,type ,inst)) ,value))))
      orig)))

(cl-defmacro jez-with-slots (spec-list (type inst) &body body)
  "Like WITH-SLOTS, but for structs."
  (if (symbolp inst)
      `(symbol-macrolet
           ,(loop for spec in spec-list
               collect `(,spec (jez-slot-value ',type ,inst ',spec)))
         ,@body)
    (let ((inst-symbol (cl-gensym "with-struct-slots")))
      `(let ((,inst-symbol ,inst))
         (jez-with-slots
             ,spec-list ,inst-symbol ,@body)))))

(put 'jez-with-slots 'lisp-indent-function 2)

(cl-defun jez-struct-type (value &aux tag)
  "If value is a CL struct, return its struct symbol.  Otherwise,
return nil.  Fails to detect instances of structs with an
:initial-offset and structs that are not named."
  (and (or (consp value)
           (and (vectorp value) (> (length value) 0)))
       (setf tag (elt value 0))
       (symbolp tag)
       (setf tag (symbol-name tag))
       (> (length tag) (length "cl-struct-"))
       (setf tag (intern-soft (substring tag
                                         (length "cl-struct-")
                                         (length tag))))
       (get tag 'cl-struct-type)
       tag))

(deftype jez-struct ()
  `(satisfies (lambda (v) (jez-struct-type v))))

(cl-defun jez-indent-string (indent s)
  "Return a string like S, except that line begins with INDENT
  spaces.  The returned string also ends in a newline."

  (with-temp-buffer
    (let (indent-tabs-mode)
      (insert s)
      (indent-rigidly (point-min) (point-max) indent)
      (goto-char (point-max))
      (unless (eql (char-before) ?\n)
        (insert "\n"))
      (buffer-substring (point-min) (point-max)))))

(cl-defmacro with-jez-indented-output (indent &body body)
  `(princ
    (jez-indent-string ,indent
                       (with-output-to-string
                           ,@body))))
(put 'with-jez-indented-output 'lisp-indent-function 1)

(defvar jez-describe-seen)

(cl-defun jez-describe-1 (val)
  (typecase val
    (jez-struct
     (let ((struct-type (jez-struct-type val)))
       (princ (format "#(struct %S\n" struct-type))
       (with-jez-indented-output 2
         (loop
            for (slot . nil) in (get struct-type 'cl-struct-slots)
            unless (eq slot 'cl-tag-slot)
            do (princ (format "(:%S\n" slot))
            and do (with-jez-indented-output 2
                     (jez-describe-1 (jez-slot-value struct-type val slot)))
            and do (princ ")\n")))
       (princ ")\n")))
    (hash-table
     (princ "#(hash-table\n")
     (with-jez-indented-output 2
       (maphash (lambda (item-key item-val)
                  (with-jez-indented-output 0
                    (jez-describe-1 item-key))
                  (with-jez-indented-output 0
                    (if (eq item-key item-val)
                        (princ "#(eq key)")
                      (jez-describe-1 item-val))))
                val))
     (princ ")\n"))
    (cons
     (if (eq (car val) 'lambda)
         (pp val)
       (princ "(\n")
       (with-jez-indented-output 2
         (loop for cons on val
            when (eq (car cons) 'lambda)
            do (progn
                 (princ " . ")
                 (pp cons)) and return nil
            do (with-jez-indented-output 0
                 (jez-describe-1 (car cons)))))
       (princ ")\n")))
    (t
     (pp val))))

(cl-defun jez-describe (val &optional stream)
  (let ((standard-output stream))
    (jez-describe-1 val)
    nil))

;;;; Purely functional structs.

(cl-defmacro define-functional-struct (name &rest orig-slots)
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
        copymod-name
        copymod-provided
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
           (setf copymod-provided t)
           (setf filter-out t)))
        (unless filter-out
          (push option filtered-options))))
    (setf name (list* name-symbol filtered-options))

    ;; Compute defaults

    (unless copymod-provided
      (setf copymod-name
            (intern (format "copy-and-modify-%s" name-symbol))))

    (when (and (null named) (null struct-type))
      (setf named (intern (format "cl-struct-%s" name-symbol))))

    (setf struct-type (ecase struct-type
                        ((vector nil) 'vector)
                        (list 'list)))

    ;; Parse slots, first adding a dummy slot for the name if
    ;; necessary.

    (when named
      (push 1 slots))

    (dolist (slot orig-slots)
      ;; stringp test skips doc strings
      (when (not (stringp slot))
        (push (if (symbolp slot) slot (car slot))
              slots)))

    (setf slots (reverse slots))

    ;; Turn off generation below if we don't actually have a copymod
    ;; function to generate.
    (unless copymod-name
      (setf struct-type nil))

    ;; Generate the actual macros we'll use to do the copy-and-modify
    ;; operation.

    `(progn
       (defstruct ,name ,@orig-slots)
       ,(functional-struct--inner
         name-symbol
         (ecase struct-type
           (list   'functional-struct--list)
           (vector 'functional-struct--vector)
           (nil    'ignore))
         copymod-name
         slots)
       ',name-symbol)))

(cl-defun functional-struct--inner (name-symbol inner copymod-name slots)
  (let* ((slots-supplied
          (loop for slot in slots
             collect (intern (format "%s-supplied-p" slot))))
         (docstr (concat
                  "Copy and modify an instance of "
                  (symbol-name name-symbol)
                  ".\n\n"
                  "(fn INST &key"
                  (mapconcat (lambda (slot)
                               (if (and slot (symbolp slot))
                                   (concat
                                    " "
                                    (upcase (symbol-name slot)))
                                 ""))
                             slots "")
                  ")")))
    (when copymod-name
      `(progn
         (cl-defmacro ,copymod-name
             (inst &key
                     ,@(loop for slot in slots
                          for supp in slots-supplied
                          when (and slot (symbolp slot))
                          collect (list slot nil supp)))
           ,docstr
           (let ((slot-info (list
                             ,@(loop for slot in slots
                                  for supp in slots-supplied
                                  collect
                                    (append
                                     '(list)
                                     (if (and slot (symbolp slot))
                                         (list (list 'quote slot)
                                               slot supp)
                                       (list nil nil nil)))))))
             ,(funcall inner 'inst 'slot-info)))
         (put ',copymod-name 'lisp-indent-function 1)))))

(defun functional-struct--expand-anaphor (anaphor def form &optional env)
  "Expand FORM with ANAPHOR expanding to DEF.  Return a
cons (EXPANDED . USED) where EXPANDED is the fully macroexpanded
version of FORM and USED is true if NAME was used in the
expansion of FORM.  Macro environment ENV is used for expansion."

  (let ((hack-macro-sym (cl-gensym "expand-anaphor-hack"))
        functional-struct--expand-anaphor-hack)
    (cons
     (macroexpand-all
      `(macrolet ((,hack-macro-sym
                      ()
                    (setf functional-struct--expand-anaphor-hack t)
                    ',def))
         (symbol-macrolet ((,anaphor (,hack-macro-sym)))
           ,form))
      env)
     functional-struct--expand-anaphor-hack)))

(defun functional-struct--vector (inst-sym slot-info-sym)
  `(loop
      with new-sym = (gensym "copymod-new")

      for idx upfrom 0
      for (slot-name slot-value-form slot-supplied-p) in ,slot-info-sym
      when slot-supplied-p
      collect `(aset
                ,new-sym
                ,idx
                ,(first (functional-struct--expand-anaphor
                         'orig `(aref ,new-sym ,idx)
                         slot-value-form
                         macroexpand-all-environment)))
      into body

      finally return
        `(let ((,new-sym (copy-sequence ,,inst-sym)))
           ,@body
           ,new-sym)))

(defun functional-struct--list (_inst-sym slot-info-sym)
  `(loop
      with new-sym = (gensym "copymod-new")
      with tmp-sym = (gensym "copymod-tmp")
      with orig-sym = (gensym "copymod-orig")
      with need-orig-sym

      with nr-to-process = (loop for (nil nil supplied-p) in ,slot-info-sym
                              count supplied-p)

      for (slot-name slot-value-form slot-supplied-p)
      in ,slot-info-sym

      ;; Expand value form so we know whether we need to bind
      ;; the orig form.

      ;; N.B. if slot-supplied-p is nil, slot-value-form will be nil and
      ;; this expansion will be harmless. Also, orig-used will also be
      ;; nill in this case.

      for (exp . orig-used) = (functional-struct--expand-anaphor
                               'orig
                               orig-sym
                               slot-value-form
                               macroexpand-all-environment)

      until (zerop nr-to-process)

      ;; Figure out how to get the body for this slot.

      collect (cond (orig-used
                     (assert slot-supplied-p)
                     (setf need-orig-sym t)
                     (decf nr-to-process)
                     `(progn
                        (setf ,orig-sym (pop ,tmp-sym))
                        ,exp))
                    (slot-supplied-p
                     (decf nr-to-process)
                     `(progn
                        (setf ,tmp-sym (rest ,tmp-sym))
                        ,exp))
                    (t
                     `(pop ,tmp-sym)))
      into body

      ;; And when we're done, package everything into a single form.

      finally return
        `(let ((,tmp-sym ,inst) ,@(when need-orig-sym `(,orig-sym)))
           (list* ,@body ,tmp-sym))))

(defun jez-dbg (fmt &rest args)
  (princ (apply #'format (concat fmt "\n") args)))

(cl-defmacro jez-with-named-temp-file ((filename-symbol
                                        prefix
                                        &optional
                                        dir-flag
                                        suffix)
                                       &rest body)
  "Like `make-temp-file', but clean up on scope exit.
FILENAME-SYMBOL is defined to be the name of the temporary file.
PREFIX, DIR-FLAG, and SUFFIX are as for `make-temp-file'.
"
  `(let ((,filename-symbol
          (make-temp-file ,prefix ,dir-flag ,suffix)))
     (unwind-protect
          ,(macroexp-progn body)
       (ignore-errors
         (delete-file ,filename-symbol)))))
(put 'jez-with-named-temp-file 'lisp-indent-function 1)

(defun jez-string-strip (string)
  "Strip leading and trailing whitespace from STRING."
  (when (string-match "\\`[ \t\n\r\v]*\\(.*?\\)[ \t\n\r\v]*\\'" string)
    (setf string (match-string 1 string)))
  string)

(defun jez-run-command-sentinel (proc reason)
  (unless (process-live-p proc)
    (setf reason (jez-string-strip reason))
    (when (and (not (zerop (process-exit-status proc)))
               (not (equal reason "killed")))
      (message "process %s failed: %s%s" proc reason
               (jez-string-strip
                (if (buffer-live-p (process-buffer proc))
                    (concat
                     ": "
                     (with-current-buffer (process-buffer proc)
                       (buffer-substring (point-min) (point-max))))
                  ""))))
    (delete-process proc)
    (kill-buffer (process-buffer proc))))

(cl-defun jez-run-command (command
                           &key
                             (name "jez-run-command")
                             (input "")
                             (background nil)
                             (debug nil))
  "Run COMMAND."
  (let ((proc nil)
        (pbuffer (generate-new-buffer name)))
    (when debug
      (princ input))
    (unwind-protect
         (progn
           (let ((process-connection-type nil))
             (setf proc (start-file-process-shell-command
                         name pbuffer command)))
           (set-process-query-on-exit-flag proc nil)
           (set-process-sentinel proc #'jez-run-command-sentinel)
           (process-send-string proc input)
           (process-send-eof proc)
           (if background
               (setf proc nil pbuffer nil)
             (while (process-live-p proc)
               (accept-process-output proc))))
      (when proc
        (delete-process proc))
      (when pbuffer
        (kill-buffer pbuffer)))))

(defun jez-combine-ranges (items)
  "Merge overlapping ranges and combine items in each range.
ITEMS is a list, each item of which is ((LB . UB) . CONTENTS).  LB
and UB are the numeric bounds (inclusive) of the item; CONTENTS
is a list of arbitrary items associated with the given range.  ITEMS
may contain overlapping range in arbitrary order.

Return a list of non-overlapping ranges sorted by lower bound;
ranges are split to preserve to make them disjoint.  When more
than one item in an input item covers a numeric range, the output
range corresponding to the overlap contains all the elements of
the CONTENTS items covering the overlap range.  The order of
CONTENTS elements in a merged range is unspecified.

The returned range list may share structure with the input; ITEMS
itself may be altered destructively, but individual items will not be
altered."
  ;; N.B. Be wary of overflow.  Bounds are allowed to range from
  ;; `most-negative-fixnum' to `most-positive-fixnum' inclusive;
  ;; curpos and nextpos below have a lattice structure where we
  ;; consider `t' one greater than `most-positive-fixnum'.
  (if (or (null items) (null (cdr items))) items ; N=0, N=1 are trivial
    (let* ((input (sort items (lambda (a b) (< (caar a) (caar b)))))
           (active nil)
           (curpos (caar (car input)))
           (output nil))
      (while (or input active)
        (let (next-lb)
          ;; Move any items that begin at the current position to the
          ;; active set.  Move the item's cons cell instead of
          ;; allocating a new cons.
          (while (eql curpos (setf next-lb (caar (car input))))
            (let ((input-cdr (cdr input)))
              (setcdr input active)
              (setf active input)
              (setf input input-cdr)))
          (let* ((min-rb (cl-loop for item in active minimize (cdar item)))
                 (nextpos (or (and (integerp next-lb)
                                   (integerp min-rb)
                                   (< min-rb most-positive-fixnum)
                                   (min next-lb (1+ min-rb)))
                              (and (integerp next-lb) next-lb)
                              (and (integerp min-rb)
                                   (< min-rb most-positive-fixnum)
                                   (1+ min-rb))
                              t)))
            (when active
              (let ((item-limit (if (eq nextpos t)
                                    most-positive-fixnum
                                  (1- nextpos))))
                (if (and (null (cdr active))
                         (let ((active-item (car active)))
                           (and (= (caar active-item) curpos)
                                (= (cdar active-item) item-limit))))
                    (progn
                      ;; Special cons-free case for single,
                      ;; non-overlapping item
                      (setcdr active output)
                      (setf output active)
                      (setf active nil))
                  (let ((merged-contents nil)
                        (prev nil)
                        (active-cursor active))
                    (while active-cursor
                      (let ((active-item (car active-cursor)))
                        (if merged-contents
                            (setf merged-contents (append
                                                   (cdr active-item)
                                                   merged-contents))
                          (setf merged-contents (cdr active-item)))
                        (if (= (cdar active-item) item-limit)
                            (if prev
                                (setcdr prev (cdr active-cursor))
                              (setf active (cdr active-cursor)))
                          (setf prev active-cursor))
                        (setf active-cursor (cdr active-cursor))))
                    (cl-assert (<= curpos item-limit))
                    (push (cons (cons curpos item-limit)
                                merged-contents)
                          output)))))
            (setf curpos nextpos))))
      (nreverse output))))

(defun jez-invert-char-table (char-table)
  "Return a char-table inverting CHAR-TABLE.
The inverted char-table is `t' where CHAR-TABLE is nil and nil
where CHAR-TABLE is non-nil."
  (let ((inverted-char-table (make-char-table nil))
        (base 0))
    (map-char-table
     (lambda (r v)
       (when v
         (let* ((r (if (characterp r) (cons r r) r))
                (lb (car r)) (ub (cdr r)))
           (when (< base lb)
             (set-char-table-range
              inverted-char-table (cons base (1- lb)) t))
           (setf base (1+ ub)))))
     char-table)
    (when (< base (max-char))
      (set-char-table-range
       inverted-char-table
       (cons base (max-char)) t))
    inverted-char-table))

(defun jez-char-table-as-list (char-table &optional limit)
  "Return char-table entries from CHAR-TABLE as a list.
Return up to LIMIT entries, or unlimited if LIMIT is nil."
  (let ((entries nil) (nr 0))
    (catch 'char-table-escape
      (map-char-table
       (lambda (r v)
         (let (lb ub)
           (if (characterp r)
               (setf lb r ub r)
             (setf lb (car r) ub (cdr r)))
           (push (cons (cons lb ub) v) entries))
         (when (and limit (>= (incf nr) limit))
           (throw 'char-table-escape t)))
       char-table))
    (nreverse entries)))

(defun jez-safe-char-format (c)
  "Format C printable."
  (if (aref printable-chars c)
      (format "%c" c)
    (format "\\x%x" c)))

(provide 'jezebel-util)
