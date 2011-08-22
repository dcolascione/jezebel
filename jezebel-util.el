;;;; Stuff from https://github.com/sroccaserra/emacs/blob/master/tools.el


(defmacro -> (x &optional form &rest more)
  (cond ((not (null more))
         `(-> (-> ,x ,form) ,@more))
        ((not (null form))
         (if (sequencep form)
             `(,(first form) ,x ,@(rest form))
           (list form x)))
        (t x)))

(defmacro ->> (x form &rest more)
  (cond ((not (null more)) `(->> (->> ,x ,form) ,@more))
        (t (if (sequencep form)
               `(,(first form) ,@(rest form) ,x)
             (list form x)))))

(defmacro -?> (x form &rest more)
  (cond ((not (null more)) `(-?> (-?> ,x ,form) ,@more))
        (t (if (sequencep form)
               `(if (null ,x) nil
                  (,(first form) ,x ,@(rest form)))
             `(if (null ,x) nil
                ,(list form x))))))

(defmacro -?>> (x form &rest more)
  (cond ((not (null more)) `(-?>> (-?>> ,x ,form) ,@more))
        (t (if (sequencep form)
               `(if (null ,x) nil
                  (,(first form) ,@(rest form) ,x))
             `(if (null ,x) nil
                ,(list form x))))))

(defun delete-function (fun)
  (interactive "aFunction to delete: ")
  (fmakunbound fun))

(defmacro* define-functional-struct (name &rest orig-slots)
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

(defun* functional-struct--inner (name-symbol inner copymod-name slots)
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
         (defmacro* ,copymod-name
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

  (let ((hack-macro-sym (gensym "expand-anaphor-hack"))
        functional-struct--expand-anaphor-hack)
    (cons
     (cl-macroexpand-all
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
                       cl-macro-environment)))
    into body
    
    finally return
    `(let ((,new-sym (copy-sequence ,,inst-sym)))
       ,@body
       ,new-sym)))

(defun functional-struct--list (inst-sym slot-info-sym)
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
                             cl-macro-environment)

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

(defun* jez--update-hash (dest src)
  "Copy all entries in hash SRC into DEST."
  (maphash (lambda (key value)
             (puthash key value dest))
           src))

(provide 'jezebel-util)
