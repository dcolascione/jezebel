(require 'jezebel)
(require 'ert)
(require 'jezebel-util)

(defmacro should-eql (a b)
  `(should (eql ,a ,b)))

(ert-deftest jezt-basic-trees ()
  (let ((tr (-> (jez-make-empty-tree)
                (jez-tree-put 'foo 1)
                (jez-tree-put 'bar 2))))
    (should-eql (jez-tree-get tr 'bar) 2)
    (should-eql (jez-tree-get tr 'foo) 1)))

(defmacro jezt-passthrough (val arg-sym &rest forms)
  `(funcall (lambda (,arg-sym) ,@forms ,arg-sym) ,val))
(put 'jezt-passthrough 'lisp-indent-function 1)

(defun jezt-make-basic-tree ()

  ;; N.B. This code may look imperative, but it is in fact purely
  ;; functional!
  
  (-> (jez-make-empty-tree)
      (jez-tree-put 'label 'a)
      
      (jez-tree-append-child)
      (jez-tree-put 'label 'amiddle)
      (jezt-passthrough tr
        (should-error (jez-tree-next-sibling tr)))
      (jez-tree-up)
      
      (jez-tree-prepend-child)
      (jez-tree-put 'label 'afirst)
      (jezt-passthrough tr
        (should-error (jez-tree-prev-sibling tr))
        (should-eql (-> tr
                        (jez-tree-next-sibling)
                        (jez-tree-get 'label))
                    'amiddle))
      (jez-tree-up)
      
      (jez-tree-append-child)
      (jez-tree-put 'label 'alast)
      (jezt-passthrough tr
        (should-error (jez-tree-next-sibling tr))
        (should-eql (-> tr
                        (jez-tree-prev-sibling)
                        (jez-tree-get 'label))
                    'amiddle))
      (jez-tree-up)))

(ert-deftest jezt-tree-construction ()
  (let ((tr (jezt-make-basic-tree)))
    (should-error (jez-tree-next-sibling tr))
    (should-error (jez-tree-prev-sibling tr))
    (should-error (jez-tree-up tr))
    (should (jez-tree-root-p tr))
    (should-eql (jez-tree-get tr 'label) 'a)
    (should-eql (jez-tree-get (jez-tree-first-child tr) 'label) 'afirst)
    (should-eql (jez-tree-get (jez-tree-last-child tr) 'label) 'alast)))

(defmacro* jezt-functional-struct-test (&rest forms)
  "Test a jetz functional struct. Runs FORMS repeatedly,
once for each variety of functional structure.

For each iteration, replace the following symbols with the
ones appropriate for the specific structure being tested:

jezt-fstruct-field1 
jezt-fstruct-field2
make-jezt-fstruct
copy-and-modify-jezt-fstruct
"

  `(progn
     (define-functional-struct (jezt-fstruct-list
                                (:type list)
                                (:named))
       field1
       field2)
     
     (define-functional-struct (jezt-fstruct-vector
                                (:type vector)
                                (:named))
       field1
       field2)

     (define-functional-struct (jezt-fstruct-list-unnamed
                                (:type list))
       field1
       field2)
     
     (define-functional-struct (jezt-fstruct-vector-unnamed
                                (:type vector))
       field1
       field2)     
     
     ,@(loop for s in '(jezt-fstruct-list
                        jezt-fstruct-vector
                        jezt-fstruct-list-unnamed
                        jezt-fstruct-vector-unnamed)
             collect (sublis
                      (loop for sym in '(jezt-fstruct-field1
                                         jezt-fstruct-field2
                                         make-jezt-fstruct
                                         copy-and-modify-jezt-fstruct)
                            for sname = (symbol-name sym)
                            do (when (string-match "jezt-fstruct" sname)
                                 (setf sname
                                       (replace-match (symbol-name s) t t sname)))
                            collect (cons sym (intern sname)))
                      (list* 'progn
                             forms)))))

(ert-deftest jezt-functional-struct-basic ()
  "Test basic operation of functional structs."
  (jezt-functional-struct-test
   (let* ((v1 (make-jezt-fstruct :field1 1 :field2 2))
          (v2 (copy-and-modify-jezt-fstruct v1 :field1 3))
          (v3 (copy-and-modify-jezt-fstruct v1 :field2 4)))

      (should-eql (jezt-fstruct-field1 v1)
                  (jezt-fstruct-field1 v3))
      (should-eql (jezt-fstruct-field2 v2)
                  (jezt-fstruct-field2 v1))
      (should-eql (jezt-fstruct-field1 v2) 3)
      (should-eql (jezt-fstruct-field2 v3) 4))))

(ert-deftest jezt-functional-struct-orig ()
  "Test `orig' anaphor for original field values in copy-and-modify."
  (jezt-functional-struct-test
   (let* ((v1 (make-jezt-fstruct :field1 1 :field2 -1))
          (v2 (copy-and-modify-jezt-fstruct v1 :field1 (1+ orig))))
     (should-eql (jezt-fstruct-field1 v1) 1)
     (should-eql (jezt-fstruct-field1 v2) 2))))

(ert-deftest jezt-functional-struct-shared ()
  "Test list-based functional struct structure sharing."

  ;; Called for structure-defining side effects
  (jezt-functional-struct-test)

  ;; Test only list structures
  (let* ((v1 (make-jezt-fstruct-list :field1 1 :field2 2))
         (v2 (copy-and-modify-jezt-fstruct-list v1 :field1 3)))

      ;; Test that we share structure when possible
      (should (equal (cddr v1) (cddr v2)))
      (should-eql (cddr v1) (cddr v2))))

(ert-deftest jezt-functional-struct-eval-time ()
  "Test that forms in copy-and-modify functions are not evaluated
when the macro is expanded."
  (jezt-functional-struct-test
   (cl-macroexpand-all
    '(copy-and-modify-jezt-fstruct dummy :field1 (error "blah'")))
   (let ((v (make-jezt-fstruct)))
     (should-error 
      (copy-and-modify-jezt-fstruct v
       :field1 (error "bleg"))))))



