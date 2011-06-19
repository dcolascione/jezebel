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

(defmacro* jezt-functional-struct-test (form)
  "Test a jetz functional struct. Runs form repeatedly,
once for each variety of functional structure.

For each iteration, replace the following symbols with the
ones appropriate for the specific structure being tested:

jezt-fstruct-field1 
jezt-fstruct-field2
make-jezt-fstruct
copy-and-modify-jezt-fstruct
"

  
  
  (define-functional-struct (jezt-fstruct-list
                             (:type list)
                             (:named))
    field1
    field2)
  (define-functional-struct (jezt-fstruct-vector
                             (:type vector)
                             (:named))
    field1
    field2))

(ert-deftest jezt-functional-struct-basic-list ()
  "Test basic creation and modification of functional structs."
  (jezt-functional-struct-preamble)
  (let* ((v1 (make-jezt-fstruct-list :field1 1 :field2 2))
           (v2 (copy-and-modify-jezt-fstruct-list v1 :field1 3))
           (v3 (copy-and-modify-jezt-fstruct-list v1 :field2 4)))

      ;; Test that basic stuff works
      (should-eql (jezt-fstruct-list-field1 v1)
                  (jezt-fstruct-list-field1 v3))
      (should-eql (jezt-fstruct-list-field2 v2)
                  (jezt-fstruct-list-field2 v1))
      (should-eql (jezt-fstruct-list-field1 v2) 3)
      (should-eql (jezt-fstruct-list-field2 v3) 4)))

(ert-deftest jezt-functional-struct-basic-vector ()
  "Test basic creation and modification of functional structs."
  (jezt-functional-struct-preamble)
  (let* ((v1 (make-jezt-fstruct-vector :field1 1 :field2 2))
           (v2 (copy-and-modify-jezt-fstruct-vector v1 :field1 3))
           (v3 (copy-and-modify-jezt-fstruct-vector v1 :field2 4)))

      ;; Test that basic stuff works
      (should-eql (jezt-fstruct-vector-field1 v1)
                  (jezt-fstruct-vector-field1 v3))
      (should-eql (jezt-fstruct-vector-field2 v2)
                  (jezt-fstruct-vector-field2 v1))
      (should-eql (jezt-fstruct-vector-field1 v2) 3)
      (should-eql (jezt-fstruct-vector-field2 v3) 4)))

(ert-deftest jezt-functional-struct-shared ()
  "Test list-based functional struct structure sharing."
  (jezt-functional-struct-preamble)
  (let* ((v1 (make-jezt-fstruct-list :field1 1 :field2 2))
         (v2 (copy-and-modify-jezt-fstruct-list v1 :field1 3)))

      ;; Test that we share structure when possible
      (should (equal (cddr v1) (cddr v2)))
      (should-eql (cddr v1) (cddr v2))))

(ert-deftest jezt-functional-struct-eval-time ()
  "Test that forms in copy-and-modify functions are not evaluated
when the macro is expanded."
  (jezt-functional-struct-preamble)
  (cl-macroexpand-all
   '(copy-and-modify-jezt-fstruct-list dummy :field1 (error "blah'"))))

