(require 'jezebel-test-util)
(require 'jezebel-util)

(eval-and-compile
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
  (jezt-functional-struct-test t))

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

(defstruct jezt-foo-vector a b c)
(defstruct (jezt-foo-list (:type list) (:named)) a b c)

(ert-deftest jezt-jez-slot-value-vector ()
  (let ((val (make-jezt-foo-vector :a 1 :b 2 :c 3)))
    (should-eql (jez-slot-value 'jezt-foo-vector val 'c) 3)
    (setf (jez-slot-value 'jezt-foo-vector val 'c) 4)
    (should-eql (jez-slot-value 'jezt-foo-vector val 'c) 4)))

(ert-deftest jezt-jez-slot-value-list ()
  (let ((val (make-jezt-foo-list :a 1 :b 2 :c 3)))
    (should-eql (jez-slot-value 'jezt-foo-list val 'c) 3)
    (setf (jez-slot-value 'jezt-foo-list val 'c) 4)
    (should-eql (jez-slot-value 'jezt-foo-list val 'c) 4)))

(ert-deftest jezt-with-struct-slots ()
  (let ((val (make-jezt-foo-vector :a 1 :b 2 :c 3)))
    (should-equal (jez-with-slots
                   (a b c) (jezt-foo-vector val)
                   (list c b a))
                  (list 3 2 1))))

(ert-deftest jezt-nested-with-struct-slots ()
  (let ((val (make-jezt-foo-vector :a 1 :b 2 :c 3))
        (val2 (make-jezt-foo-list :a 4 :b 5 :c 6)))
    (jez-with-slots (a) (jezt-foo-vector val)
      (jez-with-slots (b) (jezt-foo-list val2)
        (should-equal (list a b)
                      (list 1 5))))))


(provide 'jezebel-util-test)
