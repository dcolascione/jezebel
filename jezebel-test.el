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
    (should-eql (jez-tree-get (jez-tree-last-child tr) 'label) 'alast)
    ))

