(require 'ert)

(defmacro should-eql (a b)
  `(should (eql ,a ,b)))

(defmacro should-equal (a b)
  `(should (equal ,a ,b)))

(defmacro jezt-passthrough (val arg-sym &rest forms)
  `(funcall (lambda (,arg-sym) ,@forms ,arg-sym) ,val))
(put 'jezt-passthrough 'lisp-indent-function 1)



(provide 'jezebel-test-util)
