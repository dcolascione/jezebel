(require 'ert)

(defmacro should-eql (a b)
  `(should (eql ,a ,b)))

(defmacro should-equal (a b)
  `(should (equal ,a ,b)))

(defmacro jezt-passthrough (val arg-sym &rest forms)
  `(funcall (lambda (,arg-sym) ,@forms ,arg-sym) ,val))
(put 'jezt-passthrough 'lisp-indent-function 1)

(defun jezt-hash-table-to-alist (hash)
  (loop for key in (sort
                    (loop for key being the hash-keys of hash
                          collect key)
                    (lambda (x y)
                      (string< (format "%S" x) (format "%S" y))
                      ))
        collect (cons key (gethash key hash))))

(provide 'jezebel-test-util)
