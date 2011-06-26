(require 'jezebel-test-util)
(require 'jezebel)

(defun jezt-create-simple-grammar ()
  (jez-make-grammar
   (include jez-root-grammar)
   (rule top "hello")))

(ert-deftest jezt-make-grammar ()
  (jezt-create-simple-grammar))

(ert-deftest jezt-compile-grammar ()
  (let* ((grammar (jezt-create-simple-grammar))
         (parser (jez-grammar-compile grammar)))
    (jezt-hash-table-to-alist (jez-grammar--rules grammar))
    ))

(provide 'jezebel-test)
