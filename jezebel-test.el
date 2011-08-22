(require 'jezebel-test-util)
(require 'jezebel)

(defconst jezt-simple-grammar
  '((:include jez-root-grammar)
    (top "hello")
    (foo bar qux)))

(defun jezt-examine-grammar (grammar &rest args)
  (let ((parser (jez--make-parser)))
    (jez--slurp-grammar parser grammar)
    (apply #'jez-describe-parser parser args)))

(ert-deftest jezt-compile-grammar ()
  (let* ((parser (jez-compile jezt-simple-grammar)))
    (jezt-hash-table-to-alist
     (jez-parser--states parser))
    ))

(provide 'jezebel-test)
