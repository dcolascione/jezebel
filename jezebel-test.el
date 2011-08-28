(require 'jezebel-test-util)
(require 'jezebel)

(defconst jezt-simple-grammar
  '((:include jez-root-grammar)
    (top "hello")
    (foo bar qux)))

(defun jezt-examine-grammar (grammar &rest args)
  (apply #'jez-describe-parser
         (jez--slurp-grammar grammar (jez--make-parser))
         args))

(ert-deftest jezt-compile-grammar ()
  (let* ((parser (jez-compile jezt-simple-grammar)))
    (jezt-hash-table-to-alist
     (jez-parser--states parser))))



(provide 'jezebel-test)
