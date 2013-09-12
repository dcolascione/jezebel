(require 'cl)
(require 'jezebel-util)
(require 'jezebel-engine)
(require 'jezebel-grammar)

(defun* jez-compile (grammar &optional top-rd)
  "Compiles GRAMMAR into a jez-parser. Return the new parser instance.
TOP-RD denotes with which the generated parser will begin
parsing; by default, we begin with the rule called `top'."
  (let ((top-irn (jez-grammar-to-irn grammar top-rd)))
    (jez--make-parser top-irn)))

(provide 'jezebel)

