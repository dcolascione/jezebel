(require 'jezebel-mode)

(defconst jezt-cmode-grammar
  '((:section :ast-node)

    (top
     (* (: opt-ws toplevel-declaration opt-ws)))

    (toplevel-declaration
     (: variable-declaration))

    (variable-declaration
     (: type ws variable-name opt-ws ";"))

    (type
     (/ "int" "double" "char"))

    (variable-name
     (: identifier))

    (identifier
     (ast-node 'identifier
               (in "a-zA-Z_")
               (* (in  "a-zA-Z0-9_"))))

    (section :rule)

    (ws
     (+ (in " \t\n")))

    (opt-ws
     (* (in " \t\n")))

))

(defconst jezt-cmode-font-lock-keywords
  '(jez-font-lock-matcher)
  "Font-lock keywords for jezt-cmode")

(defconst jezt-cmode-font-lock-defaults
  '( jezt-cmode-font-lock-keywords
     nil                                ; not keywords only
     nil                                ; don't case-fold
     nil                                ; no special font-lock syntax
     nil                                ; no syntax-begin function
     )
  "Font-lock settings for jezt-cmode.")

(define-derived-mode jezt-cmode fundamental-mode "jezt-c"
  (jez-setup-buffer jezt-cmode-grammar)
  (setf font-lock-defaults jezt-cmode-font-lock-defaults))

(provide 'jezt-c-mode)
