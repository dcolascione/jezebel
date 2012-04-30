(require 'jezebel-mode)

(defconst jezt-cmode-grammar
  '((:section :ast-node)

    (top
     (: (* optws)
        (* (: optws toplevel-declaration optws))
        (* optws)))

    (toplevel-declaration
     (: variable-declaration))

    (variable-declaration
     (: type ws variable-name optws ";"))

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

    (:section :font)

    (type font-lock-type-face)
    (variable-name font-lock-variable-name-face)))

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
