(require 'jezebel-test-util)
(require 'jezebel)

(defconst jezt-simple-grammar
  '((:include jez-root-grammar)
    (top "hello")
    (foo bar qux)))

(defun* jezt-examine-grammar (grammar &rest args)
  (apply #'jez-describe-parser
         (jez--slurp-grammar grammar (jez--make-parser))
         args))

(defun* jezt-find-primitive (parser state-sym)
  (loop for state-prim being the hash-keys of
        (jez-parser--expansion-cache parser) 
        using (hash-values irn)
        for irn-state-sym = (jez-irn--symbol irn)
        when (eq irn-state-sym state-sym)
        return state-prim))

(defun* jezt-find-irn (parse state-sym)
  (loop for state-prim being the hash-keys of
        (jez-parser--pstates parser) 
        using (hash-values irn)
        for irn-state-sym = (jez-irn--symbol irn)
        when (eq irn-state-sym state-sym)
        return irn))

(defun* jezt-describe-irn (parser irn)
  (let* ((type (jez-struct-type irn))
         (type-name
          (and (symbolp type)
               (if (and type
                        (string-match "^jez-\\(.*\\)$"
                                      (symbol-name type))
                        (jez-irn-p irn))
                   (match-string 1 (symbol-name type))
                 (symbol-name type)))))
    (cond (type-name
           (princ (format "%s" type-name))
           (case type
             (jez-char
              (princ
               (format " %S" (char-to-string
                              (jez-char--char irn)))))))
          (t
           (princ (format "%S" irn))))))

(defun* jezt-describe-state (state stepno)
  (princ (format "step %d\n" stepno))
  (princ "and-stack:\n")
  (loop with parser = (jez-state--parser state)
        for state-sym in (jez-state--and-stack state)
        for i upfrom 0
        for irn = (jezt-find-irn parser state-sym)
        for prim = (jezt-find-primitive parser state-sym)
        do (progn
             (princ (format " %2d: " i))
             (jezt-describe-irn parser irn)
             (princ "\n"))))

(defconst jezt-parse-debug-keymap
  (let ((keymap (make-sparse-keymap)))
    (define-key keymap [(?\ )] 'step)
    (define-key keymap [(?g)] 'go)
    (define-key keymap [(?e)] #'eval-expression)
    (define-key keymap [(?q)] #'keyboard-quit)
    (define-key keymap [(control ?g)] #'keyboard-quit)
    (define-key keymap [(?r)] #'recursive-edit)
    keymap))

(defvar jezt-debug-prompt
  (concat
   "Action: "
   "(go:\\[go]) "
   "(step:\\[step]) "
   "(eval:\\[eval-expression]) "
   "(edit:\\[recursive-edit]) "
   "(quit:q) "))

(defun* jezt-try-parse (grammar text &optional debug)
  (with-current-buffer (get-buffer-create "*jezt*")
    (delete-region (point-min) (point-max))
    (save-excursion
      (insert text))
    (let* ((parser (jez-compile grammar))
           (state (jez-begin-parse parser))
           (stepno 0)
           debug-buf
           success)

      (when debug
        (setf debug-buf (get-buffer-create "*jdebug*")))
      
      (while (progn
               (when debug
                 (with-current-buffer debug-buf
                   (delete-region (point-min) (point-max))
                   (let ((standard-output debug-buf))
                     (jezt-describe-state state stepno)))
                 ;; Custom little command loop we use to prompt the
                 ;; user at each step.
                 (save-excursion
                   (save-restriction
                     (while
                         (let* ((key (read-key-sequence-vector
                                      (let ((overriding-local-map
                                             jezt-parse-debug-keymap))
                                        (substitute-command-keys
                                         jezt-debug-prompt))))
                                (binding (lookup-key
                                          jezt-parse-debug-keymap
                                          key)))
                           (cond ((eq binding 'step)
                                  nil)
                                 ((eq binding 'go)
                                  (setf debug nil)
                                  nil)
                                 ((commandp binding t)
                                  (call-interactively binding nil key)
                                  (when (eq binding 'eval-expression)
                                    (sit-for 1))
                                  t)
                                 (t
                                  (message "No binding for %s"
                                           (key-description key))
                                  (beep)
                                  (sit-for 1)
                                  t)))))))
               (case (jez-advance state)
                 (done (setf success t) nil)
                 (fail nil)
                 (t t)))
        (incf stepno))
      (and success (eobp)))))

(ert-deftest jezt-compile-grammar ()
  (let* ((parser (jez-compile jezt-simple-grammar)))
    (jez-parser--states parser)))

(ert-deftest jezt-simple-parse ()
  (progn
    (should-not
     (jezt-try-parse jezt-simple-grammar "test"))
    (should-not
     (jezt-try-parse jezt-simple-grammar "helloo"))
    (should
     (jezt-try-parse jezt-simple-grammar "hello"))))

(ert-deftest jezt-repetition-parse ()
  (let ((grammar '((:include jez-root-grammar)
                   (top "a" (* "b") "c"))))
    (jezt-try-parse grammar "abc")))

(defun foo ()
  (interactive)
  (let ((grammar '((:include jez-root-grammar)
                   (top "a" (* "b") "c"))))
    (jezt-try-parse grammar "abc" t)))

(provide 'jezebel-test)
