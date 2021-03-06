;;
;; High-level tests for Jezebel.  Please write tests such that they
;; can be evaluated using C-c C-e.
;;

(require 'jezebel-test-util)
(require 'jezebel)
(require 'ert)

(defconst jezt-simple-grammar
  '((top "hello")
    (foo bar qux)))

(cl-defun jezt-hash-rmap (value
                          table
                          &optional (test #'eq)
                          &aux result)
  "Find a key in TABLE mapping to VALUE."
  (maphash (lambda (hkey hvalue)
             (when (funcall test hvalue value)
               (setf result hkey)))
           table)
  result)

(cl-defun jezt-find-irn (parser name)
  "Find the IR node named NAME.  Return nil if
no such node exists in PARSER."
  (jezt-hash-rmap name
                  (jez-parser--node-names parser)))

(cl-defun jezt-find-primitive (parser name)
  "Find the primitive that compiled down to NAME."
  (let ((irn (if (jez-irn-p name)
                 name
               (jezt-find-irn parser name))))
    (jezt-hash-rmap irn nil)))

(cl-defun jezt-describe-irn (parser irn)
  (let* ((type (jez-struct-type irn))
         (type-name (progn (string-match "^jez-\\(.*\\)$"
                                         (symbol-name type))
                           (match-string 1 (symbol-name type))))
         (primitive (jezt-find-primitive parser irn)))

    (princ (format "%s%s" type (if primitive
                                   (format " %S" primitive)
                                 "")))
    (case type
      (jez-char (princ
                 (format " char:%S" (char-to-string
                                     (jez-char--char irn)))))
      (jez-end-state (princ
                      (format " result:%S"
                              (jez-end-state--result irn)))))))

(cl-defun jezt-describe-stackent (parser val)
  (let (irn)
    (cond ((and (symbolp val)
                (fboundp val)
                (string-match "^jez-irn" (symbol-name val))
                (setf irn (jezt-find-irn parser val)))
           (jezt-describe-irn parser irn))
          (t
           (prin1 val)))))

(cl-defun jezt-describe-state (state stepno point)
  (princ (format "step %d point:%d\n" stepno point))
  (jez-with-slots (and-stack or-stack)
      (jez-state state)

    (princ (format "and-stack:%S\n" and-stack))
    (loop for val in and-stack
       for i upfrom 0
       do (progn
            (princ (format " %2d: " i))
            (jezt-describe-stackent nil val)
            (princ "\n")))

    (princ "\nor-stack:\n")
    (loop for val in or-stack
       for i upfrom 0
       do (progn
            (princ (format " %2d: " i))
            (jezt-describe-stackent nil val)
            (princ "\n")))))

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

(cl-defun jezt-try-parse (grammar text &optional debug)
  (with-current-buffer (get-buffer-create "*jezt*")
    (delete-region (point-min) (point-max))
    (save-excursion
      (insert text))
    (let* ((parser (jez-compile grammar))
           (state (jez-begin-parse parser))
           (stepno 0)
           debug-buf
           success
           point)

      (when debug
        (setf debug-buf (get-buffer-create "*jezt*"))
        (select-window (get-buffer-window "*jezt*" 'visible)))

      (while (progn
               (when debug
                 (setf point (point))
                 (with-current-buffer debug-buf
                   (delete-region (point-min) (point-max))
                   (let ((standard-output debug-buf))
                     (jezt-describe-state state stepno point)))
                 ;; Custom little command loop we use to prompt the
                 ;; user at each step.
                 (while
                     (let* ((key
                             (with-temp-message
                                 (let ((overriding-local-map
                                        jezt-parse-debug-keymap))
                                   (substitute-command-keys
                                    jezt-debug-prompt))
                               (read-key-sequence-vector nil)))
                            (binding (lookup-key
                                      jezt-parse-debug-keymap
                                      key)))
                       (cond ((eq binding 'step)
                              nil)
                             ((eq binding 'go)
                              (setf debug nil)
                              nil)
                             ((commandp binding t)
                              (let* ((parser nil)
                                     (and-stack (jez-state--and-stack state)))
                                (call-interactively binding nil key))
                              (when (eq binding 'eval-expression)
                                (sit-for 10))
                              t)
                             (t
                              (message "No binding for %s"
                                       (key-description key))
                              (beep)
                              (sit-for 1)
                              t)))))
               (case (jez-advance state)
                 (done (setf success t) nil)
                 (fail nil)
                 (t t)))
        (incf stepno))
      success)))

(ert-deftest jezt-compile-grammar ()
  (jez-compile jezt-simple-grammar))

(ert-deftest jezt-simple-parse ()
  (progn
    (should-not
     (jezt-try-parse jezt-simple-grammar "test"))
    (should-not
     (jezt-try-parse jezt-simple-grammar "helloo"))
    (should
     (jezt-try-parse jezt-simple-grammar "hello"))))

(ert-deftest jezt-repetition-parse ()
  (let ((grammar '((top "a" (* "b") "c"))))
    (should
     (jezt-try-parse grammar "abc"))
    (should
     (jezt-try-parse grammar "abbbbbbc"))
    (should-not
     (jezt-try-parse grammar "abbbbbb"))
    (should
     (jezt-try-parse grammar "ac"))))

(ert-deftest jezt-ochoice-parse ()
  (let ((grammar '((top "a" (/ "b" "c" "x") "d"))))
    (should
     (jezt-try-parse grammar "abd"))
    (should-not
     (jezt-try-parse grammar "ad"))
    (should
     (jezt-try-parse grammar "acd"))
    (should-not
     (jezt-try-parse grammar "ac"))))

(ert-deftest jezt-ast-construction ()
  (let ((grammar '((top (ast-node 'hello "hello")))))
    (should
     (jezt-try-parse grammar "hello"))))

(provide 'jezebel-test)
