;; -*- lexical-binding: t -*-

(require 'ert)
(require 'cl-lib) 

(defmacro should-eql (a b)
  `(should (eql ,a ,b)))

(defmacro should-equal (a b)
  `(should (equal ,a ,b)))

(defmacro jezt-passthrough (val arg-sym &rest forms)
  `(funcall (lambda (,arg-sym) ,@forms ,arg-sym) ,val))
(put 'jezt-passthrough 'lisp-indent-function 1)

(defun jezt-kill-symbols ()
  "Make all jezebel symbols unbound"
  (interactive)
  (cl-loop
     for feature in features
     when (string-match "^jezebel-" (symbol-name feature))
     do (unload-feature feature t))
  (cl-loop
     for x being the symbols
     when (string-match "^jezt?-" (symbol-name x))
     do (unintern x nil)))

(provide 'jezebel-test-util)
