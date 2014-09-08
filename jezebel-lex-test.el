;; -*- lexical-binding: t -*-
(require 'jezebel-test-util)
(require 'jezebel-util)
(require 'jezebel-lex)

(defvar jezt-nfa-try-match-index nil)
(defvar jezt-nfa-success-index nil)
(defun jezt-nfa-on-accept ()
  (setf jezt-nfa-success-index jezt-nfa-try-match-index))

(defun jezt-nfa-match (nfa text)
  "Match NFA against TEXT and return the longest match.
Return nil if NFA did not match at all."
  (let* ((auto (jez-nfa-simple-automaton-create
                (jez-nfa-with-accept-function
                 (cond ((jez-nfa-p nfa) nfa)
                       ((stringp nfa) (jez-nfa-build `(regexp ,nfa)))
                       (t (jez-nfa-build nfa)))
                 #'jezt-nfa-on-accept)))
         (jezt-nfa-success-index nil)
         (length (length text))
         (i 0))
    (let ((jezt-nfa-try-match-index 0))
      (jez-nfa-simple-automaton-reset auto))
    (while (and (< i length)
                (let ((jezt-nfa-try-match-index (1+ i)))
                  (jez-nfa-simple-automaton-transition
                   auto
                   (aref text i))))
      (incf i))
    (when jezt-nfa-success-index
      (substring text 0 jezt-nfa-success-index))))

(defun jezt-nfa-match-test (pattern text expected)
  "Test when PATTERN matches TEXT, the match is EXPECTED.
If EXPECTED is `t', expect to match TEXT.  If TEXT or EXPECTED is
a symbol, match the value of that symbol."
  (let* ((expected (if (eq expected t) text expected))
         (text (if (symbolp text) (symbol-value text) text))
         (expected (if (symbolp expected)
                       (symbol-value expected)
                     expected))
         (result (jezt-nfa-match pattern text)))
    (unless (equal result expected)
      (error (concat "failed to match pattern %S against text %S"
                     ": match was %S expected %S")
             pattern
             text
             result
             expected))))

(defmacro jezt-define-nfa-test (name &rest testcases)
  "Define an NFA matcher testcase.
NAME is the ERT name of the testcase.  TESTCASES is an
unevaluated list of (PATTERN TEXT EXPECTED) triplets for
`jezt-nfa-match-test'."
  `(ert-deftest ,name ()
     (mapc (lambda (testcase)
             (apply #'jezt-nfa-match-test testcase))
           ',testcases)))
(put 'jezt-define-nfa-test 'lisp-indent-function 1)

(jezt-define-nfa-test jezt-nfa-matching
  ("abc" "abc" t)
  ("ab?c" "abc" t)
  ("abx?c" "abc" t)
  ("x*" "abc" "")
  ("a+bc?" "aaaabc" t)
  ("a\\(bc\\)+d" "abcbcbcd" t)
  ("a\\(bc\\)+d" "abbbd" nil))

(defconst jezt-nfa-evil-input "aaaaaaaaaaaaaaaaaaaaaaaa!")
(defconst jezt-nfa-evil-match "aaaaaaaaaaaaaaaaaaaaaaaa")

(jezt-define-nfa-test jezt-nfa-torture
  ;; Wikipedia list of malicious regexes.  We have a DFA and don't
  ;; suffer from exponential blowup, but we might as well test for
  ;; correctness.
  ("\\(a+\\)+" jezt-nfa-evil-input jezt-nfa-evil-match)
  ("\\([a-zA-Z]+\\)*" jezt-nfa-evil-input jezt-nfa-evil-match)
  ("\\(a+\\)+" jezt-nfa-evil-input jezt-nfa-evil-match))

(jezt-define-nfa-test jezt-nfa-bounded-repetition
  ("a\\{3\\}" "" nil)
  ("a\\{3\\}" "a" nil)
  ("a\\{3\\}" "aa" nil)
  ("a\\{3\\}" "aaa" "aaa")
  ("a\\{3\\}" "aaaa" "aaa"))

(jezt-define-nfa-test jezt-nfa-char-classes
  ("[ab]" "a" "a")
  ("[ab]" "b" "b")
  ("[ab]" "c" nil))

(jezt-define-nfa-test jezt-nfa-char-classes-negated
  ("[^ab]" "a" nil)
  ("[^ab]" "b" nil)
  ("[^ab]" "c" "c")
  ("[^ab]" "-" "-"))

(jezt-define-nfa-test jezt-nfa-empty
  ("" "abc" ""))

(provide 'jezebel-lex-test)
