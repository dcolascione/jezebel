;; -*- lexical-binding: t -*-
(require 'jezebel-test-util)
(require 'jezebel-util)
(require 'jezebel-lr)

(defconst jezt-toy-terminals
  '((a . 1)
    (b . 2)
    (c . 3)
    (d . 4)))

(defconst jezt-toy-grammar
  '((A a b)
    (A B)
    (B b a)))

(defconst jezt-expr-terminals
  '((+ . 0)
    (* . 1)
    (i . 2)
    ({ . 3)
    (} . 4)))

(defconst jezt-expr-grammar
  '((E E + T)
    (E T)
    (T T * F)
    (T F)
    (F { E })
    (F i)))

(ert-deftest jezt-lr-slurp ()
  (jez-lr-slurp-grammar
   jezt-toy-grammar
   jezt-toy-terminals
   'A))

(defun jezt-build-string (&rest args)
  (concat (mapconcat #'identity args "\n") "\n"))

(ert-deftest jez-lr0-closure ()
  (let* ((lr (jez-lr-slurp-grammar
              jezt-expr-grammar
              jezt-expr-terminals
              'E))
         (start-item (jez-lr-make-item 0 0))
         (start-state (list start-item))
         (closed-state (jez-lr0-closure lr start-state)))
    (should (equal
             (with-output-to-string
                 (dolist (item closed-state)
                   (princ (format "%s\n" (jez-dbg-format-item item lr)))))
             (jezt-build-string
              "^→•E$"
              "E→•E+T"
              "E→•T"
              "T→•T*F"
              "T→•F"
              "F→•{E}"
              "F→•i")))))

(ert-deftest jez-lr0-goto ()
  (let* ((lr (jez-lr-slurp-grammar
              jezt-expr-grammar
              jezt-expr-terminals
              'E))
         (start-state (list (jez-lr-make-item 0 0)
                            (jez-lr-make-item 1 1)))
         (closed-state (jez-lr0-closure lr start-state))
         (next-state (jez-lr0-goto lr closed-state
                                   (gethash
                                    '+ (jez-lr-sym->symno lr)))))
    (should
     (equal
      (with-output-to-string
          (dolist (item next-state)
            (princ (format "%s\n" (jez-dbg-format-item item lr)))))
      (jezt-build-string
       "E→E+•T"
       "T→•T*F"
       "T→•F"
       "F→•{E}"
       "F→•i")))))

(defun jezt-canonical-lr0-construction-test ()
  (let* ((lr (jez-lr-slurp-grammar
              jezt-expr-grammar
              jezt-expr-terminals
              'E))
         (states (jez-lr-states lr))
         (transitions (jez-lr-transitions lr)))
    ;; We should have no duplicate states and no duplicate transitions.
    (should (equal states (remove-duplicates states :test 'equal)))
    (should (equal transitions (remove-duplicates transitions :test 'equal)))
    (should (equal (length transitions) 23))

    ;; Make sure we generate all the states we expect
    (should
     (equal
      (with-output-to-string
          (dotimes (i (length states))
            (princ (format "State %d:\n" i))
            (dolist (item (aref states i))
              (princ (format "%s\n" (jez-dbg-format-item item lr))))
            (princ "\n")))
      (jezt-build-string
       "State 0:"
       "^→•E$"
       "E→•E+T"
       "E→•T"
       "T→•T*F"
       "T→•F"
       "F→•{E}"
       "F→•i"
       ""
       "State 1:"
       "F→i•"
       ""
       "State 2:"
       "E→•E+T"
       "E→•T"
       "T→•T*F"
       "T→•F"
       "F→•{E}"
       "F→{•E}"
       "F→•i"
       ""
       "State 3:"
       "^→E•$"
       "E→E•+T"
       ""
       "State 4:"
       "E→T•"
       "T→T•*F"
       ""
       "State 5:"
       "T→F•"
       ""
       "State 6:"
       "T→T*•F"
       "F→•{E}"
       "F→•i"
       ""
       "State 7:"
       "T→T*F•"
       ""
       "State 8:"
       "E→E+•T"
       "T→•T*F"
       "T→•F"
       "F→•{E}"
       "F→•i"
       ""
       "State 9:"
       "^→E$•"
       ""
       "State 10:"
       "E→E+T•"
       "T→T•*F"
       ""
       "State 11:"
       "E→E•+T"
       "F→{E•}"
       ""
       "State 12:"
       "F→{E}•"
       ""
       )))

    (should
     (equal
      (with-output-to-string
          (dolist (tx transitions)
            (princ (format "%s\n" (jez-dbg-format-tx tx lr)))))
      (jezt-build-string
       "0→1 via i"
       "0→2 via {"
       "0→3 via E"
       "0→4 via T"
       "0→5 via F"
       "4→6 via *"
       "6→1 via i"
       "6→2 via {"
       "6→7 via F"
       "3→8 via +"
       "3→9 via $"
       "8→1 via i"
       "8→2 via {"
       "8→10 via T"
       "8→5 via F"
       "10→6 via *"
       "2→1 via i"
       "2→2 via {"
       "2→11 via E"
       "2→4 via T"
       "2→5 via F"
       "11→8 via +"
       "11→12 via }")))))

(ert-deftest jez-canonical-lr0-construction ()
  (jezt-canonical-lr0-construction-test))

(defun jezt-lalr-test-toy ()
  (let* ((lr (jez-lr-slurp-grammar
              jezt-toy-grammar
              jezt-toy-terminals
              'A))
         (states (jez-lr-states lr))
         (transitions (jez-lr-transitions lr))
         (la (jez-lr-lookaheads lr)))
    (should
     (equal
      (with-output-to-string
          (dotimes (i (length states))
            (princ (format "State %d:\n" i))
            (dolist (item (aref states i))
              (princ
               (format "%s\n"
                       (jez-dbg-format-item item lr la
                                            :la-prefix " LA:"))))
            (princ "\n")))
      (jezt-build-string
       "State 0:"
       "^→•A$"
       "A→•ab"
       "A→•B"
       "B→•ba"
       ""
       "State 1:"
       "A→a•b"
       ""
       "State 2:"
       "B→b•a"
       ""
       "State 3:"
       "^→A•$"
       ""
       "State 4:"
       "A→B• LA:{$}"
       ""
       "State 5:"
       "^→A$• LA:∅"
       ""
       "State 6:"
       "B→ba• LA:{$}"
       ""
       "State 7:"
       "A→ab• LA:{$}"
       "")))))

(ert-deftest jez-lalr-toy ()
  (jezt-lalr-test-toy))

(ert-deftest jez-lalr-nqlalr-1 ()
  "This test ensures we don't fall into the first kind of NQLALR trap.
It's also a nice stress test of the relation engine."
  (let* ((lr (jez-lr-slurp-grammar
              '((S b A d)
                (S a A c)
                (B g)
                (S a g d)
                (A B)
                (S b g c))
              '((a . 1)
                (b . 2)
                (c . 3)
                (d . 4)
                (g . 5))
              'S))
         (states (jez-lr-states lr))
         (transitions (jez-lr-transitions lr))
         (la (jez-lr-lookaheads lr)))
    (should
     (equal
      (with-output-to-string
          (dotimes (i (length states))
            (princ (format "State %d:\n" i))
            (dolist (item (aref states i))
              (princ
               (format "%s\n"
                       (jez-dbg-format-item item lr la
                                            :la-prefix " LA:"))))
            (princ "\n")))
      "State 0:
^→•S$
S→•bAd
S→•aAc
S→•agd
S→•bgc

State 1:
S→a•Ac
B→•g
S→a•gd
A→•B

State 2:
S→b•Ad
B→•g
A→•B
S→b•gc

State 3:
^→S•$

State 4:
^→S$• LA:∅

State 5:
B→g• LA:{d}
S→bg•c

State 6:
A→B• LA:{c d}

State 7:
S→bA•d

State 8:
S→bAd• LA:{$}

State 9:
S→bgc• LA:{$}

State 10:
B→g• LA:{c}
S→ag•d

State 11:
S→aA•c

State 12:
S→aAc• LA:{$}

State 13:
S→agd• LA:{$}

"))))

(ert-deftest jez-lalr-nqlalr-2 ()
  "This test ensures we don't fall into the second kind of NQLALR trap.
It's also a nice stress test of the relation engine."
  (let* ((lr (jez-lr-slurp-grammar
              '((S a B d)
                (B D E)
                (S C B g)
                (S c d)
                (C c)
                (D)
                (E))
              '((a . 1)
                (b . 2)
                (c . 3)
                (d . 4)
                (g . 5))
              'S))
         (states (jez-lr-states lr))
         (transitions (jez-lr-transitions lr))
         (la (jez-lr-lookaheads lr)))
    (should
     (equal
      (with-output-to-string
          (dotimes (i (length states))
            (princ (format "State %d:\n" i))
            (dolist (item (aref states i))
              (princ
               (format "%s\n"
                       (jez-dbg-format-item item lr la
                                            :la-prefix " LA:"))))
            (princ "\n")))
      "State 0:
^→•S$
S→•aBd
S→•CBg
S→•cd
C→•c

State 1:
S→a•Bd
B→•DE
D→• LA:{d}

State 2:
S→c•d
C→c• LA:{g}

State 3:
^→S•$

State 4:
B→•DE
S→C•Bg
D→• LA:{g}

State 5:
S→CB•g

State 6:
B→D•E
E→• LA:{d g}

State 7:
B→DE• LA:{d g}

State 8:
S→CBg• LA:{$}

State 9:
^→S$• LA:∅

State 10:
S→cd• LA:{$}

State 11:
S→aB•d

State 12:
S→aBd• LA:{$}

"))))

(ert-deftest jez-lalr-demo ()
  (let* ((lr (jez-lr-slurp-grammar
              '((S E)
                (E E - T)
                (E T)
                (T n)
                (T { E }))
              '((- . 1)
                ({ . 2)
                (} . 3)
                (n . 4))
              'S))
         (states (jez-lr-states lr))
         (transitions (jez-lr-transitions lr))
         (la (jez-lr-lookaheads lr)))
    (should
     (equal
      (with-output-to-string
          (dotimes (i (length states))
            (princ (format "State %d:\n" i))
            (dolist (item (aref states i))
              (princ
               (format "%s\n"
                       (jez-dbg-format-item item lr la
                                            :la-prefix " LA:"))))
            (princ "\n")))
      "State 0:
^→•S$
S→•E
E→•E-T
E→•T
T→•n
T→•{E}

State 1:
E→•E-T
E→•T
T→•n
T→•{E}
T→{•E}

State 2:
T→n• LA:{- } $}

State 3:
^→S•$

State 4:
S→E• LA:{$}
E→E•-T

State 5:
E→T• LA:{- } $}

State 6:
E→E-•T
T→•n
T→•{E}

State 7:
E→E-T• LA:{- } $}

State 8:
^→S$• LA:∅

State 9:
E→E•-T
T→{E•}

State 10:
T→{E}• LA:{- } $}

"))))

(defun jezt-do-set-test (idx n)
  (let ((v (make-bool-vector n nil))
        (r nil))
    (dolist (q idx)
      (aset v q t))
    (jez-do-set (q v)
      (push q r))
    (setf r (nreverse r))
    (should (equal r idx))))

(ert-deftest jezt-do-set ()
  (jezt-do-set-test '(1 3 4 7) 10))

(ert-deftest jezt-do-set-empty ()
  (jezt-do-set-test nil 10))

(ert-deftest jezt-do-set-all ()
  (jezt-do-set-test '(0 1 2 3 4) 5))

(defun jezt-view-toylr ()
  (interactive)
  (let ((toylr
         (jez-lr-slurp-grammar
          jezt-toy-grammar
          jezt-toy-terminals
          'A)))
    (jez-lr-view-automaton
     toylr
     :la-type :lalr
     :numbered-states t
     :numbered-ntt t
     :background nil)))

(defun jezt-view-complex-lr ()
  (jez-lr-view-automaton
   (jez-lr-slurp-grammar
    '((S E)
      (E E P T)
      (P -)
      (P +)
      (E T)
      (T n)
      (T \( E \)))
    '((- . 1)
      (+ . 2)
      (\( . 3)
      (\) . 4)
      (n . 5))
    'S)
   :la-type :lalr-full
   :numbered-states t
   :background t))
