;; -*- lexical-binding: t -*-

(require 'jezebel-test-util)
(require 'jezebel-util)

(defun jezt-make-lr0-item (lr nonterm arrow &rest rhs-input)
  "Make an LR(0) item from a human-readable description
of a production."

  (let* ((sym->symno (jez-lr-sym->symno lr))
         (nontermno (or (gethash nonterm sym->symno)
                        (and (eq nonterm 'START) (jez-lr-min-nonterm lr))
                        (error "unknown symbol: %S" nonterm)))
         (dotpos nil)
         (rhs nil)
         (prodno nil))

    (unless (>= nontermno (jez-lr-min-nonterm lr))
      (error "LHS is not a nonterminal: %S" nonterm))

    (unless (equal arrow '->) (error "invalid item spec"))

    (setf rhs
          (loop for rterm in rhs-input
                for i upfrom 0
                if (eq rterm '@)
                do (progn
                     (when dotpos
                       (error "more than one dot in item spec"))
                     (setf dotpos i))
                else collect (or (gethash rterm sym->symno)
                                 (error "unknown symbol: %S" rterm))))

    (unless dotpos (error "no dot found"))

    (loop for candidate-prodno in (jez-lr-production-rules-for-symbol
                                   lr
                                   nontermno)

          if (equal rhs (jez-lr-rhs-for-prodno lr candidate-prodno))
          do (progn
               (when prodno (error "ambiguous production"))
               (setf prodno candidate-prodno)))

    (unless prodno (error "no production found: %S -> %S"
                          nonterm rhs-input))

    (cons prodno dotpos)))

(defun jezt-make-lr0-state (lr hr-items)
  "Make an LR(0) state from human-readable item descriptions."

  (delete-consecutive-dups
   (sort
    (loop for hr-item in hr-items
          collect (apply #'jezt-make-lr0-item lr hr-item))
    #'jez-lr0-item-<)))

(defun jezt-lr-lisp-symbol-for-symno (lr symno)
  "Find the lisp symbol for symbol numbered SYMNO in LR."

  (catch 'found
    (maphash
     (lambda (k v)
       (when (eq v symno)
         (throw 'found k)))
     (jez-lr-sym->symno lr))
    (error "could not find symbol for symno %s" symno)))

(defun jezt-pp-hr-symbol (lr symno)
  (cond
    ((eq symno (jez-lr-end-sym lr)) "#")
    (t (symbol-name (jezt-lr-lisp-symbol-for-symno
                     lr symno)))))

(cl-defun jezt-pp-production-rule (lr rule &optional stream &key dotpos lahead)
  (let* ((lhs (car rule))
         (rhs (cdr rule))
         (rhsidx 0))
    (princ (format "%15s \u2192 "
                   (jezt-lr-lisp-symbol-for-symno lr lhs))
           stream)
    (if (null rhs)
        (princ "\u03B5")
      (princ (mapconcat
              (lambda (symno)
                (prog1
                    (concat
                     (if (eql dotpos rhsidx) "\u00B7 ")
                     (jezt-pp-hr-symbol lr symno))
                  (incf rhsidx)))
              rhs " ")
             stream))
    (if (eql dotpos rhsidx)
        (princ " \u00B7" stream))
    (if lahead
        (princ (format "  [%s]" (jezt-pp-hr-symbol lr lahead))
               stream))
    (princ "\n" stream)))

(defun jezt-pp-lr (lr &optional stream)
  (princ (format "Production rules:\n") stream)
  (loop for rule across (jez-lr-productions lr)
        for prodno upfrom 0
        do (princ (format "  %03d: " prodno) stream)
        and do (jezt-pp-production-rule lr rule stream)))

(defun jezt-pp-item (lr item &optional stream)
  (princ (format "[%3s %3s %3s] "
                 (aref item 0)
                 (aref item 1)
                 (aref item 2))
         stream)
  (jezt-pp-production-rule
   lr
   (aref (jez-lr-productions lr) (jez-lr-item-prodno item))
   stream
   :dotpos (jez-lr-item-dotpos item)
   :lahead (jez-lr-item-lahead item)))

(defun jezt-pp-state (lr state &optional stream)
  (princ "LR State Items:\n" stream)
  (loop for item in (jez-lr-state-items state)
        do (progn
             (princ "  " stream)
             (jezt-pp-item lr item stream)))
  (princ "End\n" stream))

(defun jezt-pp-lr0-item (lr item &optional stream)
  (princ (format "(%3s . %3s) " (car item) (cdr item)) stream)
  (jezt-pp-production-rule
   lr
   (aref (jez-lr-productions lr) (car item))
   stream
   :dotpos (cdr item)))

(defun jezt-pp-lr0-state (lr state &optional stream)
  (princ "LR(0) State Items:\n" stream)
  (loop for item in state
        do (progn
             (princ " " stream)
             (jezt-pp-lr0-item lr item)))
  (princ "End\n" stream))

(defconst jezt-lr-toy-terminals
  '((a . 1)
    (b . 2)
    (c . 3)
    (d . 4)))

(ert-deftest jezt-lr-slurp ()
  (let*
      ((toyrules
        '((A a b)
          (A B)
          (B b a)))

       (toylr
        (jez-lr-slurp-grammar
         toyrules
         jezt-lr-toy-terminals
         'A)))

    toylr))

(ert-deftest jez-lr0-closure ()
  (let* ((lr (jez-lr-slurp-grammar
              '((E E + T)
                (E T)
                (T T * F)
                (T F)
                (F { E })
                (F i))

              '((+ . 0)
                (* . 1)
                (i . 2)
                ({ . 3)
                (} . 4))

              'E)))

    (should (equal (jez-lr0-closure
                    lr
                    (jezt-make-lr0-state
                     lr
                     '((START -> @ E))))
                   (jezt-make-lr0-state
                    lr
                    '((START -> @ E)
                      (E -> @ E + T)
                      (E -> @ T)
                      (T -> @ T * F)
                      (T -> @ F)
                      (F -> @ { E })
                      (F -> @ i)))))))

(ert-deftest jez-lr0-goto ()
  (let* ((lr (jez-lr-slurp-grammar
              '((E E + T)
                (E T)
                (T T * F)
                (T F)
                (F { E })
                (F i))

              '((+ . 0)
                (* . 1)
                (i . 2)
                ({ . 3)
                (} . 4))

              'E))
         (sym->symno (jez-lr-sym->symno lr)))

    (should (equal
             (jez-lr0-goto
              lr
              (jez-lr0-closure
               lr
               (jezt-make-lr0-state
                lr
                '((START -> E @)
                  (E -> E @ + T))))
              (gethash '+ sym->symno))

             (jezt-make-lr0-state
              lr
              '((E -> E + @ T)
                (T -> @ T * F)
                (T -> @ F)
                (F -> @ { E })
                (F -> @ i)))))))

(defun jezt-canonical-lr0-construction-test ()
  (let* ((lr (jez-lr-slurp-grammar
              '((E E + T)
                (E T)
                (T T * F)
                (T F)
                (F { E })
                (F i))

              '((+ . 0)
                (* . 1)
                (i . 2)
                ({ . 3)
                (} . 4))

              'E)))

    (destructuring-bind (states txdb) (jez-compute-lr0-states lr)
      (setf states (cl-coerce states 'list))
      ;; We should have no duplicate states and no duplicate transitions.
      (let ((transitions (jez-txdb--transitions txdb)))
        (should (equal states (remove-duplicates states :test 'equal)))
        (should (equal transitions (remove-duplicates transitions :test 'equal)))
        (should (equal (length transitions) 22)))

      ;; Make sure we generate all the states we expect
      (dotimes (i (length states))
        (princ (format "State %d:\n" i))
        (jezt-pp-lr0-state lr (elt states i)))

      (cl-loop
         for expected-state in
           '(((START -> @ E)
              (E -> @ E + T)
              (E -> @ T)
              (T -> @ T * F)
              (T -> @ F)
              (F -> @ { E })
              (F -> @ i))

             ((START -> E @)
              (E -> E @ + T))

             ((E -> T @)
              (T -> T @ * F))

             ((T -> F @))

             ((F -> { @ E })
              (E -> @ E + T)
              (E -> @ T)
              (T -> @ T * F)
              (T -> @ F)
              (F -> @ { E })
              (F -> @ i))

             ((F -> i @))

             ((E -> E + @ T)
              (T -> @ T * F)
              (T -> @ F)
              (F -> @ { E })
              (F -> @ i))

             ((T -> T * @ F)
              (F -> @ { E })
              (F -> @ i))

             ((F -> { E @ })
              (E -> E @ + T))

             ((E -> E + T @)
              (T -> T @ * F))

             ((T -> T * F @))

             ((F -> { E } @)))
         for sno upfrom 0
         do (let ((translated-state
                   (jezt-make-lr0-state lr expected-state)))
              (princ (format "Expecting to find state:\n"))
              (jezt-pp-lr0-state lr translated-state)
              (cond ((member translated-state states)
                     (setf states (remove translated-state states)))
                    (t (error "could not find state #%d: %S" sno
                              expected-state)))))

      (when states
        (error "unexpected states found")))))

(ert-deftest jez-canonical-lr0-construction ()
  (jezt-canonical-lr0-construction-test))

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

(defun jezt-lalr-test ()
  (let* ((toyrules
          '((A a b)
            (A B)
            (B b a)))
         (lr
          (jez-lr-slurp-grammar
           toyrules
           jezt-lr-toy-terminals
           'A))
         (lr0info (jez-compute-lr0-states lr))
         )
    lr0info
    ))


(defun jezt-view-toylr ()
  (let*
      ((toyrules
        '((A a b)
          (A B)
          (B b a)))

       (toylr
        (jez-lr-slurp-grammar
         toyrules
         jezt-lr-toy-terminals
         'A)))
    (jez-view-automaton
     toylr
     :la-type :lalr
     :numbered-states t
     :numbered-ntt t
     :background nil)))
