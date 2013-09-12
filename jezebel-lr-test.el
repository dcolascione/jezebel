;; -*- lexical-binding: t -*-

(require 'jezebel-test-util)
(require 'jezebel-util)

(ert-deftest jezt-int-set-basic ()
  (let (is)
    (setf is (jez-make-int-set))
    (should (jez-int-set-empty-p is))
    (should (not (jez-int-set-member-p is 42)))
    (should (not (jez-int-set-remove is 33)))

    (should (jez-int-set-add is -1))
    (should (not (jez-int-set-add is -1)))
    (should (not (jez-int-set-empty-p is)))
    (should (jez-int-set-member-p is -1))
    (should (not (jez-int-set-remove is -1)))
    (should (not (jez-int-set-member-p is -1)))))

(ert-deftest jezt-int-set-union ()
  (let (is is2)
    (setf is (jez-make-int-set '(1 3 5)))
    (setf is2 (jez-make-int-set '(0 2 4 6)))

    (should (jez-int-set-union is is2))

    (should (equal (jez-int-set-as-list is) '(0 1 2 3 4 5 6)))
    (should (equal (jez-int-set-as-list is2) '(0 2 4 6)))

    (should (not (jez-int-set-union is (jez-make-int-set))))
    (should (equal (jez-int-set-as-list is) '(0 1 2 3 4 5 6)))))

(ert-deftest jezt-int-set-union-into-empty ()
  (let (is is2)
    (setf is (jez-make-int-set))
    (setf is2 (jez-make-int-set '(0 2 4 6)))

    (should (eq (jez-int-set-union is is2) is))

    (should (equal (jez-int-set-as-list is) '(0 2 4 6)))
    (should (equal (jez-int-set-as-list is2) '(0 2 4 6)))))

(ert-deftest jezt-int-set-equal-are-equal ()
  (let (is is2)
    (setf is (jez-make-int-set))
    (setf is2 (jez-make-int-set))

    (loop for x in '(1 2 3 4)
          do (jez-int-set-add is x))

    (loop for x in '(4 3 2 1)
          do (jez-int-set-add is2 x))

    (should (equal is is2))
    (should (eql (sxhash is) (sxhash is2)))))

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

(ert-deftest jezt-lr-FIRST ()
    (let* ((lr (jez-lr-slurp-grammar
                '((A a b c)
                  (B B b)
                  (B b)
                  (B C b)
                  (C)
                  (C B c)
                  (B))
                jezt-lr-toy-terminals
                'A))
           (sym->symno (jez-lr-sym->symno lr))
           (testdata
            '(((A)   . (a))
              ((C)   . (b nil))
              ((B)   . (b nil))
              ((B A) . (b a))
              ((A B) . (a)))))

      (loop for (input . expected) in testdata
            for in-munge = (loop for x in input
                                 collect (or (gethash x sym->symno)
                                             (error "unknown symbol: %s" x)))
            for out-munge =
            (jez-make-int-set
             (loop for x in expected
                   collect (or (gethash x sym->symno)
                               (if (not x) jez-epsilon-sym)
                               (error "unknown symbol: %s" x))))


            for FIRST = (jez-lr-FIRST lr in-munge)
            do (assert (equal FIRST out-munge) t))))

(ert-deftest jezt-lr-closure ()
  (let* ((lr (jez-lr-slurp-grammar
              '((S B)
                (A a b c)
                (B B b)
                (B b)
                (B C b)
                (C)
                (C B c)
                (B))
              jezt-lr-toy-terminals
              'S))
         (item (jez-create-lr-item :prodno 0
                                   :dotpos 0
                                   :lahead -2))
           (lrs (jez-create-lr-state)))
    (jez-lr-state-add-item lrs item)
    (jez-lr-nclosure lr lrs)

    (should (equal (jez-lr-state-items lrs)
                  '( [  0   0  -2]
                     [  1   0  -2]
                     [  3   0  -2]
                     [  3   0   2]
                     [  3   0   3]
                     [  4   0  -2]
                     [  4   0   2]
                     [  4   0   3]
                     [  5   0  -2]
                     [  5   0   2]
                     [  5   0   3]
                     [  6   0   2]
                     [  7   0   2]
                     [  8   0  -2]
                     [  8   0   2]
                     [  8   0   3])))))

(ert-deftest jez-goto ()
  (let* ((lr (jez-lr-slurp-grammar
              '((S C C)
                (C c C)
                (C d))
              jezt-lr-toy-terminals
              'S))
         (item (jez-create-lr-item :prodno 0
                                   :dotpos 0
                                   :lahead -2))
         (lrs (jez-create-lr-state)))
    (jez-lr-state-add-item lrs item)
    (jez-lr-nclosure lr lrs)
    (setf lrs (jez-lr-goto lr lrs (gethash 'd (jez-lr-sym->symno lr))))))

