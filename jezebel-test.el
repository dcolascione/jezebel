(require 'jezebel)
(require 'ert)

(ert-deftest jez-tree-add-child ()
  (let (v1 v2 new-node rootv1 rootv2)
    ;; Start with empty tree
    (setf v1 (jez-make-empty-tree))
    (should (eql (length (jez-tree--ancestors v1)) 0))
    (setf rootv1 (jez-tree--current-node v1))
    (should (jez-tree-node-p rootv1))

    ;; Add a child; make sure it takes
    (setf v2 (jez-tree-add-child v1))
    (should (eql (length (jez-tree--ancestors v2)) 1))
    (setf rootv2 (first (jez-tree--ancestors v2)))
    (should (jez-tree-node-p rootv2))

    ;; Make sure old root wasn't mutated.
    (should (eq rootv1 (jez-tree--current-node v1)))
    
    ;; Make sure the old and new tree roots are different (required
    ;; for the structure to be functionally persistent).
    (should-not (eq rootv1 rootv2))

    ;; Make sure the new node was added as the first (and only) child
    ;; of its parent.
    (setf new-node (jez-tree--current-node v2))
    (should (eql (length (jez-tree-node--left-children rootv2)) 1))
    (should (eql (length (jez-tree-node--right-children rootv2)) 0))
    (should (eq (first (jez-tree-node--left-children rootv2)) new-node))

    ))



