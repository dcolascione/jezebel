(require 'jezebel-util)

(declare (optimize (speed 3) (safety 0)))

;;
;; Purely functional AST built incrementally by parsing.
;;

(define-functional-struct
 (jez-tree-node
  (:constructor jez--make-tree-node)
  (:copier nil)
  (:conc-name jez-tree-node--))
  "Node of an N-ary purely-functional zippered tree."

  ;; List of children of this node; updated lazily. jez-tree-node's
  ;; zippered list for this node is authoritative when it exists.
  children

  ;; plist of properties of this node
  properties)

(define-functional-struct
 (jez-tree
  (:constructor jez--make-tree)
  (:copier nil)
  (:conc-name jez-tree--))
  "View into a jez-tree.  Pure functional data structure."

  ;; Current jez-tree-node
  current

  ;; Is the current node dirty?
  dirty

  ;; Children of parent to the left of current; stored in reverse
  ;; order
  left

  ;; Children of parent to the right of current; stored in forward
  ;; order
  right

  ;; Parent jez-tree (not jez-tree-node!) or nil if we're at top
  parent

  ;; Properties of this tree node.
  properties
  )

(defun* jez-make-empty-tree ()
  "Create a brand-new empty tree."
  (jez--make-tree
   :current (jez--make-tree-node)))

(defun* jez-tree-prepend-child (tree &optional properties)
  "Add a child to the beginning of TREE's child list.  Return a
new cursor pointing at the new child.  Constant time."
  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :properties properties
   :dirty t
   :left nil
   :right (jez-tree-node--children (jez-tree--current tree))
   :parent tree))

(defun* jez-tree-append-child (tree &optional properties)
  "Add a child to the end of TREE's child list.  Return a new
cursor pointing at the new child.  Takes time proportional to the
number of children in TREE's current node."
  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :properties properties
   :dirty t
   :left (reverse
          (jez-tree-node--children (jez-tree--current tree)))
   :right nil
   :parent tree))

(defun* jez-tree-up (tree)
  "Move cursor to parent of current node.  Return a new cursor
pointing at the parent.  Raise error if already at top of tree.
Constant time if tree has not been modified; otherwise, takes
time proportional to the number of children in the parent."

  ;; If the current node isn't dirty, all we have to do is return the
  ;; cursor we saved when we went down into the current node.

  ;; Otherwise, life becomes trickier. We return a new cursor that
  ;; points at a new tree node. This new node is just like our parent,
  ;; except that its child list is reconstructed from TREE's zippered
  ;; child list, which takes into account any modifications we made.

  (let ((old-parent (jez-tree--parent tree)))
    (unless old-parent
      (error "already at top of tree"))
    (if (jez-tree--dirty tree)
        (copy-and-modify-jez-tree old-parent
         ;; Make new child to stand in for (jez-tree--current
         ;; old-parent).  The new child incorporates any changes we've
         ;; made since we branched from parent.
         :current (jez--make-tree-node
                   :children (append (reverse (jez-tree--left tree))
                                     (list (jez-tree--current tree))
                                     (jez-tree--right tree))
                   :properties (jez-tree-node--properties
                                (jez-tree--current old-parent)))

         ;; The new cursor is dirty because we need to propagate changes
         ;; all the way up to the top of the tree.
         :dirty t)

      ;; Not dirty. Return original parent cursor unchanged.
      old-parent)))

(defun* jez-tree-first-p (tree)
  "Return non-nil if current node of TREE has a previous sibling.
Constant time."
  (jez-tree--left tree))

(defun* jez-tree-last-p (tree)
  "Return non-nil if current node of TREE has a next sibling.
Constant time."
  (jez-tree--right tree))

(defun* jez-tree-children-p (tree)
  "Return non-nil if current node of TREE has children.  Constant
time."
  (jez-tree-node--children
   (jez-tree--current tree)))

(defun* jez-tree-root-p (tree)
  "Return non-nil if current node of TREE is the root.  Constant
time."
  (not (jez-tree--parent tree)))

(defun* jez-tree-prev-sibling (tree)
  "Return a new cursor pointing to the previous sibling of the
current node.  Raise error if there is no previous sibling.
Constant time."
  (let* ((old-left (jez-tree--left tree)))
    (copy-and-modify-jez-tree tree
     :current (or (first old-left)
                  (error "already at leftmost child"))
     :left (rest old-left)
     :right (list* (jez-tree--current tree)
                   (jez-tree--right tree)))))

(defun* jez-tree-next-sibling (tree)
  (let* ((old-right (jez-tree--right tree)))
    (copy-and-modify-jez-tree tree
     :current (or (first old-right)
                  (error "already at rightmost child"))
     :left (list* (jez-tree--current tree)
                  (jez-tree--left tree))
     :right (rest old-right))))

(defun* jez-tree-first-child (tree)
  "Return a cursor pointing to the first child of the current
node.  Raise error if the current node has no children.  Constant
time."
  (let ((children (jez-tree-node--children
                   (jez-tree--current tree))))
    (copy-and-modify-jez-tree tree
     :current (or (first children)
                  (error "current node has no children"))
     :dirty nil
     :left nil
     :right (rest children)
     :parent tree)))

(defun* jez-tree-last-child (tree)
  "Return a cursor pointing to the last child of the current
node.  Raise error if the current node has no children.  Time
proportional to number of children in current node."
  (let ((rchildren (reverse (jez-tree-node--children
                             (jez-tree--current tree)))))

    (copy-and-modify-jez-tree tree
     :current (or (first rchildren)
                  (error "current node has no children"))
     :dirty nil
     :left (rest rchildren)
     :right nil
     :parent tree)))

(defun* jez-tree-insert-sibling-before (tree)
  "Insert a sibling before current node.  Return a cursor
pointing to the new node.  Raise error if current node is the
root node.  Constant time."

  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :dirty t
   :left (jez-tree--left tree)
   :right (list* (jez-tree--current tree)
                 (jez-tree--right tree))
   :parent (or (jez-tree--parent tree)
               (error "root node cannot have siblings"))))

(defun* jez-tree-insert-sibling-after (tree)
  "Insert a sibling after current node.  Return a cursor pointing
to new node.  Raise error if current node is the root node.
Constant time."

  (copy-and-modify-jez-tree tree
   :current (jez--make-tree-node)
   :dirty t
   :left (list* (jez-tree--current tree)
                (jez-tree--left tree))
   :right (jez-tree--right tree)
   :parent (or (jez-tree--parent tree)
               (error "root node cannot have siblings"))))

(defun* jez-tree-get (tree prop)
  "Return the value of PROP in the current node of TREE.  Time
proportional to number of existing properties."

  (plist-get
   (jez-tree-node--properties (jez-tree--current tree))
   prop))

(defun* jez-tree-put (tree prop val)
  "Set PROP to VAL in the current node of TREE.  Return a new
cursor pointing to the modified node.  Time proportional to
number of existing properties."

  (copy-and-modify-jez-tree tree
    :current (copy-and-modify-jez-tree-node orig
               :properties (plist-put (copy-sequence orig)
                                      prop val))
    :dirty t))

(provide 'jezebel-tree)
