; (declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 Int) (Node_2 Tree)) (Nil))))
(declare-fun flatten3 (Tree) list)
(declare-fun append (list list) list)
(declare-fun flatten0 (Tree) list)
(assert (not (forall ((p Tree)) (= (flatten3 p) (flatten0 p)))))
; (assert
;   (forall ((x Tree))
;     (= (flatten3 x)
;       (ite
;         (is-Nil x) nil
;         (ite
;           (is-Nil (Node_0 x)) (cons (Node_1 x) (flatten3 (Node_2 x)))
;           (flatten3
;             (Node (Node_0 (Node_0 x))
;               (Node_1 (Node_0 x))
;               (Node (Node_2 (Node_0 x)) (Node_1 x) (Node_2 x)))))))))

 (assert (= (flatten3 Nil) nil))

(assert
  (forall ((t Tree) (n Int))
    (= (flatten3 (Node Nil n t)) (cons n (flatten3 t)))))


; rotate to right tree
(assert
  (forall ((l1 Tree) (ln Int) (l2 Tree) (n Int) (r Tree))
    (= (flatten3 (Node (Node l1 ln l2) n r)) 
      (flatten3 (Node l1 ln (Node l2 n r))))))


;

; (assert
;   (forall ((x list) (y list))
;     (= (append x y)
;       (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))

(assert (forall ((x list)) (= (append nil x) x)))
(assert (forall ((x Int) (y list) (z list)) (= (append (cons x y) z) (cons x (append y z)))))

; (assert
;   (forall ((x Tree))
;     (= (flatten0 x)
;       (ite
;         (is-Nil x) nil
;         (append (append (flatten0 (Node_0 x)) (cons (Node_1 x) nil))
;           (flatten0 (Node_2 x)))))))

(assert (= (flatten0 Nil) nil))
(assert
  (forall ((t1 Tree) (t2 Tree) (n Int))
    (= (flatten0 (Node t1 n t2))
      (append (append (flatten0 t1) (cons n nil)) (flatten0 t2)))))
(check-sat)
