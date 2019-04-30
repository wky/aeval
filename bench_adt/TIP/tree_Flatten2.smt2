;(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 Int) (Node_2 Tree)) (Nil))))
(declare-fun flatten2 (Tree list) list)
(declare-fun append (list list) list)
(declare-fun flatten0 (Tree) list)
(assert
  (not (forall ((p Tree)) (= (flatten2 p nil) (flatten0 p)))))


; (assert
;   (forall ((x Tree) (y list))
;     (= (flatten2 x y)
;       (ite
;         (is-Nil x) y
;         (flatten2 (Node_0 x) (cons (Node_1 x) (flatten2 (Node_2 x) y)))))))


(assert
  (forall ((t1 Tree) (t2 Tree) (n Int) (l list))
    (= (flatten2 (Node t1 n t2) l) (flatten2 t1 (cons n (flatten2 t2 l))))))

(assert
  (forall ((y list))
    (= (flatten2 Nil y) y)))

; (assert
;   (forall ((x list) (y list))
;     (= (append x y)
;       (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))

(assert (forall ((x list)) (= (append nil x) x)))
(assert (forall ((x Int) (y list) (z list)) (= (append (cons x y) z) (cons x (append y z)))))

(assert
  (forall ((p Tree) (l list))
    (= (flatten2 p l) (append (flatten0 p) l))))
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
