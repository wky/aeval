; (declare-sort sk_a 0)
; (declare-datatypes ()
;   ((list (nil) (cons (head sk_a) (tail list)))))
; (declare-fun append (list list) list)
; (assert
;   (not
;     (forall ((xs list) (ys list) (zs list))
;       (=> (= (append xs zs) (append ys zs)) (= xs ys)))))
; (assert
;   (forall ((x list) (y list))
;     (= (append x y)
;       (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
; (check-sat)

(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(assert (not (forall ((x Lst) (y Lst) (z Lst)) (=> (= (append x z) (append y z)) (= x y)))))
(check-sat)
