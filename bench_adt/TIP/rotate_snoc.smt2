; (declare-sort sk_a 0)
; (declare-datatypes ()
;   ((list (nil) (cons (head sk_a) (tail list)))))
; (declare-datatypes () ((Nat (Z) (S (p Nat)))))
; (declare-fun snoc (sk_a list) list)
; (declare-fun rotate (Nat list) list)
; (declare-fun length (list) Nat)
; (assert (not (forall ((xs list)) (= (rotate (length xs) xs) xs))))
; (assert
;   (forall ((x sk_a) (y list))
;     (= (snoc x y)
;       (ite (is-cons y) (cons (head y) (snoc x (tail y))) (cons x nil)))))
; (assert
;   (forall ((x Nat) (y list))
;     (= (rotate x y)
;       (ite
;         (is-S x)
;         (ite (is-cons y) (rotate (p x) (snoc (head y) (tail y))) nil) y))))
; (assert
;   (forall ((x list))
;     (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))












(declare-datatypes () ((Nat (succ (pred Nat)) (zero))))
(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)

(declare-fun rotate (Nat Lst) Lst)

(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y)))))
(assert (forall ((x Lst)) (= (rotate zero x) x)))
(assert (forall ((n Nat)) (= (rotate (succ n) nil) nil)))
(assert (forall ((n Nat) (y Nat) (x Lst)) (= (rotate (succ n) (cons y x)) (rotate n (append x (cons y nil))))))



(assert (not (forall ((x Lst)) (= (rotate (len x) x) x))))
(check-sat)



(check-sat)
