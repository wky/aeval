(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun pow (Nat Nat) Nat)

(assert (not (forall ((x Nat)) (= (pow (S Z) x) (S Z)))))

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
; (assert
;   (forall ((x Nat) (y Nat))
;     (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))

(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))

(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (mult (S x) y) (plus y (mult x y)))))

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (pow x y) (ite (is-S y) (mult x (pow x (p y))) (S Z)))))

(assert
  (forall ((x Nat))
    (= (pow x Z) (S Z))))

(assert
  (forall ((x Nat) (y Nat))
    (= (pow x (S y)) (mult x (pow x y)))))

(check-sat)
