(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun acc_plus (Nat Nat) Nat)


(assert (forall ((y Nat)) (= (plus Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))


(assert (forall ((y Nat)) (= (acc_plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (acc_plus (S x) y) (acc_plus x (S y)))))

(assert
  (not (forall ((x Nat) (y Nat)) (= (plus x y) (acc_plus x y)))))


; (assert
;   (forall ((x Nat) (y Nat))
;     (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (acc_plus x y) (ite (is-S x) (acc_plus (p x) (S y)) y))))
(check-sat)
