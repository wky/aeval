(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun acc_plus (Nat Nat) Nat)

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (acc_plus x y) (ite (is-S x) (acc_plus (p x) (S y)) y))))

(assert (forall ((y Nat)) (= (acc_plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (acc_plus (S x) y) (acc_plus x (S y)))))

(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (acc_plus x (acc_plus y z)) (acc_plus (acc_plus x y) z)))))

(check-sat)
