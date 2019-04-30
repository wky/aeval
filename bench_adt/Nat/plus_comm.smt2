(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)

(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))


(assert
  (not (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x)))))

(check-sat)
