(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)

(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))


(assert
  (not (forall ((x Nat) (y Nat) (z Nat)) (= (plus (plus x y) z) (plus x (plus y z))))))

(check-sat)
