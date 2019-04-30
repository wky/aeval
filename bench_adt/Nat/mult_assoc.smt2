(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)


(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))

(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (mult (S x) y) (plus y (mult x y)))))


(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat) (y Nat) (z Nat)) (= (plus (plus x y) z) (plus x (plus y z)))))
(assert (forall ((x Nat) (y Nat)) (= (mult x y) (mult y x))))
(assert (forall ((x Nat) (y Nat) (z Nat)) (= (mult x (plus y z)) (plus (mult x y) (mult x z)))))

(assert
  (not (forall ((x Nat) (y Nat) (z Nat)) (= (mult x (mult y z)) (mult (mult x y) z)))))

(check-sat)
