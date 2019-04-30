(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)


(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))

(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (mult (S x) y) (plus y (mult x y)))))


(assert
  (not (forall ((x Nat) (y Nat)) (= (mult x y) (mult y x)))))

(check-sat)
