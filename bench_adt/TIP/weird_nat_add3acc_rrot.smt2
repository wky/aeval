(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (add3acc x y z) (add3acc z x y)))))

; (assert
;   (forall ((x Nat) (y Nat) (z Nat))
;     (= (add3acc x y z)
;       (ite
;         (is-S x) (add3acc (p x) (S y) z)
;         (ite (is-S y) (add3acc Z (p y) (S z)) z)))))


(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (add3acc (S x) y z) (add3acc x (S y) z))))
(assert
  (forall ((y Nat) (z Nat))
    (= (add3acc Z (S y) z) (add3acc Z y (S z)))))

(assert
  (forall ((z Nat))
    (= (add3acc Z Z z) z)))

(check-sat)