(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(assert
  (not
    (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat))
      (= (add3acc (add3acc x1 x2 x3) x4 x5)
        (add3acc x1 (add3acc x2 x3 x4) x5)))))
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