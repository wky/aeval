(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3 (Nat Nat Nat) Nat)
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat)) (= (add3 x y z) (add3 x z y)))))

(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (add3 (S x) y z) (S (add3 x y z)))))

(assert
  (forall ((y Nat) (z Nat))
    (= (add3 Z (S y) z) (S (add3 Z y z)))))


(assert
  (forall ((z Nat))
    (= (add3 Z Z z) z)))

; (assert
;   (forall ((x Nat) (y Nat) (z Nat))
;     (= (add3 x y z)
;       (ite
;         (is-S x) (S (add3 (p x) y z))
;         (ite (is-S y) (S (add3 Z (p y) z)) z)))))
(check-sat)
