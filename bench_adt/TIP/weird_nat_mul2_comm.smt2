(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(declare-fun mul2 (Nat Nat) Nat)
(assert (not (forall ((x Nat) (y Nat)) (= (mul2 x y) (mul2 y x)))))

; (assert
;   (forall ((x Nat) (y Nat) (z Nat))
;     (= (add3acc x y z)
;       (ite
;         (is-S x) (add3acc (p x) (S y) z)
;         (ite (is-S y) (add3acc Z (p y) (S z)) z)))))

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (mul2 x y)
;       (ite
;         (is-S x)
;         (ite (is-S y) (S (add3acc (p x) (p y) (mul2 (p x) (p y)))) Z) Z))))


(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (add3acc (S x) y z) (add3acc x (S y) z))))
(assert
  (forall ((y Nat) (z Nat))
    (= (add3acc Z (S y) z) (add3acc Z y (S z)))))

(assert
  (forall ((z Nat))
    (= (add3acc Z Z z) z)))

(assert
  (forall ((z Nat))
    (= (add3acc Z z Z) z)))

(assert
  (forall ((z Nat))
    (= (add3acc z Z Z) z)))


(assert
  (forall ((x Nat) (y Nat))
    (= (mul2 (S x) (S y)) (S (add3acc x y (mul2 x y))))))

(assert
  (forall ((x Nat))
    (= (mul2 x Z) Z)))

(assert
  (forall ((x Nat) )
    (= (mul2 Z x) Z)))


(check-sat)