(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun alt_mul (Nat Nat) Nat)




(assert (forall ((y Nat)) (= (plus Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))

(assert (forall ((x Nat)) (= (acc_alt_mul x Z) Z)))
(assert (forall ((y Nat)) (= (acc_alt_mul Z y) Z)))
(assert (forall ((x Nat) (y Nat)) 
  (= (acc_alt_mul (S x) (S y)) 
    (S (acc_plus x (acc_plus y 
      (acc_alt_mul x y)))))))

(assert
  (not (forall ((x Nat) (y Nat)) (= (alt_mul x y) (alt_mul y x)))))


; (assert
;   (forall ((x Nat) (y Nat))
;     (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
; (assert
;   (forall ((x Nat) (y Nat))
;     (= (alt_mul x y)
;       (ite
;         (is-S x)
;         (ite
;           (is-S y) (S (plus (plus (alt_mul (p x) (p y)) (p x)) (p y))) Z)
;         Z))))

(check-sat)
