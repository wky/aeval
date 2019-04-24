(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun acc_plus (Nat Nat) Nat)
(declare-fun acc_alt_mul (Nat Nat) Nat)


(assert (forall ((y Nat)) (= (acc_plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (acc_plus (S x) y) (acc_plus x (S y)))))

(assert (forall ((x Nat)) (= (acc_alt_mul x Z) Z)))
(assert (forall ((y Nat)) (= (acc_alt_mul Z y) Z)))
(assert (forall ((x Nat) (y Nat)) 
  (= (acc_alt_mul (S x) (S y)) 
    (S (acc_plus x (acc_plus y 
      (acc_alt_mul x y)))))))

(assert
  (not
    (forall ((x Nat) (y Nat))
      (= (acc_alt_mul x y) (acc_alt_mul y x)))))
; (assert
;   (forall ((x Nat) (y Nat))
;     (= (acc_plus x y) (ite (is-S x) (acc_plus (p x) (S y)) y))))
; (assert
;   (forall ((x Nat) (y Nat))
;     (= (acc_alt_mul x y)
;       (ite
;         (is-S x)
;         (ite
;           (is-S y)
;           (S (acc_plus (p x) (acc_plus (p y) (acc_alt_mul (p x) (p y))))) Z)
;         Z))))
(check-sat)
