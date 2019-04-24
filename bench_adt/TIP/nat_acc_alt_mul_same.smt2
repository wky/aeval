(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
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


(assert (forall ((y Nat)) (= (plus Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))


(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert (forall ((x Nat) (y Nat)) (= (mult (S x) y) (plus y (mult x y)))))

(assert
  (not (forall ((x Nat) (y Nat)) (= (acc_alt_mul x y) (mult x y)))))

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
; (assert
;   (forall ((x Nat) (y Nat))
;     (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
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
