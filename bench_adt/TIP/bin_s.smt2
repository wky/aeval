(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Bin (One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(declare-fun s (Bin) Bin)
(declare-fun plus (Nat Nat) Nat)
(declare-fun toNat (Bin) Nat)


; (assert
;   (forall ((x Bin))
;     (= (s x)
;       (ite
;         (is-OneAnd x) (ZeroAnd (s (OneAnd_0 x)))
;         (ite (is-ZeroAnd x) (OneAnd (ZeroAnd_0 x)) (ZeroAnd One))))))


(assert (= (s One) (ZeroAnd One)))
(assert
  (forall ((x Bin))
    (= (s (OneAnd x)) (ZeroAnd (s x)))))
(assert
  (forall ((x Bin))
    (= (s (ZeroAnd x)) (OneAnd x))))


; (assert
;   (forall ((x Nat) (y Nat))
;     (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))

(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus (S x) y) (S (plus x y)))))

; (assert
;   (forall ((x Bin))
;     (= (toNat x)
;       (ite
;         (is-OneAnd x) (S (plus (toNat (OneAnd_0 x)) (toNat (OneAnd_0 x))))
;         (ite
;           (is-ZeroAnd x) (plus (toNat (ZeroAnd_0 x)) (toNat (ZeroAnd_0 x)))
;           (S Z))))))

(assert (= (toNat One) (S Z)))
(assert (forall ((x Bin)) (= (toNat (OneAnd x)) (S (plus (toNat x) (toNat x))))))
(assert (forall ((x Bin)) (= (toNat (ZeroAnd x)) (plus (toNat x) (toNat x)))))



(assert (not (forall ((n Bin)) (= (toNat (s n)) (S (toNat n))))))

(check-sat)
