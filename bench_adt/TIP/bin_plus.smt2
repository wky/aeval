(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Bin (One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(declare-fun s (Bin) Bin)
(declare-fun plus2 (Nat Nat) Nat)
(declare-fun toNat (Bin) Nat)
(declare-fun plus (Bin Bin) Bin)

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
;     (= (plus2 x y) (ite (is-S x) (S (plus2 (p x) y)) y))))

(assert (forall ((y Nat)) (= (plus2 Z y) y)))
(assert (forall ((x Nat) (y Nat)) (= (plus2 (S x) y) (S (plus2 x y)))))

; (assert
;   (forall ((x Bin))
;     (= (toNat x)
;       (ite
;         (is-OneAnd x) (S (plus2 (toNat (OneAnd_0 x)) (toNat (OneAnd_0 x))))
;         (ite
;           (is-ZeroAnd x) (plus2 (toNat (ZeroAnd_0 x)) (toNat (ZeroAnd_0 x)))
;           (S Z))))))

(assert (= (toNat One) (S Z)))
(assert (forall ((x Bin)) (= (toNat (OneAnd x)) (S (plus2 (toNat x) (toNat x))))))
(assert (forall ((x Bin)) (= (toNat (ZeroAnd x)) (plus2 (toNat x) (toNat x)))))

; (assert
;   (forall ((x Bin) (y Bin))
;     (= (plus x y)
;       (ite
;         (is-OneAnd x)
;         (ite
;           (is-OneAnd y) (ZeroAnd (s (plus (OneAnd_0 x) (OneAnd_0 y))))
;           (ite
;             (is-ZeroAnd y) (OneAnd (plus (OneAnd_0 x) (ZeroAnd_0 y)))
;             (s (OneAnd (OneAnd_0 x)))))
;         (ite
;           (is-ZeroAnd x)
;           (ite
;             (is-OneAnd y) (OneAnd (plus (ZeroAnd_0 x) (OneAnd_0 y)))
;             (ite
;               (is-ZeroAnd y) (ZeroAnd (plus (ZeroAnd_0 x) (ZeroAnd_0 y)))
;               (s (ZeroAnd (ZeroAnd_0 x)))))
;           (s y))))))

(assert
  (forall ((y Bin))
    (= (plus One y) (s y))))

(assert
  (forall ((x Bin))
    (= (plus x One) (s x))))

(assert
  (forall ((x Bin) (y Bin))
    (= (plus (ZeroAnd x) (ZeroAnd y)) (ZeroAnd (plus x y)))))

(assert
  (forall ((x Bin) (y Bin))
    (= (plus (ZeroAnd x) (OneAnd y)) (OneAnd (plus x y)))))

(assert
  (forall ((x Bin) (y Bin))
    (= (plus (OneAnd x) (ZeroAnd y)) (OneAnd (plus x y)))))

(assert
  (forall ((x Bin) (y Bin))
    (= (plus (OneAnd x) (OneAnd y)) (ZeroAnd (s (plus x y))))))


(assert
  (not
    (forall ((x Bin) (y Bin))
      (= (toNat (plus x y)) (plus2 (toNat x) (toNat y))))))

(check-sat)
