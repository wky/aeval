(declare-datatypes ()
  ((Bin (One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(declare-fun s (Bin) Bin)
(declare-fun plus (Bin Bin) Bin)
(declare-fun times (Bin Bin) Bin)

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


; (assert
;   (forall ((x Bin) (y Bin))
;     (= (times x y)
;       (ite
;         (is-OneAnd x) (plus (ZeroAnd (times (OneAnd_0 x) y)) y)
;         (ite (is-ZeroAnd x) (ZeroAnd (times (ZeroAnd_0 x) y)) y)))))

(assert
  (forall ((x Bin) (y Bin))
    (= (times (OneAnd x)  y) (plus (ZeroAnd (times x y)) y))))

(assert
  (forall ((x Bin) (y Bin))
    (= (times (ZeroAnd x)  y) (plus (ZeroAnd (times x y)) y))))

(assert
  (forall ((y Bin))
    (= (times One y) y)))



(assert
  (not
    (forall ((x Bin) (y Bin) (z Bin))
      (= (times x (plus y z)) (plus (times x y) (times x z))))))
(check-sat)
