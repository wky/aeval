(declare-datatypes () ((Nat (Zero) (Succ (pred Nat)))))
(declare-datatypes () ((Z (P (P_0 Nat)) (N (N_0 Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Z)
(declare-fun plus2 (Z Z) Z)


; (assert
;   (forall ((x Nat) (y Nat))
;     (= (plus x y) (ite (is-Succ x) (Succ (plus (pred x) y)) y))))

(assert
  (forall ((y Nat)) 
    (= (plus Zero y) y)))
(assert
  (forall ((x Nat) (y Nat)) 
    (= (plus (Succ x) y) (Succ (plus x y)))))

; (assert
;   (forall ((x Nat) (y Nat))
;     (= (minus x y)
;       (ite
;         (is-Succ x)
;         (ite (is-Succ y) (minus (pred x) (pred y)) (P (Succ (pred x))))
;         (ite (is-Succ y) (N (pred y)) (P Zero))))))


(assert
  (forall ((x Nat)) 
    (= (minus x Zero) (P x))))


(assert
  (forall ((y Nat)) 
    (= (minus Zero y) (N y))))


(assert
  (forall ((x Nat) (y Nat)) 
    (= (minus (Succ x) (Succ y)) (minus x y))))

; (assert
;   (forall ((x Z) (y Z))
;     (= (plus2 x y)
;       (ite
;         (is-N x)
;         (ite
;           (is-N y) (N (Succ (plus (N_0 x) (N_0 y))))
;           (minus (P_0 y) (Succ (N_0 x))))
;         (ite
;           (is-N y) (minus (P_0 x) (Succ (N_0 y)))
;           (P (plus (P_0 x) (P_0 y))))))))



(assert
  (forall ((x Nat) (y Nat)) 
    (= (plus2 (P x) (P y)) (P (plus x y)))))
(assert
  (forall ((x Nat) (y Nat)) 
    (= (plus2 (P x) (N y)) (minus x y))))
(assert
  (forall ((x Nat) (y Nat)) 
    (= (plus2 (N x) (P y)) (minus y x))))
(assert
  (forall ((x Nat) (y Nat)) 
    (= (plus2 (N x) (N y)) (N (plus x y)))))



; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (P x) (plus2 (P y) (P z))) (plus2 (plus2 (P x) (P y)) (P z))))))

; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (P x) (plus2 (P y) (N z))) (plus2 (plus2 (P x) (P y)) (N z))))))

; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (P x) (plus2 (N y) (N z))) (plus2 (plus2 (P x) (N y)) (N z))))))

; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (P x) (plus2 (N y) (P z))) (plus2 (plus2 (P x) (N y)) (P z))))))


; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (N x) (plus2 (P y) (P z))) (plus2 (plus2 (N x) (P y)) (P z))))))


; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 N x) (plus2 (P y) (N z))) (plus2 (plus2 (N x) (P y)) (N z))))))

; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (N x) (plus2 (N y) (P z))) (plus2 (plus2 (N x) (N y)) (P z))))))

; (assert
;   (not
;     (forall ((x Nat) (y Nat) (z Nat))
;       (= (plus2 (N x) (plus2 (N y) (N z))) (plus2 (plus2 (N x) (N y)) (N z))))))


(check-sat)
