(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun op (Nat Nat Nat Nat) Nat)
(assert
  (not
    (forall ((a Nat) (b Nat) (c Nat) (d Nat) (e Nat))
      (= (op (op a b Z Z) c d e) (op a (op b c Z Z) d e)))))



(assert
  (forall ((x Nat) (y Nat) (x2 Nat))
  (= (op (S x) y Z x2) (op x y y x2))))

(assert
  (forall ((x Nat) (y Nat) (z Nat) (x2 Nat))
  (= (op (S x) y (S z) x2) (op (S x) y z (S x2)))))
 

 (assert
  (forall ((y Nat) (z Nat) (x2 Nat))
  (= (op Z y (S z) x2) (op Z y z (S x2)))))

 (assert
  (forall ((y Nat) (x2 Nat))
  (= (op Z y Z x2) x2)))

; (assert
;   (forall ((x Nat) (y Nat) (z Nat) (x2 Nat))
;     (= (op x y z x2)
;       (ite
;         (is-S x)
;         (ite 
;           (is-S z) 
;             (op (S (p x)) y (p z) (S x2)) 
;             (op (p x) y y x2))
;         (ite 
;           (is-S z) 
;             (op Z y (p z) (S x2)) 
;             x2)))))
(check-sat)
