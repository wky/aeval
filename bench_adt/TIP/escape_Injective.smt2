(declare-datatypes () ((Token (A) (B) (C) (D) (ESC) (P) (Q) (R))))
(declare-datatypes ()
  ((list (nil) (cons (head Token) (tail list)))))
(declare-fun isSpecial (Token) Bool)
(declare-fun code (Token) Token)
(declare-fun escape (list) list)

; (assert
;   (forall ((x Token))
;     (= (isSpecial x)
;       (ite
;         (is-R x) true
;         (ite (is-Q x) true (ite (is-P x) true (is-ESC x)))))))




(assert (isSpecial ESC))
(assert (isSpecial P))
(assert (isSpecial Q))
(assert (isSpecial R))





; (assert
;   (forall ((x Token))
;     (= (code x)
;       (ite
;         (is-R x) C
;         (ite (is-Q x) B (ite (is-P x) A (ite (is-ESC x) ESC x)))))))



(assert (= (code ESC) ESC))
(assert (= (code P) A))
(assert (= (code Q) B))
(assert (= (code R) C))
(assert (= (code A) A))
(assert (= (code B) B))
(assert (= (code C) C))
(assert (= (code D) D))


; (assert
;   (forall ((x list))
;     (= (escape x)
;       (ite
;         (is-cons x)
;         (ite
;           (isSpecial (head x))
;           (cons ESC (cons (code (head x)) (escape (tail x))))
;           (cons (head x) (escape (tail x))))
;         nil))))


(assert (= (escape nil) nil))
(assert (forall ((t Token) (l list)) 
  (= (escape (cons t l)) 
    (ite (isSpecial t) 
      (cons ESC (cons (code t) (escape l))) 
      (cons t (escape l))))))

(assert
  (not
    (forall ((xs list) (ys list))
      (=> (= (escape xs) (escape ys)) (= xs ys)))))

(check-sat)
