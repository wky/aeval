;(set-logic ALL)
(declare-datatypes () ((INT (succ (i INT)) (zero))))


(declare-fun add (INT INT) INT)
(declare-fun mult (INT INT) INT)

(assert (forall ((n INT)) (= (add n zero) n)))
(assert (forall ((n INT) (m INT)) (= (add n (succ m)) (succ (add n m)))))

(assert (forall ((n INT)) (= (mult n zero) zero)))

(assert (forall ((n INT) (m INT)) (= (mult n (succ m)) (add n (mult n m)))))



(assert (forall ((n INT)) (= (mult zero n) (mult n zero))))
;(assert (forall ((n INT)) (= (add zero n) zero)))


; add is associative lemma
(assert (forall ((x INT) (y INT) (z INT)) (= (add (add x y) z) (add x (add y z))) ))

; add is commutative lemma
(assert (forall ((x INT) (y INT)) (= (add x y) (add y x))))

(assert (not (forall ((n INT) (m INT)) (= (mult n m) (mult m n)) )))

(check-sat)


