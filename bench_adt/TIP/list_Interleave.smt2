;(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head Int) (tail list)))))
(declare-fun interleave (list list) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(assert
  (not
    (forall ((xs list)) (= (interleave (evens xs) (odds xs)) xs))))
; (assert
;   (forall ((x list) (y list))
;     (= (interleave x y)
;       (ite (is-cons x) (cons (head x) (interleave y (tail x))) y))))


(assert
  (forall ((n Int) (x list) (y list))
    (= (interleave (cons n x) y)
      (cons n (interleave y x)))))


(assert
  (forall ((y list))
    (= (interleave nil y) y)))


; (assert
;   (forall ((x list))
;     (= (evens x)
;       (ite (is-cons x) (cons (head x) (odds (tail x))) nil))))
; (assert
;   (forall ((x list))
;     (= (odds x) (ite (is-cons x) (evens (tail x)) nil))))


(assert
  (forall ((n Int) (x list))
    (= (odds (cons n x)) (evens x))))

(assert (= (odds nil) nil))


(assert
  (forall ((n Int) (x list))
    (= (evens (cons n x)) (cons n (odds x)))))

(assert (= (evens nil) nil))

(check-sat)
