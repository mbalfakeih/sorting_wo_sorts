(declare-datatype list (par (a) ((Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-fun less (par (a) (a a) Bool))
(declare-fun leq (par (a) (a a) Bool))
(assert (par (a) (forall ((x a) (y a)) (= (less a x y) (and (leq a x y) (distinct x y))))))
(assert (par (a) (forall ((x a)) (leq a x x))))
(assert (par (a) (forall ((x a) (y a) (z a)) (=> (and (leq a x y) (leq a y z)) (leq a x z)))))
(assert (par (a) (forall ((x a) (y a)) (=> (and (leq a x y) (leq a y x)) (= x y)))))
(assert (par (a) (forall ((x a) (y a)) (or (leq a x y) (leq a y x)))))

(define-fun-rec insort (par (a) ((x a) (ys (list a))) (list a)
  (match ys (((Nil a) (Cons a x (Nil a)))
             ((Cons a z zs) (ite (leq a x z) (Cons a x (Cons a z zs)) (Cons a z (insort a x zs))))))))
(define-fun-rec isort (par (a) ((xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
             ((Cons a z zs) (insort a z (isort a zs)))))))

(define-fun-rec filter_mset (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (= y x) (Cons a y (filter_mset a x ys)) (filter_mset a x ys)))))))

; lemma 1
(assert
  (par (a)
    (forall ((x a) (y a) (ys (list a)))
      (=
        (filter_mset a x (Cons a y ys))
        (filter_mset a x (insort a y ys))
      )
  ))
)

; lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:sos=theory:sstl=1:sp=occurrence:indao=on_89
; mset(isort(xs)) = mset(xs)
(assert-not
  (par (a)
    (forall ((x a)(xs (list a)))
      (=
        (filter_mset a x xs)
        (filter_mset a x (isort a xs))
      )
  ))
)
