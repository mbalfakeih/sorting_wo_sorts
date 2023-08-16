(declare-datatype nat ((zero) (s (s_0 nat))))
(declare-datatype list (par (a) ((Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-fun less (par (a) (a a) Bool))
(define-fun leq (par (a) ((x a) (y a)) Bool (not (less a y x))))
(assert (par (a) (forall ((x a)) (leq a x x))))
(assert (par (a) (forall ((x a) (y a) (z a)) (=> (and (leq a x y) (leq a y z)) (leq a x z)))))
(assert (par (a) (forall ((x a) (y a)) (=> (and (leq a x y) (leq a y x)) (= x y)))))
(assert (par (a) (forall ((x a) (y a)) (or (leq a x y) (leq a y x)))))

(define-fun-rec append (par (a) ((xs (list a)) (ys (list a))) (list a)
  (match xs (((Nil a) ys)
             ((Cons a z zs) (Cons a z (append a zs ys)))))))

; definitions needed for mergesort
(define-fun-rec len (par (a) ((xs (list a))) nat
  (match xs (((Nil a) zero)
             ((Cons a z zs) (s (len a zs)))))))
(define-fun-rec div2 ((x nat)) nat
  (match x ((zero zero)
            ((s z) (match z ((zero zero)
                             ((s n) (s (div2 n)))))))))
(define-fun-rec merge (par (a) ((xs (list a)) (ys (list a))) (list a)
  (match xs (((Nil a) ys)
             ((Cons a z zs) (match ys (((Nil a) xs)
                ((Cons a u us) (ite (leq a z u) (Cons a z (merge a zs (Cons a u us))) (Cons a u (merge a (Cons a z zs) us)))))))))))
(define-fun-rec take (par (a) ((n nat) (xs (list a))) (list a)
  (match n ((zero (Nil a))
            ((s m) (match xs (((Nil a) (Nil a))
              ((Cons a z zs) (Cons a z (take a m zs))))))))))
(define-fun-rec drop (par (a) ((n nat) (xs (list a))) (list a)
  (match n ((zero xs)
            ((s m) (match xs (((Nil a) (Nil a))
              ((Cons a z zs) (drop a m zs)))))))))
(define-fun-rec mergesort (par (a) ((xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
             ((Cons a z zs)
                (merge a (mergesort a (take a (div2 (len a xs)) xs)) (mergesort a (drop a (div2 (len a xs)) xs))))))))

(define-fun-rec filter_mset (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (= y x) (Cons a y (filter_mset a x ys)) (filter_mset a x ys)))))))

; lemma 1
(assert
  (par (a)
    (forall ((x a)(xs (list a))(ys (list a)))
      (=
        (filter_mset a x (merge a xs ys))
        (append a (filter_mset a x xs) (filter_mset a x ys))
      )
  ))
)

; lemma 2
(assert
  (par (a)
    (forall ((x a) (n nat) (xs (list a)))
      (=
        (filter_mset a x xs)
        (append a
          (filter_mset a x (take a n xs))
          (filter_mset a x (drop a n xs))
        )
      )
  ))
)

; lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
(assert-not
  (par (a)
    (forall ((x a)(xs (list a)))
      (=
        (filter_mset a x xs)
        (filter_mset a x (mergesort a xs))
      )
  ))
)
