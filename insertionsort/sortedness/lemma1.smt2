(declare-datatype list (par (a) ((Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-fun in_set (par (a) (a (list a)) Bool))
(assert (par (a) (forall ((x a)) (not (in_set a x (Nil a))))))
(assert (par (a) (forall ((x a) (y a) (ys (list a))) (= (in_set a x (Cons a y ys)) (or (= x y) (in_set a x ys))))))
(declare-fun less (par (a) (a a) Bool))
(declare-fun leq (par (a) (a a) Bool))
(assert (par (a) (forall ((x a) (y a)) (= (less a x y) (and (leq a x y) (distinct x y))))))
(assert (par (a) (forall ((x a)) (leq a x x))))
(assert (par (a) (forall ((x a) (y a) (z a)) (=> (and (leq a x y) (leq a y z)) (leq a x z)))))
(assert (par (a) (forall ((x a) (y a)) (=> (and (leq a x y) (leq a y x)) (= x y)))))
(assert (par (a) (forall ((x a) (y a)) (or (leq a x y) (leq a y x)))))

; every element of the first arg is greater than or equal to second arg
(define-fun-rec list_ge_elem (par (a) ((xs (list a)) (y a)) Bool
  (match xs (((Nil a) true)
             ((Cons a z zs) (and (not (less a z y)) (list_ge_elem a zs y)))))))

(define-fun-rec sorted (par (a) ((xs (list a))) Bool
  (match xs (((Nil a) true)
             ((Cons a z zs) (and (list_ge_elem a zs z) (sorted a zs)))))))

(define-fun-rec insort (par (a) ((x a) (ys (list a))) (list a)
  (match ys (((Nil a) (Cons a x (Nil a)))
             ((Cons a z zs) (ite (leq a x z) (Cons a x (Cons a z zs)) (Cons a z (insort a x zs))))))))
(define-fun-rec isort (par (a) ((xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
             ((Cons a z zs) (insort a z (isort a zs)))))))

; lrs+1002_1_aac=none:anc=all:sac=on:ind=struct:thsq=on:to=lpo:nui=on:drc=encompass:sik=recursion:urr=on_89
; lemma 1
(assert-not
  (par (a) (forall ((x a) (xs (list a)))
    (=>
      (sorted a xs)
      (sorted a (insort a x xs))
    )
  ))
)
