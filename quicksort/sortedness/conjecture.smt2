

(declare-datatype list (par (a) 
    (
      (Nil) 
      (Cons (head a) (tail (list a)))
    )
))


(declare-fun less (par (a) (a a) Bool))
(define-fun leq (par (a) ((x a) (y a)) Bool (not (less a y x))))
(assert (par (a) (forall ((x a)) (leq a x x))))
(assert (par (a) (forall ((x a) (y a) (z a)) (=> (and (leq a x y) (leq a y z)) (leq a x z)))))
(assert (par (a) (forall ((x a) (y a)) (=> (and (leq a x y) (leq a y x)) (= x y)))))
(assert (par (a) (forall ((x a) (y a)) (or (leq a x y) (leq a y x)))))
(define-fun-rec filter_less (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (less a y x) (Cons a y (filter_less a x ys)) (filter_less a x ys)))))))
(define-fun-rec filter_ge (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (not (less a y x)) (Cons a y (filter_ge a x ys)) (filter_ge a x ys)))))))
(define-fun-rec append (par (a) ((xs (list a)) (ys (list a))) (list a)
  (match xs (((Nil a) ys)
             ((Cons a z zs) (Cons a z (append a zs ys)))))))

; every element of the first arg is greater than or equal to second arg
(define-fun-rec list_ge_elem (par (a) ((xs (list a)) (y a)) Bool
  (match xs (((Nil a) true)
             ((Cons a z zs) (and (not (less a z y)) (list_ge_elem a zs y)))))))

(define-fun-rec sorted (par (a) ((xs (list a))) Bool
  (match xs (((Nil a) true)
             ((Cons a z zs) (and (list_ge_elem a zs z) (sorted a zs)))))))

; Definition 2 of quicksort
(define-fun-rec quicksort (par (a) ((xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
             ((Cons a z zs) (append a (quicksort a (filter_less a z zs)) (Cons a z (quicksort a (filter_ge a z zs)))))))))

; every element of the first arg is greater than or equal to every element of the second arg
(define-fun-rec list_ge_list (par (a) ((xs (list a)) (ys (list a))) Bool
  (match ys (((Nil a) true)
             ((Cons a z zs) (and (list_ge_elem a xs z) (list_ge_list a xs zs)))))))

; lemma 1
(assert
  (par (a) (forall ((x a) (xs (list a)) (ys (list a)))
  (=>
    (and
      (sorted a xs)
      (sorted a ys)
      (list_ge_elem a ys x)
      (list_ge_list a (Cons a x ys) xs)
    )
    (sorted a (append a xs (Cons a x ys)))
  )))
)

; lemma 3, assumption 4 from the exact used instance of lemma 1
(assert
  (par (a) (forall ((x a) (xs (list a)))
  (list_ge_list a (Cons a x (quicksort a (filter_ge a x xs))) (quicksort a (filter_less a x xs)))
)))

; lemma 4
(assert
  (par (a) (forall ((x a) (ys (list a)))
    (=> (list_ge_elem a ys x) (list_ge_elem a (quicksort a ys) x))
)))

; lemma 5, list_ge_list second arg is invariant under quicksort
(assert
  (par (a) (forall ((x a) (xs (list a)) (ys (list a)))
    (=>  (list_ge_list a ys xs) (list_ge_list a ys (quicksort a xs)))
)))

; lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
(assert-not (par (a) (forall ((xs (list a))) (sorted a (quicksort a xs)))))
