(declare-datatype nat ((zero) (s (s_0 nat))))
(declare-datatype list (par (a) ((Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))
(declare-fun less (par (a) (a a) Bool))
(define-fun leq (par (a) ((x a) (y a)) Bool (not (less a y x))))
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
                ((Cons a u us) (ite (not (less a u z)) (Cons a z (merge a zs (Cons a u us))) (Cons a u (merge a (Cons a z zs) us)))))))))))
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
             ((Cons a z zs) (ite (= zs (Nil a)) xs
                (merge a (mergesort a (take a (div2 (len a xs)) xs)) (mergesort a (drop a (div2 (len a xs)) xs)))))))))

; lemma 2
(assert
  (par (a)
    (forall ((x a) (y a) (ys (list a)))
      (=>
        (and (leq a x y) (list_ge_elem a ys y))
        (list_ge_elem a ys x)
      )
    )
  )
)

(assert-not
  (par (a) 
    (forall ((xs (list a)) (ys (list a)))
      (=>
        (and (sorted a xs) (sorted a ys))
        (sorted a (merge a xs ys))
      )
    )
  )
)

; lrs+10_1_drc=encompass:ind=struct:sik=one_plus_recursion:to=lpo:thsq=on:sp=occurrence:nui=on:indoct=on:urr=on:indmd=1_890
; (assert-not
;   (par (a)
;     ; (=>
;       (and
;         ; (forall ((x a) (xs (list a)) (y a) (ys (list a)))
;         ;   (=>
;         ;     (and (sorted a (Nil a)) (sorted a ys))
;         ;     (sorted a (merge a (Nil a) ys))
;         ;   )
;         ; )
;         ; (forall ((x a) (xs (list a)) (y a) (ys (list a)))
;         ;   (=>
;         ;     (and (sorted a (Cons a x xs)) (sorted a (Nil a)))
;         ;     (sorted a (merge a (Cons a x xs) (Nil a)))
;         ;   )
;         ; )
;         (forall ((x a) (xs (list a)) (y a) (ys (list a)))
;           (=>
;             (and
;               (=>
;                 (and (sorted a (Cons a x xs)) (sorted a ys))
;                 (sorted a (merge a (Cons a x xs) ys))
;               )
;               (=>
;                 (and (sorted a xs) (sorted a (Cons a y ys)))
;                 (sorted a (merge a xs (Cons a y ys)))
;               )
;             )
;             (=>
;               (and (sorted a (Cons a x xs)) (sorted a (Cons a y ys)))
;               (sorted a (merge a (Cons a x xs) (Cons a y ys)))
;             )
;           )
;         )
;       )
;       ; (forall ((x a) (xs (list a)) (y a) (ys (list a)))
;       ;   (=>
;       ;     (and (sorted a xs) (sorted a ys))
;       ;     (sorted a (merge a xs ys))
;       ;   )
;       ; )
;     ; )
;   )
; )
