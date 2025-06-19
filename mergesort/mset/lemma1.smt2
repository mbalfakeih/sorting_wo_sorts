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

(define-fun-rec merge (par (a) ((xs (list a)) (ys (list a))) (list a)
  (match xs (((Nil a) ys)
             ((Cons a z zs) (match ys (((Nil a) xs)
                ((Cons a u us) (ite (leq a z u) (Cons a z (merge a zs (Cons a u us))) (Cons a u (merge a (Cons a z zs) us)))))))))))

(define-fun-rec filter_mset (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (= y x) (Cons a y (filter_mset a x ys)) (filter_mset a x ys)))))))

; lemma 3
(assert
  (par (a)
    (forall ((x a) (z a)(zs (list a))(u a) (us (list a)))
      (=
        (append a (filter_mset a x zs) (filter_mset a x us))
        (append a (filter_mset a x us) (filter_mset a x zs))
      )
    )
  )
)

; ; computation induction formula
; ; the IH antecedent can be proven but if we let vampire do the induction it times out
; ; switch to assert and uncomment stuff below to use as induction formula

; Moham here: I interpret the above to result in the following assertion:

(assert-not
 ;(assert
   (par (a)
     ; (=>
       (and
         (forall ((x a) (zs (list a)))
           (=
             (filter_mset a x (merge a (Nil a) zs))
             (append a (filter_mset a x (Nil a)) (filter_mset a x zs))
           )
         )
         (forall ((x a) (z a) (zs (list a)))
           (=
             (filter_mset a x (merge a (Cons a z zs) (Nil a)))
             (append a (filter_mset a x (Cons a z zs)) (filter_mset a x (Nil a)))
           )
         )
         (forall ((x a) (z a) (zs (list a)) (u a) (us (list a)))
           (=>
             (and
               (=
                 (filter_mset a x (merge a zs (Cons a u us)))
                 (append a (filter_mset a x zs) (filter_mset a x (Cons a u us)))
               )
               (=
                 (filter_mset a x (merge a (Cons a z zs) us))
                 (append a (filter_mset a x (Cons a z zs)) (filter_mset a x us))
               )
             )
             (=
               (filter_mset a x (merge a (Cons a z zs) (Cons a u us)))
               (append a (filter_mset a x (Cons a z zs)) (filter_mset a x (Cons a u us)))
             )
           )
         )
       )
     ;   (forall ((x a) (zs (list a)) (us (list a)))
     ;     (=
     ;       (filter_mset a x (merge a zs us))
     ;       (append a (filter_mset a x zs) (filter_mset a x us))
     ;     )
     ;   )
     ; )
   )
 )

(assert-not
  (par (a)
    (forall ((x a) (z a)(zs (list a))(u a) (us (list a)))
      (=
        (filter_mset a x (merge a zs us))
        (append a (filter_mset a x zs) (filter_mset a x us))
      )
    )
  )
)
