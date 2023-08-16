(declare-datatype nat ((zero) (s (s_0 nat))))
(declare-datatype list (par (a) ((Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))

(define-fun-rec append (par (a) ((xs (list a)) (ys (list a))) (list a)
  (match xs (((Nil a) ys)
             ((Cons a z zs) (Cons a z (append a zs ys)))))))

(define-fun-rec evens (par (a) ((xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
             ((Cons a z zs) (match zs
                (((Nil a) (Nil a))
                 ((Cons a u us) (Cons a u (evens a us))))))))))
(define-fun-rec odds (par (a) ((xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
             ((Cons a z zs) (match zs
                (((Nil a) (Cons a z (Nil a)))
                 ((Cons a u us) (Cons a z (evens a us))))))))))


(define-fun-rec len (par (a) ((xs (list a))) nat
  (match xs (((Nil a) zero)
             ((Cons a z zs) (s (len a zs)))))))
(define-fun-rec div2 ((x nat)) nat
  (match x ((zero zero)
            ((s z) (match z ((zero zero)
                             ((s n) (s (div2 n)))))))))
(define-fun-rec take (par (a) ((n nat) (xs (list a))) (list a)
  (match n ((zero (Nil a))
            ((s m) (match xs (((Nil a) (Nil a))
              ((Cons a z zs) (Cons a z (take a m zs))))))))))
(define-fun-rec drop (par (a) ((n nat) (xs (list a))) (list a)
  (match n ((zero xs)
            ((s m) (match xs (((Nil a) (Nil a))
              ((Cons a z zs) (drop a m zs)))))))))
(define-fun-rec filter_mset (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (= y x) (Cons a y (filter_mset a x ys)) (filter_mset a x ys)))))))

; lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
; lemma 2
(assert-not
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
