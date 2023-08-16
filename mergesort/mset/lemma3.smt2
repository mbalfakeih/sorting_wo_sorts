(declare-datatype list (par (a) ((Nil) (Cons (Cons_0 a) (Cons_1 (list a))))))

(define-fun-rec append (par (a) ((xs (list a)) (ys (list a))) (list a)
  (match xs (((Nil a) ys)
             ((Cons a z zs) (Cons a z (append a zs ys)))))))

(define-fun-rec filter_mset (par (a) ((x a) (xs (list a))) (list a)
  (match xs (((Nil a) (Nil a))
            ((Cons a y ys) (ite (= y x) (Cons a y (filter_mset a x ys)) (filter_mset a x ys)))))))

; lrs+10_1_drc=encompass:ind=struct:sik=recursion:to=lpo:thsq=on:sp=occurrence_89
(assert-not
  (par (a)
    (forall ((x a) (z a)(zs (list a))(u a) (us (list a)))
      (=
        (append a (filter_mset a x zs) (filter_mset a x us))
        (append a (filter_mset a x us) (filter_mset a x zs))
      )
    )
  )
)
