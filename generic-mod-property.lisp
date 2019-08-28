(in-package "ACL2")

(encapsulate
     (
      ((generic-invertible-p * *) => *)
      ((generic-inv * *) => *)
      )
   
   (local (defun generic-invertible-p (x p)
            (declare (ignore x p))
            nil))
   
   (local (defun generic-inv (x p)
            (declare (ignore x p))            
            0))

   (defthm generic-integerp-inv
     (integerp (generic-inv x p)))
   
   (defthm generic-modular-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (generic-invertible-p x p))
      (equal (mod (* (generic-inv x p) x) p)
             (mod 1 p))))
   
   (defthm generic-invertible-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (generic-invertible-p x p))
      (generic-invertible-p (generic-inv x p) p)))

   )

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (local (include-book "arithmetic-5/lib/floor-mod/top" :dir :system))

     (defthmd equal-mod-product-reduction-1
       (implies
        (and
         (integerp x)
         (integerp a)
         (integerp b)
         (natp p)
         (equal (mod a p) (mod b p)))
        (equal (mod (* x a) p) (mod (* x b) p))))

     (defthm sigh
       (implies
        (and
         (integerp x)
         (integerp y))
        (integerp (* x y))))
     
     (defthm inv-product-assoc
       (implies
        (and
         (integerp a)
         (integerp x)
         (natp p)
         (generic-invertible-p x p))
        (equal (mod (* (generic-inv x p) x a) p)
               (mod a p)))
       :otf-flg t
       :hints (("Goal" :in-theory '(generic-modular-inverse)
                :use (:instance equal-mod-product-reduction-1
                                (a (* (generic-inv x p) x))
                                (x a)
                                (b 1)))
               (and stable-under-simplificationp
                    '(:in-theory (current-theory :here)))
               ))

     ))

  (local
   (defthmd equal-mod-product-reduction-2
     (implies
      (and
       (integerp x)
       (integerp a)
       (integerp b)
       (generic-invertible-p x p)
       (natp p)
       (equal (mod (* x a) p) (mod (* x b) p)))
      (equal (mod a p) (mod b p)))
     :hints (("Goal" :in-theory '(inv-product-assoc generic-integerp-inv)
              :use (:instance equal-mod-product-reduction-1
                              (a (* x a))
                              (b (* x b))
                              (x (generic-inv x p)))))))

  (defthm generic-equal-mod-product-reduction
    (implies
     (and
      (integerp x)
      (integerp a)
      (integerp b)
      (generic-invertible-p x p)
      (natp p))
     (equal (equal (mod (* a x) p) (mod (* b x) p))
            (equal (mod a p) (mod b p))))
    :hints (("Goal" :in-theory (disable mod)
             :use (equal-mod-product-reduction-2
                   equal-mod-product-reduction-1))))
   
  )
