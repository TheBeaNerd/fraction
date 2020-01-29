;; 
;; Copyright (C) 2019, David Greve
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms of
;; the 3-clause BSD license.  See the ACL2 LICENSE file for details.
;; 
;;
(in-package "ACL2")

(defun invertible-modulus-p (p)
  (and (integerp p)
       (< 1 p)))

(defthm invertible-modulus-p-implies
  (implies
   (invertible-modulus-p p)
   (and (integerp p)
        (< 1 p)))
  :rule-classes (:forward-chaining))

(defun-sk generic-invertible-p (x p)
  (exists (a) (equal (mod (* (ifix a) (ifix x)) (nfix p)) 1)))

(defthm proving-invertibility
  (implies
   (and
    (equal (mod (* a x) p) 1)
    (integerp a)
    (integerp x)
    (natp p))
   (generic-invertible-p x p))
  :hints (("Goal" :in-theory (disable mod generic-invertible-p)
           :use generic-invertible-p-suff)))

(defun generic-inv (x p)
  (ifix (generic-invertible-p-witness x p)))

(defthm integerp-generic-inv
  (integerp (generic-inv x p))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((generic-inv x p)))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm generic-modular-inverse
  (implies
   (and
    (integerp x)
    (natp p)
    (generic-invertible-p x p))
   (equal (mod (* (generic-inv x p) x) p)
          1)))

(encapsulate
    ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm invertible-modulus-p-mod-1
    (implies
     (invertible-modulus-p p)
     (equal (mod 1 p) 1)))
  )

(defthm generic-invertible-p-implies-invertible-modulus-p
  (implies
   (and
    (generic-invertible-p x p)
    (posp p)
    (integerp x))
   (invertible-modulus-p p))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes (:forward-chaining))

(defthm generic-invertible-inverse
  (implies
   (and
    (integerp x)
    (natp p)
    (generic-invertible-p x p))
   (generic-invertible-p (generic-inv x p) p))
  :hints (("Goal" :in-theory (disable mod generic-invertible-p)
           :expand (generic-invertible-p x p)
           :use (:instance generic-invertible-p-suff
                           (x (generic-inv x p))
                           (a x)))))

(defthm generic-invertible-p-witnesses
  (implies
   (invertible-modulus-p p)
   (and (generic-invertible-p  1 p)
        (generic-invertible-p -1 p)))
  :hints (("Goal" :in-theory (disable generic-invertible-p)
           :use ((:instance generic-invertible-p-suff
                            (a 1)
                            (x 1))
                 (:instance generic-invertible-p-suff
                            (a -1)
                            (x -1))))))

(in-theory (disable generic-invertible-p))
(in-theory (disable generic-inv))
                        
(defthmd generic-invertible-p-mod
  (implies
   (and
    (integerp x)
    (natp q))
   (iff (generic-invertible-p (mod x q) q)
        (generic-invertible-p x q)))
  :hints (("Subgoal 2" :expand (generic-invertible-p x q)
           :use (:instance generic-invertible-p-suff
                           (a (generic-invertible-p-witness x q))
                           (x (mod x q))
                           (p q)))
          ("Subgoal 1" :expand (generic-invertible-p (mod x q) q)
           :use (:instance generic-invertible-p-suff
                           (a (generic-invertible-p-witness (mod x q) q))
                           (x x)
                           (p q)))
          ))


(defthm generic-invertible-p-negation
  (implies
   (and
    (integerp x)
    (natp q)
    (generic-invertible-p x q))
   (generic-invertible-p (- x) q))
  :hints (("Goal" :expand (generic-invertible-p x q)
           :use (:instance generic-invertible-p-suff
                           (a (- (ifix (GENERIC-INVERTIBLE-P-WITNESS X Q))))
                           (x (- x))
                           (p q)))))

#+joe
(encapsulate
     (
      ((generic-invertible-p * *) => *)
      ((generic-inv * *) => *)
      )
   
   (local (defun generic-invertible-p (x p)
            ;;(declare (ignore x p))
            (and (integerp p)
                 (< 1 p)
                 (or (equal (mod x p) 1)
                     (equal (mod x p) (- p 1))))))
   
   (local (defun generic-inv (x p)
            ;;(declare (ignore x p))            
            (if (equal (mod x p) 1) 1 -1)))

   ;; ;; I might add these 3 properties here for now.
   ;; ;; We might be able to prove them ..
   ;; (defthm generic-invertible-p-product
   ;;   (implies
   ;;    (and
   ;;     (generic-invertible-p a p)
   ;;     (generic-invertible-p x p))
   ;;    (generic-invertible-p (* a x) p)))
   
   ;; ;; Can we prove this?
   ;; (defthm generic-invertible-p-congruence
   ;;   (equal (generic-invertible-p (mod x p) p)
   ;;          (generic-invertible-p x p)))

   ;; ;; Can we prove this?
   ;; (defthm generic-inv-congruence
   ;;   (equal (generic-inv (mod x p) p)
   ;;          (generic-inv x p)))

   (defthm integerp-generic-inv
     (integerp (generic-inv x p))
     :rule-classes (:rewrite
                    (:forward-chaining :trigger-terms ((generic-inv x p)))))
   
   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm generic-modular-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (generic-invertible-p x p))
      (equal (mod (* (generic-inv x p) x) p)
             1)))

   (local
    (defthm mod-is-zero
      (implies
       (and
        (integerp x)
        (natp p)
        (integerp (* (/ p) x)))
       (equal (mod x p) 0))
      :hints (("Goal" :in-theory (enable mod)))))

   (defthm generic-invertible-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (generic-invertible-p x p))
      (generic-invertible-p (generic-inv x p) p)))

   (defthm generic-invertible-p-witnesses
     (implies
      (invertible-modulus-p p)
      (and (generic-invertible-p  1 p)
           (generic-invertible-p -1 p))))

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
     :hints (("Goal" :in-theory '(inv-product-assoc integerp-generic-inv)
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

(defthm generic-invertible-p-is-not-zero
  (implies
   (and
    (generic-invertible-p x q)
    (natp q))
   (not (equal x 0)))
  :hints (("Goal" :use (:instance generic-modular-inverse
                                  (p q))
           :in-theory (disable generic-modular-inverse)))
  :rule-classes (:forward-chaining))
