;; 
;; Copyright (C) 2019, David Greve
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms of
;; the 3-clause BSD license.  See the ACL2 LICENSE file for details.
;; 
;;
(in-package "ACL2")
(include-book "coi/util/defun" :dir :system)

(defun invertible-modulus-p (p)
  (and (integerp p)
       (< 1 p)))

(defthm invertible-modulus-p-implies
  (implies
   (invertible-modulus-p p)
   (and (integerp p)
        (< 1 p)))
  :rule-classes (:forward-chaining))

(include-book "coi/quantification/quantified-congruence" :dir :system)

(defthm natp-nfix
  (implies
   (natp x)
   (equal (nfix x) x)))

(defun nfix-equiv (x y)
  (equal (nfix x) (nfix y)))

(defequiv nfix-equiv)

(defthm nfix-equiv-nfix
  (nfix-equiv (nfix x) x))

(defcong nfix-equiv equal (nfix x) 1)

(in-theory (disable nfix-equiv))

(in-theory (disable nfix-equiv))

(defun ifix-equiv (x y)
  (equal (ifix x) (ifix y)))

(defequiv ifix-equiv)

(defthm ifix-equiv-ifix
  (ifix-equiv (ifix x) x))

(defcong ifix-equiv equal (ifix x) 1)

(defun pfix (x)
  (declare (type t x))
  (if (posp x) x 1))

(defthm posp-pfix-identity
  (implies
   (posp x)
   (equal (pfix x) x)))

(defthm posp-pfix
  (posp (pfix x))
  :rule-classes ((:forward-chaining :trigger-terms ((pfix x)))))

(defthm posp-implies
  (implies
   (posp x)
   (and (natp x)
        (integerp x)
        (< 0 x)))
  :rule-classes (:forward-chaining))

(defun pfix-equiv (x y)
  (equal (pfix x) (pfix y)))

(defequiv pfix-equiv)

(defthm pfix-equiv-pfix
  (pfix-equiv (pfix x) x))

(defcong pfix-equiv equal (pfix x) 1)

(local
 (encapsulate
     ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm mod-1
     (implies
      (integerp x)
      (equal (mod x 1) 0)))
   
   (defthm mod-of-0
     (equal (mod 0 x) 0))
   
   (defthm times-zero
     (equal (* 0 x) 0))
   
   (defthm mod-mod
     (implies
      (and (integerp x) (integerp q))
      (equal (mod (mod x q) q)
             (mod x q))))
   
   ))

(in-theory (disable mod))

(defun generic-invertible-predicate (a x p)
  (equal (mod (* (ifix a) (ifix x)) (pfix p)) 1))

(defcong ifix-equiv equal (generic-invertible-predicate a x p) 1)
(defcong ifix-equiv equal (generic-invertible-predicate a x p) 2)
(defcong pfix-equiv equal (generic-invertible-predicate a x p) 3)

(in-theory (disable ifix-equiv pfix-equiv))

(defun-sk generic-invertible-p (x p)
  (exists (a) (generic-invertible-predicate a x p))
  :strengthen t)

(encapsulate
    ()

  (local (in-theory (disable nth generic-invertible-predicate)))

  (quant::congruence generic-invertible-p (x p)
   (exists (a) (generic-invertible-predicate a x p))
   :congruences ((x ifix-equiv)
                 (p pfix-equiv)))

  )

(defthm zero-not-invertible
  (not (generic-invertible-p 0 p)))

(defthm non-integer-not-invertible
  (implies
   (not (integerp x))
   (not (generic-invertible-p x p))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm not-invertible-one
    (not (generic-invertible-p x 1)))

  )

(defthm proving-invertibility
  (implies
   (and
    (equal (mod (* a x) p) 1)
    (integerp a)
    (integerp x)
    (posp p))
   (generic-invertible-p x p))
  :hints (("Goal" :in-theory (disable mod generic-invertible-p)
           :use generic-invertible-p-suff)))

(defun generic-inv (x p)
  (ifix (generic-invertible-p-witness x p)))

(defthm integerp-generic-inv
  (integerp (generic-inv x p))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((generic-inv x p)))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm generic-modular-inverse
    (implies
     (and
      (integerp x)
      (natp p)
      (generic-invertible-p x p))
     (equal (mod (* (generic-inv x p) x) p)
            1)))

  )

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
    (posp p)
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
                        
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm ifix-equiv-mod-zero
    (implies
     (and (not (integerp x))
          (integerp q))
     (ifix-equiv (mod x q) 0))
    :hints (("Goal" :in-theory (enable ifix-equiv))))

  
  (defthmd generic-invertible-p-mod
    (implies
     (natp q)
     (iff (generic-invertible-p (mod x q) q)
          (generic-invertible-p x q)))
    :hints (("Subgoal 2" :expand (generic-invertible-p x q)
             :cases ((integerp x))
             :use (:instance generic-invertible-p-suff
                             (a (generic-invertible-p-witness x q))
                             (x (mod x q))
                             (p q)))
            ("Subgoal 1" :expand (generic-invertible-p (mod x q) q)
             :cases ((integerp x))
             :use (:instance generic-invertible-p-suff
                             (a (generic-invertible-p-witness (mod x q) q))
                             (x x)
                             (p q)))
            ))

  )
  
(defthmd generic-invertible-p-mod-helper
  (implies
   (and
    (natp q)
    (equal y (mod x q)))
   (iff (generic-invertible-p y q)
        (generic-invertible-p x q)))
  :hints (("Goal" :in-theory nil
           :use generic-invertible-p-mod)))

(include-book "coi/nary/nary-mod" :dir :system)

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthmd generic-invertible-p-mod-congruence
    (implies
     (and
      (natp q)
      (nary::bind-context
       (equal z (mod x q))))
     (iff (generic-invertible-p x q)
          (generic-invertible-p z q)))
    :otf-flg t
    :hints (("Goal" :cases ((integerp x))
             :in-theory '(NARY::OPEN-MOD-EQUIV-IN-CONCLUSION
                          IFIX-EQUIV-IMPLIES-EQUAL-GENERIC-INVERTIBLE-PREDICATE-2
                          non-integer-not-invertible
                          INTEGERP-MOD-1
                          natp
                          mod-mod
                          ifix-equiv-mod-zero
                          )
             :use ((:instance generic-invertible-p-mod-helper
                              (x (mod x q))
                              (y (mod z q)))
                   (:instance generic-invertible-p-mod
                              (x x))
                   (:instance generic-invertible-p-mod
                              (x z))))))

  
  (defthm generic-invertible-p-negation
    (implies
     (and
      (integerp x)
      (posp q)
      (generic-invertible-p x q))
     (generic-invertible-p (- x) q))
    :hints (("Goal" :expand (generic-invertible-p x q)
             :use (:instance generic-invertible-p-suff
                             (a (- (ifix (GENERIC-INVERTIBLE-P-WITNESS X Q))))
                             (x (- x))
                             (p q)))))

  )
  
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

(def::un xgcd (k n m d)
  (declare (xargs :measure (nfix (+ (nfix n) (nfix d)))
                  :signature ((natp natp natp natp) natp natp natp natp)))
  (if (zp n) (mv k n m d)
    (if (zp d) (mv k n m d)
      (if (< n d)
          (xgcd k n (+ k m) (- d n))
        (xgcd (+ k m) (- n d) m d)))))

(def::und inv (x q)
  (declare (xargs :signature ((natp natp) integerp)))
  (mv-let (k n m d) (xgcd 1 x 0 q)
    (if (zp n) (if (equal d 1) (- k m) 0)
      (if (equal n 1) (- m k) 0))))

(encapsulate
    ()
  
  (local (include-book "arithmetic-5/top" :dir :system))
  
  (def::signature mod (integerp posp) natp)
  
  (defund invertible-p (x q)
    (declare (xargs :guard (and (integerp x) (posp q))))
    (let* ((q (pfix q))
           (x (mod (ifix x) q)))
      (equal (mod (* x (inv x q)) q) 1)))
  
  )


  
(defthm invertible-implies-generic-invertible-p
  (implies
   (invertible-p x q)
   (generic-invertible-p x q))
  :hints (("Goal" :in-theory (e/d (nary::mod-rules invertible-p) (mod))
           :use (:instance generic-invertible-p-suff
                           (p (pfix q))
                           (a (INV (MOD X (PFIX Q)) (PFIX Q))))))
  :rule-classes (:rewrite :forward-chaining))
