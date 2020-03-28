(in-package "ACL2")

(include-book "generic-mod-property")

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun ndiv (n d)
    (if (not (and (natp n) (posp d))) 0
      (if (< n d) 0
        (1+ (ndiv (- n d) d)))))
    
  (defthm natp-ndiv
    (natp (ndiv n d))
    :rule-classes ((:forward-chaining :trigger-terms ((ndiv n d)))))

  (local
   (encapsulate
       ()
     
     (defun nmod (x y)
       (mod x y))
     
     (defthm open-nmod
       (implies
        (and (natp x) (posp m) (<= m x))
        (equal (nmod x m)
               (if (equal x m) 0
                 (if (< x m) x
                   (nmod (- x m) m))))))
     
     (defthm alt-nmod
       (implies
        (and (natp x) (posp m) (< x m))
        (equal (nmod x m) x)))

     (local (in-theory (disable nmod)))
     
     (defthm nmod-as-ndiv
       (implies
        (and
         (natp n)
         (posp d))
        (equal (nmod n d) (- n (* (ndiv n d) d))))
       :hints (("Goal" :induct (ndiv n d))))
     
     ))
     
  (defthmd mod-as-ndiv
    (implies
     (and
      (natp n)
      (posp d))
     (equal (mod n d) (- n (* (ndiv n d) d))))
    :hints (("Goal" :use nmod-as-ndiv)))

  )

#+joe
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthmd some-reduction
    (implies
     (and (posp k) (natp x) 
          (equal (mod (* k x) (* 2 k)) k))
     (equal (+ 1 (* 2 (ndiv (* k x) (* 2 k)))) x))
    :hints (("Goal" :use ((:instance mod-as-ndiv
                                     (n (* k x))
                                     (d (* 2 k)))))))

  (defthmd special-mod-reduction-helper
    (implies
     (and (posp k) (natp x))
     (iff (equal (mod (* k x) (* 2 k)) k)
          (equal x (+ 1 (* 2 (ndiv (* k x) (* 2 k)))))))
    :hints (("Goal" :use (some-reduction))))

  (defthmd special-mod-reduction
    (implies
     (and (posp k) (natp x))
     (iff (equal (mod (* k x) (* 2 k)) k)
          (hide (rewrite-equiv (equal x (+ 1 (* 2 (ndiv (* k (hide x)) (* 2 k)))))))))
    :hints (("Goal" :in-theory '(rewrite-equiv)
             :expand (:free (x) (hide x))
             :use special-mod-reduction-helper)))

  (defthm fred
    (implies
     (and (posp k) (natp x)
          (equal (mod (* k x) (* 2 k)) k))
     (equal (mod x 2) 1))
    :hints (("Goal" :use special-mod-reduction)))
     
  
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()

     (defun integer-quotient (x y)
       (ifix (/ x y)))
     
     (defthm integerp-integer-quotient
       (integerp (integer-quotient x y))
       :rule-classes ((:forward-chaining :trigger-terms ((integer-quotient x y)))))
     
     (defthmd natp-integer-quotient
       (implies
        (and
         (force (natp x))
         (force (natp y)))
        (<= 0 (integer-quotient x y)))
       :hints (("Goal" :in-theory (enable ifix))))
     
     (defthm integerp-quotient-implies-product
       (implies
        (and
         (integerp x)
         (integerp y)
         (not (equal y 0))
         (integerp (* x (/ y))))
        (equal (* (integer-quotient x y) y) x)))
     
     (in-theory (disable integer-quotient))
     
     (defthm integer-quotient-implication
       (implies
        (and
         (integerp x)
         (integerp y)
         (not (equal y 0))
         (integerp (* x (/ y))))
        (equal (mod x y) 0)))
     
     (defthm divisibility-property
       (implies
        (and
         (integerp q)
         (integerp x)
         (not (equal x 0))
         (integerp (* q (/ x))))
        (equal (mod (* (integer-quotient q x) x) q) (mod (* 0 x) q)))
       :hints (("Goal" :use (:instance integerp-quotient-implies-product
                                       (x q)
                                       (y x))))
       :rule-classes nil)
     
     (defthm integer-quotient-less-than
       (implies
        (and
         (posp q)
         (posp x))
        (or (< (integer-quotient q x) q)
            (equal x 1)))
       :hints (("Goal" :in-theory (enable ifix integer-quotient))))
     
     (defthm mod-less-than
       (implies
        (and
         (natp x)
         (natp q)
         (< x q))
        (equal (mod x q) x)))

     ))
     
  (defthmd generic-invertible-p-implication-1
    (implies
     (and
      (generic-invertible-p x q)
      (integerp (* q (/ x)))
      (posp q)
      (natp x))
     (equal x 1))
    :hints (("Goal" :use (divisibility-property
                          generic-invertible-p-is-not-zero
                          integer-quotient-less-than)
             :in-theory '(natp 
                          posp
                          integerp-integer-quotient
                          generic-equal-mod-product-reduction))
            (and stable-under-simplificationp
                 `(:in-theory '((force)
                                natp
                                posp 
                                mod-less-than
                                natp-integer-quotient
                                integerp-integer-quotient)))
            (and stable-under-simplificationp
                 '(:in-theory (enable integer-quotient))))
    :rule-classes :forward-chaining)

  )

(defun posfix (x)
  (if (posp x) x 1))

(defun smod (v p)
  (let ((v (ifix v))
        (p (posfix p)))
    (let ((x (mod v p)))
      (if (<= (* 2 x) p) x
        (- x p)))))

(defthm integerp-smod
  (integerp (smod v p))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((smod v p)))))

(defun sign (x)
  (if (equal (ifix x) 0) 0
    (if (< (ifix x) 0) -1 1)))
  
(defun msign (v p)
  (sign (smod v p)))

(defun mabs (v p)
  (abs (smod v p)))

(defun non-trivial-modulus (p)
  (and (integerp p)
       (< 2 p)))

(defthm implies-non-trivial-modulus
  (implies
   (and
    (< 2 p)
    (integerp p))
   (non-trivial-modulus p))
  :rule-classes (:forward-chaining))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm equal-smod-zero-mod
     (implies
      (and
       (integerp k)
       (integerp x)
       (generic-invertible-p x q)
       (posp q))
      (iff (equal (smod (* k x) q) (smod (* 0 x) q))
           (equal (mod k q) (mod 0 q))))
     :hints (("Goal" :in-theory (enable posfix smod)
              :use (:instance generic-equal-mod-product-reduction
                              (x x)
                              (a k)
                              (b 0)
                              (p q)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (posfix smod) (mod)))))))

  (defthmd equal-smod-zero-x
    (implies
     (and
      (integerp k)
      (integerp x)
      (generic-invertible-p x q)
      (posp q))
     (iff (equal (smod (* k x) q) 0)
          (equal (mod k q) 0)))
    :hints (("Goal" :in-theory (enable smod mod)
             :use equal-smod-zero-mod)))

  )

#+joe
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm equal-times-one-a
    (implies
     (and
      (integerp a)
      (integerp q)
      (integerp x)
      (equal (mod x q) 1))
     (equal (mod (* a x) q) (mod a q))))

  (defun equiv (x y)
    (equal x y))
  
  (defthmd introduce-product
    (implies
     (and
      (integerp x)
      (integerp a)
      (integerp b)
      (natp q)
      (equiv a b))
      ;;(generic-invertible-p x q))
     (equiv (mod (* a x) m)
            (mod (* b x) m))))

  (defthm remove-times-mod-1
    (implies
     (and (integerp a) (integerp a) (integerp x) (integerp q))
     (equal (mod (* (mod a q) x) q)
            (mod (* a x) q))))

  (defthm swap-assoc
    (equal (mod (* (* a x) y) q)
           (mod (* a (* x y)) q)))

  (defthmd remove-times-mod-2
    (implies
     (and (integerp a) (integerp a) (integerp x) (integerp q))
     (equal (mod (* a (mod x q)) q)
            (mod (* a x) q))))
  
  (defthmd generic-fred
    (implies
     (and (integerp a) (integerp x) (natp q) (generic-invertible-p x q))
     (equal (mod (* a (mod (* (generic-inv x q) x) q)) q)
            (mod a q)))
    :hints (("Goal" :in-theory `(generic-modular-inverse))
            (and stable-under-simplificationp
                 '(:in-theory (current-theory :here)))))

  (defthm generic-fred-1
    (implies
     (and (integerp a) (integerp x) (natp q) (generic-invertible-p x q))
     (equal (mod (* a x (generic-inv x q)) q)
            (mod a q)))
    :hints (("Goal" :in-theory '(INTEGERP-MOD-1
                                 remove-times-mod-2
                                 natp
                                 INTEGERP-GENERIC-INV)
             :use generic-fred)
            (and stable-under-simplificationp
                 '(:in-theory (current-theory :here)))
            ))
      
  (defthm equal-mod-product-reduction
    (implies
     (and
      (integerp x)
      (integerp a)
      (natp q)
      (generic-invertible-p x q)
      (equiv (mod (* a x) q) (mod a q)))
     (equal (mod (* a (generic-inv x q)) q) (mod a q)))
    :otf-flg t
    :hints (("Goal" :do-not-induct t
             :in-theory '(swap-assoc
                          remove-times-mod-1
                          natp
                          INTEGERP-MOD-1
                          INTEGERP-GENERIC-INV)
             :use (:instance introduce-product
                             (a (mod (* a x) q))
                             (b (mod a q))
                             (x (generic-inv x q))
                             (m q)))
            (and stable-under-simplificationp
                 '(:in-theory (current-theory :here)))))
  
  (defthm equal-times-zero-zero
    (implies
     (and
      (integerp a)
      (integerp q)
      (integerp x)
      (equal (mod a q) 0))
     (equal (mod (* a x) q) 0)))
  
  (defun nat-induction (n)
    (if (zp n) n
      (nat-induction (1- n))))
  
  (defthm equal-mod-product-reduction
    (implies
     (and
      (natp a)
      (integerp x)
      (< a q)
      (posp q))
     (iff (equal (mod (* a x) q) (mod a q))
          (or (equal (mod a q) 0)
              (equal (mod x q) 1))))
    :hints (("Goal" :induct (nat-induction a))))
  
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (local
   (encapsulate
       ()

     (defun mul (x y)
       (* x y))
     
     (defthm inner-product-to-mul
       (implies
        (and
         (integerp a)
         (integerp x)
         (integerp k)
         (posp m)
         )
        (equal (smod (* a (smod (* k x) m)) m)
               (smod (* (mul a k) x) m))))
     
     (defthmd simple-congruence
       (implies
        (equal x y)
        (equal (smod x m) (smod y m))))
     
     (defthm integerp-mul
       (implies
        (and (integerp x) (integerp y))
        (integerp (mul x y)))
       :rule-classes ((:forward-chaining :trigger-terms ((mul x y)))))
     
     (in-theory (disable mul))
     
     (defthm equal-product-zero-reduction
       (implies
        (and
         (posp q)
         (integerp a)
         (integerp k)
         (integerp x)
         (generic-invertible-p x q))
        (iff (equal (mod (* a k x) q) 0)
             (equal (mod (* a k) q) 0)))
       :hints (("Goal" :in-theory (disable  equal-smod-zero-x)
                :use (:instance equal-smod-zero-x
                                (k (* a k))))))
     
     (defthmd equal-q-implication-1
       (implies
        (and
         (generic-invertible-p x q)
         (integerp k)
         (integerp x)
         (integerp a)
         (non-trivial-modulus q)
         (equal (* a (smod (* k x) q)) q))
        (equal (mod (* a k) q) 0))
       :otf-flg t
       :hints (("Goal" :use (:instance simple-congruence
                                       (x (* a (smod (* k x) q)))
                                       (y q)
                                       (m q)))))
     
     (defthmd equal-q-implication-2
       (implies
        (and
         (integerp a)
         (integerp b)
         (integerp q)
         (< 0 q)
         (equal (* a b) q))
        (iff (< a 0) (< b 0))))

     (defthmd equal-q-implication
       (implies
        (and
         (generic-invertible-p x q)
         (integerp k)
         (integerp x)
         (integerp a)
         (non-trivial-modulus q)
         (equal (* a (smod (* k x) q)) q))
        (and
         (equal (mod (* a k) q) 0)
         (iff (< a 0) (< (smod (* k x) q) 0))))
       :hints (("Goal" :use ((:instance equal-q-implication-2
                                        (b (smod (* k x) q)))
                             equal-q-implication-1))))
     
     ))

  (defthm not-negative-half
    (implies
     (and
      (generic-invertible-p x q)
      (integerp x)
      (integerp k)
      (non-trivial-modulus q)
      (<= k q))
     (not (equal (* -2 (smod (* k x) q)) q)))
    :hints (("Goal" :use (:instance equal-q-implication
                                    (a -2)))))

  ;; (local
  ;;  (encapsulate
  ;;      ()
     
     ;; (defthmd half-smod-implies-1
     ;;   (implies
     ;;    (and
     ;;     (generic-invertible-p x q)
     ;;     (integerp x)
     ;;     (natp k)
     ;;     (non-trivial-modulus q)
     ;;     (<= k q)
     ;;     (equal (* 2 (smod (* k x) q)) q))
     ;;    (equal (mod (* 2 k) q) 0))
     ;;   :otf-flg t
     ;;   :hints (("Goal" :use (:instance equal-q-implication
     ;;                                   (a 2)))))

  ;;    (defthmd open-mod
  ;;      (implies
  ;;       (and
  ;;        (natp x) (posp m))
  ;;       (equal (mod x m)
  ;;              (if (equal x m) 0
  ;;                (if (< x m) x
  ;;                  (mod (- x m) m))))))
     
  ;;    (defthmd half-implies-2
  ;;      (implies
  ;;       (and
  ;;        (natp k)
  ;;        (non-trivial-modulus q)
  ;;        (<= k q)
  ;;        (equal (mod (* 2 k) q) 0))
  ;;       (or (equal k 0)
  ;;           (equal k q)
  ;;           (equal (* 2 k) q)))
  ;;      :hints (("Goal" :use (:instance open-mod
  ;;                                      (x (* 2 k))
  ;;                                      (m q)))))

  ;;    (defthmd half-implies-3
  ;;      (implies
  ;;       (and
  ;;        (natp k)
  ;;        (non-trivial-modulus q)
  ;;        (<= k q)
  ;;        (or (equal k 0)
  ;;            (equal k q)
  ;;            (equal (* 2 k) q)))
  ;;       (equal (smod (* 2 k) q) 0)))

  ;;    (defthm half-smod-equals
  ;;      (implies
  ;;       (and
  ;;        (natp k)
  ;;        (non-trivial-modulus q)
  ;;        (<= k q))
  ;;       (iff (equal (mod (* 2 k) q) 0)
  ;;            (or (equal k 0)
  ;;                (equal k q)
  ;;                (equal (* 2 k) q))))
  ;;      :hints (("Goal" :in-theory nil
  ;;               :use (half-implies-2
  ;;                     half-implies-3))
  ;;              (and stable-under-simplificationp
  ;;                   '(:in-theory (current-theory :here)))))
                 
  ;;    ))

  ;; ;; It may be that this is irrelevant ..
  ;; (defthmd half-smod-implies-1a
  ;;   (implies
  ;;    (and
  ;;     (generic-invertible-p x q)
  ;;     (integerp x)
  ;;     (natp k)
  ;;     (non-trivial-modulus q)
  ;;     (<= k q)
  ;;     (equal (* 2 (smod (* k x) q)) q))
  ;;    (equal (* 2 k) q))
  ;;   :hints (("Goal" :use (half-smod-implies-1))))

  ;; (defthmd half-smod-implies-1b
  ;;   (implies
  ;;    (and
  ;;     (generic-invertible-p x q)
  ;;     (integerp x)
  ;;     (natp k)
  ;;     (non-trivial-modulus q)
  ;;     (<= k q)
  ;;     (equal (* 2 (smod (* k x) q)) q))
  ;;    (equal (smod (* k x) q) k))
  ;;   :hints (("Goal" :in-theory (disable smod)
  ;;            :use (half-smod-implies-1a))))

  ;; (defthmd half-smod-implies-1c
  ;;   (implies
  ;;    (and
  ;;     (generic-invertible-p x q)
  ;;     (integerp x)
  ;;     (natp k)
  ;;     (non-trivial-modulus q)
  ;;     (equal (smod (* k x) q) k)
  ;;     (equal (smod (smod (* k x) q) q)
  ;;            (smod k q))
  ;;     )
  ;;    (equal (mod x q) 1)))
      
  ;;     (generic-invertible-p x q)
  ;;     (integerp x)
  ;;     (natp k)
  ;;     (non-trivial-modulus q)
  ;;     (<= k q)
  ;;     (equal (* 2 (smod (* k x) q)) q))
  ;;    )
  ;;   :hints (("Goal" :in-theory (disable smod)
  ;;            :use (half-smod-implies-1a))))
  
  ;; (defthmd half-equals
  ;;   (implies
  ;;    (and
  ;;     (generic-invertible-p x q)
  ;;     (integerp x)
  ;;     (natp k)
  ;;     (non-trivial-modulus q)
  ;;     (<= k q))
  ;;    (iff (equal (* 2 (smod (* k x) q)) q)
  ;;         (or (equal k 0)
  ;;             (equal k q)
  ;;             (equal (* 2 k) q))))
  ;;   :hints (("Goal" :in-theory nil
  ;;            :use (half-implies-2
  ;;                  half-implies-3))))
  
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd smod-commutes-plus-different
    (implies
     (and
      (integerp a)
      (integerp b)
      (posp q))
     ;; (not (equal (msign a q) (msign b q))))
     (equal (smod (+ a b) q)
            (if (not (equal (msign a q) (msign b q)))
                (+ (smod a q)
                   (smod b q))
              ;; 1/2 is positive .. and they have the same
              ;; so the result will be negative
              (if (equal (msign a q) (msign (- a) q))
                  (if (equal (msign b q) (msign (- b) q))
                      0
                    (- (smod b q) (smod a q)))
                (if (equal (msign b q) (msign (- b) q))
                    (- (smod a q) (smod b q))
                  (hide (smod (+ a b) q)))))))
    :hints (("Goal" :in-theory (enable abs)
             :expand (hide (smod (+ a b) q)))))

  )

(defund smallest-coefficient-pair-p (n k m x q)
  ;; n : universally quantified variable
  ;; k/m : coefficients
  ;; x : original value
  ;; q : modulus
  (let ((n (nfix n))
        (k (nfix k))
        (m (nfix m))
        (x (nfix x))
        (q (posfix q)))
    (implies
     (and (not (equal (mod n q) 0)) ;; smod (* n x) q) 0))
          (< (mabs (* n x) q) (+ (mabs (* k x) q) (mabs (* m x) q))))
     (and (implies (equal (msign (* n x) q) (msign (* k x) q)) (<= k n))
          (implies (equal (msign (* n x) q) (msign (* m x) q)) (<= m n))))))

(defthm smallest-coefficient-pair-p-commutes
  (iff (smallest-coefficient-pair-p n k m x q)
       (smallest-coefficient-pair-p n m k x q))
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-p)
                                  (nfix posfix mabs msign)))))

(defthm smallest-coefficient-pair-p-natp-congruence
  (implies
   (not (natp n))
   (equal (smallest-coefficient-pair-p n k m x q)
          (smallest-coefficient-pair-p 0 k m x q)))
  :hints (("Goal" :in-theory (e/d (nfix smallest-coefficient-pair-p)
                                  (posfix mabs msign)))))

(defun-sk smallest-coefficient-pair (k m x q)
  (forall (n) (smallest-coefficient-pair-p (nfix n) k m x q)))

(defthmd smallest-coefficient-pair-commutes
  (iff (smallest-coefficient-pair k m x q)
       (smallest-coefficient-pair m k x q))
  :hints (("Goal" :in-theory (disable nfix))
          ("subgoal 1" :in-theory (disable smallest-coefficient-pair-necc)
           :use (:instance smallest-coefficient-pair-necc
                           (n (smallest-coefficient-pair-witness m k x q))))
          ("subgoal 2" :in-theory (disable smallest-coefficient-pair-necc)
           :use (:instance smallest-coefficient-pair-necc
                           (n (smallest-coefficient-pair-witness k m x q))
                           (k m)
                           (m k)))))

(in-theory (disable smallest-coefficient-pair smallest-coefficient-pair-p-commutes))

(defthmd smallest-coefficient-pair-implication
  (implies
   (and
    (natp n)
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (smallest-coefficient-pair k m x q))
   (smallest-coefficient-pair-p n k m x q))
  :hints (("Goal" :use smallest-coefficient-pair-necc)))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm smod-commutes-negation
    (implies
     (and
      (posp q)
      (integerp a)
      )
     (equal (smod (- a) q)
            (if (equal (* 2 (mabs a q)) q) (smod a q)
              (- (smod a q)))))
    :hints (("Goal" :in-theory (enable mabs abs))))

  )



(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm equal-smod-product-reduction
    (implies
     (and
      (posp q)
      (natp n)
      (natp x)
      (generic-invertible-p x q)
      (natp k))
     (equal (equal (smod (* n x) q)
                   (smod (* k x) q))
            (equal (mod n q)
                   (mod k q))))
    :hints (("Goal" :in-theory (e/d (smod) (mod)))))

  )

#+joe
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd not-equal-mod
    (implies
     (and
      (integerp k)
      (integerp m)
      (integerp x)
      (posp q)
      (not (equal (msign (* k x) q) (msign (* m x) q))))
     (not (equal (mod k q) (mod m q)))))

  )

(in-theory (disable smod))

(defun delta (n m)
  (- (ifix n) (ifix m)))

(include-book "arithmetic-5/top" :dir :system)

#+joe
(defthm times-equal-zero
  (implies
   (and
    (integerp x)
    (integerp c)
    (not (equal c 0)))
   (iff (equal (* c x) 0)
        (equal x 0))))

;; (set-evisc-tuple nil)
;; :monitor (:rewrite smod-commutes-plus-different) '(:target :go)
;; :brr t

(defthm smod-times-mod
  (implies
   (and (integerp x) (integerp n) (integerp q))
   (equal (smod (* x (mod n q)) q)
          (smod (* x n) q)))
  :hints (("Goal" :in-theory (enable smod))))

(defthm smod-zero
  (equal (smod 0 q) 0)
  :hints (("Goal" :in-theory (enable smod))))

(in-theory (enable equal-smod-zero-x smod-commutes-plus-different))

(defthmd smallest-coefficients-next-step-helper
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (smallest-coefficient-pair k m x q)
    (not (equal (msign (* m x) q) (msign (* k x) q)))
    (natp N)
    (< k q)
    (< m q)
    (< (mabs (* k x) q) (mabs (* m x) q))
    )
   (smallest-coefficient-pair-p n k (+ k m) x q))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable abs smallest-coefficient-pair-p)
           :use (smallest-coefficient-pair-implication))
          (and stable-under-simplificationp
               '(:use (:instance smallest-coefficient-pair-implication
                                 (n (delta n m)))))
          (and stable-under-simplificationp
               '(:use (:instance smallest-coefficient-pair-implication
                                 (n (delta n k)))))
          ))

(defthm smallest-coefficients-next-step
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (smallest-coefficient-pair k m x q)
    (not (equal (msign (* m x) q) (msign (* k x) q)))
    (< k q)
    (< m q)
    (< (mabs (* k x) q) (mabs (* m x) q))
    )
   (smallest-coefficient-pair k (+ k m) x q))
  :hints (("Goal" :expand ((:free (x) (hide x))
                           (smallest-coefficient-pair k (+ k m) x q))
           :use (
                 (:instance smallest-coefficients-next-step-helper
                            (n (nfix (SMALLEST-COEFFICIENT-PAIR-WITNESS K (+ K M) X Q))))
                 (:instance smallest-coefficients-next-step-helper
                            (n 0))
                 ))))

(defthm smallest-coefficients-next-step-commutes
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (smallest-coefficient-pair k m x q)
    (not (equal (msign (* m x) q) (msign (* k x) q)))
    (< k q)
    (< m q)
    (< (mabs (* m x) q) (mabs (* k x) q))
    )
   (smallest-coefficient-pair (+ k m) m x q))
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-commutes)
                                  (smallest-coefficients-next-step))
           :use (:instance smallest-coefficients-next-step
                           (k m)
                           (m k)))))
