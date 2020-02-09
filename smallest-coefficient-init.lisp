(in-package "ACL2")

(include-book "smallest-coefficient-step")

(in-theory (disable SMOD-COMMUTES-MULTIPLICATION))

(local (include-book "arithmetic-5/top" :dir :system))

(defthmd mod-plus-same-sign
  (implies
   (and
    (not (and (equal (* 2 (mabs a q)) q)
              (equal (* 2 (mabs b q)) q)))
    (integerp a)
    (integerp b)
    (posp q)
    (equal (msign a q) (msign b q))
    (equal (msign (+ a b) q) (msign a q)))
   (equal (mod (+ a b) q)
          (if (< 0 (msign a q))
              (+ (mod a q)
                 (mod b q))
            (+ (- q) (mod a q) (mod b q)))))
  :hints (("Goal" :in-theory (enable ifix abs mabs smod msign))))

(defthmd smod-plus-same-sign
  (implies
   (and
    (not (and (equal (* 2 (mabs a q)) q)
              (equal (* 2 (mabs b q)) q)))
    (integerp a)
    (integerp b)
    (posp q)
    (equal (msign a q) (msign b q))
    (equal (msign (+ a b) q) (msign a q)))
   (equal (smod (+ a b) q)
          (+ (smod a q)
             (smod b q))))
  :hints (("Goal" :in-theory (enable ifix abs mabs smod msign))))

(defthm smod-zero
  (equal (smod 0 c) 0)
  :hints (("Goal" :in-theory (enable smod))))

(defun all-same-sign-upto-n (n x q)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (enable nfix posfix)))))
  (let ((n  (nfix n))
        (x  (nfix x))
        (q  (posfix q)))
    (if (equal (* 2 (mabs x q)) q) nil
      (if (<= n 0) t
        (and (equal (msign (* n x) q) (msign x q))
             (all-same-sign-upto-n (1- n) x q))))))

;; (skip-proofs
;;  (defthm generic-invertible-p-implies-not-divisible
;;    (implies
;;     (generic-invertible-p x q)
;;     (not (integerp (* (/ q) x))))
;;    :rule-classes (:forward-chaining))
;;  )

;; (skip-proofs
;;  (defthm generic-invertible-p-implies-not-divisible-corr
;;    (implies
;;     (generic-invertible-p x q)
;;     (not (EQUAL (MOD X Q) (* 1/2 Q))))
;;    :rule-classes (:forward-chaining))
;;  )

;; (defthm an-inverting-value-exists
;;   (implies
;;    (and
;;     (integerp x)
;;     (posp q)
;;     (generic-invertible-p x q)
;;     (equal v (- q 1)))
;;    (not (equal (msign (* v x) q) (msign x q))))
;;   :hints (("Goal" :in-theory (enable smod))))

(defun smallest-coefficient (n x q)
  (declare (xargs :measure (nfix (- (posfix q) (nfix n)))
                  :hints (("Goal" :in-theory (enable nfix)))))
  (let ((n (nfix n))
        (q (posfix q))
        (x (nfix x)))
    (let ((n (1+ n)))
      (if (<= q n) 0
        (if (not (equal (msign (* n x) q) (msign x q))) n
          (smallest-coefficient n x q))))))

(defthm all-same-sign-upto-n-are-the-same
  (implies
   (and
    (all-same-sign-upto-n n x q)
    (<= c n)
    (natp n)
    (posp q)
    (natp x)
    (posp c))
   (equal (msign (* c x) q) (msign x q))))

(defthm smallest-coefficient-is-smallest
  (implies
   (and
    (all-same-sign-upto-n n x q)
    (< c (smallest-coefficient n x q))
    (natp n)
    (posp q)
    (natp x)
    (posp c))
   (equal (msign (* c x) q) (msign x q)))
  :hints (("Goal" :induct (smallest-coefficient n x q)
           :in-theory (disable msign))))

(defthm smallest-coefficient-is-smallest-instance
  (implies
   (and
    (< c (smallest-coefficient 0 x q))
    (not (equal (* 2 (mabs x q)) q))
    (posp q)
    (natp x)
    (posp c))
   (equal (msign (* c x) q) (msign x q)))
  :hints (("Goal" :use (:instance smallest-coefficient-is-smallest
                                  (n 0))
           :expand (all-same-sign-upto-n 0 x q)
           :in-theory (disable smallest-coefficient-is-smallest))))

(defthm positive-smallest-coefficient-changes-sign
  (implies
   (and
    (equal (msign (* x (smallest-coefficient n x q)) q)
           (msign x q))
    (natp n)
    (posp q)
    (natp x))
   (equal (smallest-coefficient n x q) 0)))

(defthm msign-times-smallest-coefficient
  (implies
   (and
    (natp n)
    (posp q)
    (natp x)
    (< 0 (smallest-coefficient n x q)))
   (equal (msign (* x (smallest-coefficient n x q)) q)
          (- (msign x q)))))

(defthm smallest-coefficient-pair-p-1-smallest-coefficient
  (implies
   (and
    (natp n)
    (posp q)
    (natp x)
    (force (not (equal (* 2 (mabs x q)) q))))
   (smallest-coefficient-pair-p n 1 (smallest-coefficient 0 x q) x q))
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-p) 
                                  ((:type-prescription msign) 
                                   msign)))))


(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthmd generic-invertible-p-mod-rewrite
       (implies
        (force 
         (and
          (integerp x)
          (posp q)))
        (iff (generic-invertible-p (mod x q) q)
             (generic-invertible-p x q)))
       :hints (("Goal" :use generic-invertible-p-mod)))
     
     (defthm mod-of-modulus
       (implies
        (force (and (integerp x) (integerp q)))
        (equal (MOD (+ Q x) Q)
               (mod x q))))
     
     (defthm mod-negation
       (implies
        (and
         (integerp x)
         (integerp q))
        (equal (mod (- (mod x q)) q)
               (mod (- x) q))))
     
     (defthmd generic-invertible-p-mabs-helper
       (implies
        (and
         (integerp x)
         (posp q)
         (generic-invertible-p x q))
        (generic-invertible-p (mod (mabs x q) q) q))
       :hints (("Goal" :in-theory `((force) mod-of-modulus posp ifix posfix nfix smod abs mabs |(- (- x))|))
               (and stable-under-simplificationp
                    '(:in-theory `((force) mod-of-modulus posp ifix posfix nfix smod abs mabs |(- (- x))| 
                                   mod-negation generic-invertible-p-mod-rewrite)))
               (and stable-under-simplificationp
                    '(:in-theory (current-theory :here)))))
     ))

  (defthm generic-invertible-p-mabs
    (implies
     (and
      (integerp x)
      (posp q)
      (generic-invertible-p x q))
     (generic-invertible-p (mabs x q) q))
    :rule-classes (:rewrite
                   (:forward-chaining :trigger-terms ((mabs x q))))
    :hints (("Goal" :use generic-invertible-p-mabs-helper
             :in-theory (enable generic-invertible-p-mod-rewrite))))

  )

(encapsulate
    ()

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
     
  (defthm generic-invertible-p-implication-1
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

(defthm implies-not-half
  (implies
   (and
    (generic-invertible-p x q)
    (integerp x)
    (non-trivial-modulus q))
   (not (equal (* 2 (mabs x q)) q)))
  :hints (("Goal" :use (:instance generic-invertible-p-implication-1
                                  (x (mabs x q))
                                  (q q)))
          (and stable-under-simplificationp
               '(:in-theory (enable mabs abs posfix smod))))
  :rule-classes :forward-chaining)

(defthm smallest-coefficient-pair-1-smallest-coefficient
  (implies
   (and
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (natp x))
   (smallest-coefficient-pair 1 (smallest-coefficient 0 x q) x q))
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair) (smallest-coefficient mabs)))))

;;
;; Now .. the grand finale ..
;;
(defun all-mabs (m x q)
  (if (zp m) nil
    (cons (mabs (* m x) q)
          (all-mabs (1- m) x q))))

;; (defthm mabs-km-is-lower-bound
;;   (implies
;;    (and
;;     (non-trivial-modulus q)
;;     (generic-invertible-p x q)
;;     (natp k)
;;     (natp m)
;;     (natp x)
;;     (smallest-coefficient-pair k m x q)
;;     (< k m))
;;    (and (< (mabs (* k x) q) (min-difference m x q))
;;         (< (mabs (* m x) q) (min-difference m x q)))))
;; (implies
;;  (not
;;   (and
;;    (equal i k)
;;    (equal j m))
;; (<  (abs (- (mabs (* i x) q) (mabs (* j x) q))) (max (mabs (* k x) q) (mabs (* m x) q)))

