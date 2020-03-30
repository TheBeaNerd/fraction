;;
;; Copyright (C) 2020, David Greve
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;;
(in-package "ACL2")

(include-book "smallest-coefficient-step")

(defun all-same-sign-upto-n (n x q)
  (declare (xargs :measure (nfix n)
                  :hints (("Goal" :in-theory (enable nfix posfix)))))
  (let ((n  (nfix n))
        (x  (nfix x))
        (q  (posfix q)))
    (if (equal (smod x q) 0) nil
      (if (equal (* 2 (mabs x q)) q) nil
        (if (<= n 0) t
          (and (equal (msign (* n x) q) (msign x q))
               (all-same-sign-upto-n (1- n) x q)))))))
  
(def::un minimal-fraction-init-rec (n x q)
  (declare (xargs :measure (nfix (- (posfix q) (nfix n)))
                  :signature ((t t t) natp)
                  :hints (("Goal" :in-theory (enable nfix)))))
  (let ((n (nfix n))
        (q (posfix q))
        (x (nfix x)))
    (if (<= q n) 0
      (let ((n (1+ n)))
        (if (not (equal (msign (* n x) q) (msign x q))) n
          (minimal-fraction-init-rec n x q))))))

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

(defthm minimal-fraction-init-rec-is-smallest
  (implies
   (and
    (all-same-sign-upto-n n x q)
    (< c (minimal-fraction-init-rec n x q))
    (natp n)
    (posp q)
    (natp x)
    (posp c))
   (equal (msign (* c x) q) (msign x q)))
  :hints (("Goal" :induct (minimal-fraction-init-rec n x q)
           :in-theory (disable msign))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm smod-zero-product
    (implies
     (and
      (integerp x)
      (integerp q)
      (integerp c)
      (equal (smod x q) 0))
     (equal (smod (* c x) q) 0))
    :hints (("Goal" :in-theory (enable smod nary::mod-rules))))
  
  (defthm no-negative-half
    (implies
     (and
      (integerp x)
      (posp q))
     (not (equal (* -2 (smod x q)) q)))
    :hints (("Goal" :in-theory (enable smod))))

  (defthm half-is-always-positive
    (implies
     (and
      (integerp x)
      (posp q)
      (natp c)
      (equal (* 2 (smod x q)) q))
     (equal (smod (* c x) q)
            (if (equal (mod c 2) 0) 0
              (smod x q))))
    :hints (("Goal" :in-theory (enable smod))))

  (defthm minimal-fraction-init-rec-is-smallest-instance
    (implies
     (and
      (< c (minimal-fraction-init-rec 0 x q))
      (posp q)
      (natp x)
      (posp c))
     (equal (msign (* c x) q) (msign x q)))
    :otf-flg t
    :hints (("Goal" :use (:instance minimal-fraction-init-rec-is-smallest
                                    (n 0))
             :expand (all-same-sign-upto-n 0 x q)
             :in-theory (disable minimal-fraction-init-rec-is-smallest))))

  (defthm positive-minimal-fraction-init-rec-changes-sign
    (implies
     (and
      (equal (msign (* x (minimal-fraction-init-rec n x q)) q)
             (msign x q))
      (natp n)
      (posp q)
      (natp x))
     (equal (minimal-fraction-init-rec n x q) 0))
    :hints (("Goal" :induct (minimal-fraction-init-rec n x q))))
  
  (defthm msign-times-minimal-fraction-init-rec
    (implies
     (and
      (natp n)
      (posp q)
      (natp x)
      ;;(generic-invertible-p x q)
      (< 0 (minimal-fraction-init-rec n x q)))
     (equal (msign (* x (minimal-fraction-init-rec n x q)) q)
            (- (msign x q))))
    :hints (("Goal" :induct (minimal-fraction-init-rec n x q)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-smod-zero-x smod-plus)))))
  
  (defthm smallest-coefficient-pair-p-1-minimal-fraction-init-rec
    (implies
     (and
      (natp n)
      (posp q)
      (natp x)
      ;;(force (not (equal (* 2 (mabs x q)) q)))
      )
     (smallest-coefficient-pair-p n 1 (minimal-fraction-init-rec 0 x q) x q))
    :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-p) 
                                    ((:type-prescription msign) 
                                     msign)))
            (and stable-under-simplificationp
                 '(:in-theory (current-theory :here)))
            ))

  )
  
;; dag
;; :monitor (:rewrite nary::mod-+-congruence) '(:target :go)
;; :monitor (:rewrite generic-invertible-p-mod-congruence) '(:target :go)
;; :brr t
;; (set-evisc-tuple nil)
;; (trace$ NARY::UN-MOD)

(defthm generic-invertible-p-mabs
  (implies
   (and
    (posp q)
    (generic-invertible-p x q))
   (generic-invertible-p (mabs x q) q))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((mabs x q))))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (smod
                            nary::mod-rules
                            generic-invertible-p-mod-congruence
                            )
                           (mod)))))
           
;; (defthmd generic-invertible-p-mabs-helper
;;   (implies
;;    (and
;;     (integerp x)
;;     (posp q)
;;     (generic-invertible-p x q))
;;    (generic-invertible-p (mod (mabs x q) q) q))
;;   :hints (("Goal" :in-theory `((force) mod-of-modulus posp ifix posfix nfix smod abs mabs |(- (- x))|))
;;           (and stable-under-simplificationp
;;                '(:in-theory `((force) mod-of-modulus posp ifix posfix nfix smod abs mabs |(- (- x))| 
;;                               mod-negation generic-invertible-p-mod-rewrite)))
;;           (and stable-under-simplificationp
;;                '(:in-theory (current-theory :here)))))

;; (encapsulate
;;     ()

;;   (local
;;    (encapsulate
;;        ()

;;      (defthmd generic-invertible-p-mod-rewrite
;;        (implies
;;         (force 
;;          (and
;;           (integerp x)
;;           (posp q)))
;;         (iff (generic-invertible-p (mod x q) q)
;;              (generic-invertible-p x q)))
;;        :hints (("Goal" :use generic-invertible-p-mod)))
     
;;      (defthm mod-of-modulus
;;        (implies
;;         (force (and (integerp x) (integerp q)))
;;         (equal (MOD (+ Q x) Q)
;;                (mod x q))))
     
;;      (defthm mod-negation
;;        (implies
;;         (and
;;          (integerp x)
;;          (integerp q))
;;         (equal (mod (- (mod x q)) q)
;;                (mod (- x) q))))
     
;;      (defthmd generic-invertible-p-mabs-helper
;;        (implies
;;         (and
;;          (integerp x)
;;          (posp q)
;;          (generic-invertible-p x q))
;;         (generic-invertible-p (mod (mabs x q) q) q))
;;        :hints (("Goal" :in-theory `((force) mod-of-modulus posp ifix posfix nfix smod abs mabs |(- (- x))|))
;;                (and stable-under-simplificationp
;;                     '(:in-theory `((force) mod-of-modulus posp ifix posfix nfix smod abs mabs |(- (- x))| 
;;                                    mod-negation generic-invertible-p-mod-rewrite)))
;;                (and stable-under-simplificationp
;;                     '(:in-theory (current-theory :here)))))
;;      ))

;;   (defthm generic-invertible-p-mabs
;;     (implies
;;      (and
;;       (integerp x)
;;       (posp q)
;;       (generic-invertible-p x q))
;;      (generic-invertible-p (mabs x q) q))
;;     :rule-classes (:rewrite
;;                    (:forward-chaining :trigger-terms ((mabs x q))))
;;     :hints (("Goal" :use generic-invertible-p-mabs-helper
;;              :in-theory (enable generic-invertible-p-mod-rewrite))))

;;   )

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
  
  (defthm implies-not-half
    (implies
     (and
      (generic-invertible-p x q)
      (integerp x)
      (non-trivial-modulus q))
     (not (equal (* 2 (mabs x q)) q)))
    :hints (("Goal" :in-theory (disable mabs)
             :use (:instance generic-invertible-p-implication-1
                             (x (mabs x q))
                             (q q)))
            (and stable-under-simplificationp
                 '(:in-theory (enable mabs abs posfix smod))))
    :rule-classes :forward-chaining)

  )

(defthm smallest-coefficient-pair-1-minimal-fraction-init-rec
  (implies
   (and
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (natp x))
   (smallest-coefficient-pair 1 (minimal-fraction-init-rec 0 x q) x q))
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair) (minimal-fraction-init-rec mabs)))))

(defun negp (x)
  (declare (type t x))
  (and (integerp x)
       (< x 0)))

(def::un minimal-fraction-init (x q)
  (declare (xargs :signature ((natp posp) natp integerp natp integerp)))
  (let ((c (minimal-fraction-init-rec 0 x q)))
    (let ((y (smod (* c x) q))
          (x (smod x q)))
      (met ((k n m p) (if (< y 0) (mv c y 1 x) (mv 1 x c y)))
        (mv k n m p)))))

(defthm smallest-coefficient-pair-minimal-fraction-init
  (implies
   (and
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (natp x))
   (mv-let (k n m p) (minimal-fraction-init x q)
     (declare (ignore n p))
     (smallest-coefficient-pair k m x q)))
  :hints (("Goal" :in-theory (e/d (generic-invertible-p-mod
                                   SMALLEST-COEFFICIENT-PAIR-COMMUTES)
                                  (MINIMAL-FRACTION-INIT-REC)))))



;; (encapsulate
;;     ()

;;   (local (include-book "arithmetic-5/top" :dir :system))
  
;;   (local
;;    (defthm joe-helper
;;      (implies
;;       (and
;;        (posp n)
;;        (integerp x)
;;        (< (SMOD (* (1- n) X) n) 0))
;;       (not (< (SMOD X n) 0)))
;;      :hints (("Goal" :in-theory (enable smod)))))

;;   (defthm joe
;;     (implies
;;      (and
;;       (natp n)
;;       (integerp x)
;;       (< (SMOD (* N X) (+ 1 n)) 0))
;;      (not (< (SMOD X (+ 1 n)) 0)))
;;     :hints (("Goal" :use (:instance joe-helper
;;                                     (n (1+ n))))))
  
;;   )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm equal-msign-reduction-helper
    (implies
     (and
      (posp n)
      (integerp x))
     (iff (EQUAL (MSIGN (+ (- x) (* n x)) n)
                 (MSIGN X n))
          (or (equal (mod (* 2 x) n) 0)
              (equal (mod x n) 0))))
    :hints (("Goal" :in-theory (enable smod))))

  )


  
  ;; (local
  ;;  (defthm bro-helper
  ;;    (implies
  ;;     (and
  ;;      (posp n)
  ;;      (integerp x)
  ;;      (not (< (SMOD (* (1- N) X) n) 0)))
  ;;     (or (< (SMOD X n) 0)
  ;;         (equal (mod (* 2 x) n) 0)))
  ;;    :hints (("Goal" :in-theory (enable smod)))))

  ;; (defthm bro
  ;;   (implies
  ;;    (and
  ;;     (natp n)
  ;;     (integerp x)
  ;;     (not (< (SMOD (* n X) (+ 1 n)) 0)))
  ;;    (or (< (SMOD X (+ 1 n)) 0)
  ;;        (equal (mod (* 2 x) (+ 1 n)) 0)))
  ;;   :hints (("Goal" :use (:instance bro-helper
  ;;                                   (n (1+ n))))))
  
  ;; )

;; (defthmd mod-2-is-not-negative
;;   (implies
;;    (integerp x)
;;    (NOT (EQUAL (SMOD X 2) -1)))
;;   :hints (("Goal" :in-theory (enable smod))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm diffy
    (implies
     (and
      (EQUAL (MOD (* 2 X) n) 0)
      (<= 0 (SMOD X n)))
     (or (EQUAL (* 2 (SMOD X n)) n)
         (equal (smod x n) 0)))
    :hints (("Goal" :in-theory (enable smod)))
    :rule-classes nil)

  (defthm smod-x-1-is-zero
    (equal (smod x 1) 0)
    :hints (("Goal" :in-theory (enable smod))))

  (defthmd smod-when-mod-is-zero
    (implies
     (equal (mod x n) 0)
     (equal (smod x n) 0))
    :hints (("Goal" :in-theory (enable smod))))
  
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthmd not-all-same-sign-upto-n-minus-1
    (implies
     (and
      (natp x)
      (posp n))
     (not (all-same-sign-upto-n (+ -1 n) x n)))
    :otf-flg t
    :hints (("goal" :do-not-induct t
             :in-theory (e/d (smod-when-mod-is-zero)
                             (all-same-sign-upto-n-are-the-same msign))
             :cases ((<= 1 x))
             :use (:instance all-same-sign-upto-n-are-the-same
                             (n (1- n))
                             (q n)
                             (c (1- n))))
            (and stable-under-simplificationp
                 '(:expand (all-same-sign-upto-n (+ -1 n) x n)))
            (and stable-under-simplificationp
                 '(:in-theory (enable smod)))
            ))

  (defthm not-all-same-sign-upto-n+1
    (implies
     (and
      (natp x)
      (natp n))
     (not (all-same-sign-upto-n n x (+ 1 n))))
    :otf-flg t
    :hints (("Goal" :use (:instance not-all-same-sign-upto-n-minus-1
                                    (n (+ 1 n))))))

  )

(defthmd minimal-fraction-init-rec-is-positive
  (implies
   (and
    (natp n)
    (natp x)
    (non-trivial-modulus q)
    (< n q)
    (all-same-sign-upto-n n x q)
    (generic-invertible-p x q))
   (< 0 (minimal-fraction-init-rec n x q))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm generic-invertible-implies-not-smod-zero
    (implies
     (generic-invertible-p x q)
     (not (equal (smod x q) 0)))
    :hints (("Goal" :in-theory (enable smod generic-invertible-p))))

  (defthm times-normalization
    (implies
     (syntaxp (quotep c))
     (equal (* c (- x))
            (* (- c) x))))
 
  )

(defthm not-negative-half-instance
  (implies
   (and
    (generic-invertible-p x q)
    (integerp x)
    (non-trivial-modulus q))
   (not (equal (* -2 (smod x q)) q)))
  :hints (("Goal" :use (:instance not-negative-half
                                  (k 1)))))


;;
;; (integerp q) is disappearing in the following proof .. thus
;; it fails.
;;
(local (include-book "std/testing/must-fail-local" :dir :system))

(must-fail-local
 (defthm all-same-sign-upto-n-zero-fails
   (implies
    (and
     (natp n)
     (natp x)
     (non-trivial-modulus q)
     (generic-invertible-p x q))
    (all-same-sign-upto-n 0 x q))
   :otf-flg t
   :hints (("Goal" :use (half-smod-implies)))))

(defthm all-same-sign-upto-n-zero
  (implies
   (and
    (natp n)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q))
   (all-same-sign-upto-n 0 x q))
  :otf-flg t
  :hints (("Goal" :in-theory '(abs posp mabs posfix nfix natp non-trivial-modulus
                                   generic-invertible-implies-not-smod-zero
                                   times-normalization
                                   not-negative-half-instance)
           :expand (ALL-SAME-SIGN-UPTO-N 0 X Q)
           :use (half-smod-implies))))

(defthm minimal-fraction-init-rec-is-positive-instance
  (implies
   (and
    (natp n)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q))
   (< 0 (minimal-fraction-init-rec 0 x q)))
  :otf-flg t
  :hints (("Goal" :in-theory (disable all-same-sign-upto-n)
           :use (half-smod-implies
                 (:instance minimal-fraction-init-rec-is-positive
                            (n 0))))))

(defthm msign-times-minimal-fraction-init-rec-instance
  (implies
   (and
    (natp n)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q))
   (equal (msign (* x (minimal-fraction-init-rec 0 x q)) q)
          (- (msign x q))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable msign))))
