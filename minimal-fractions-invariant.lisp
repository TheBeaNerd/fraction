(in-package "ACL2")

(include-book "generic-mod-property")
(include-book "nary")

(defun negp (x)
  (declare (type t x))
  (and (integerp x)
       (< x 0)))

(defthm negp-implies
  (implies
   (negp x)
   (and (integerp x)
        (< x 0)))
  :rule-classes (:forward-chaining))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (def::un pmod (x q)
    (declare (xargs :signature ((t t) natp)))
    (mod (ifix x) (pfix q)))
  
  (defthm mod-pmod
    (implies
     (and
      (integerp x)
      (posp q))
     (equal (mod (pmod x q) q)
            (mod x q))))

  ;; This is too painful ..
  (defthmd drop-pmod
    (implies
     (and
      (natp x)
      (posp q)
      (< x q))
     (equal (pmod x q) x)))

  (defthm pmod-bound
    (implies
     (posp q)
     (< (pmod x q) q))
    :rule-classes (:linear))
  
  (def::un nmod (x q)
    (declare (xargs :signature ((t t) negp)))
    (- (mod (ifix x) (pfix q)) (pfix q)))

  (defthm nmod-reduction
    (equal (nmod a q)
           (- (pmod a q) (pfix q)))
    :hints (("Goal" :in-theory (enable nmod pmod))))

  (defthm mod-ctx-pmod-reduction
    (implies
     (and (natp x) (posp q))
     (equal (mod-ctx (pmod x q) q)
            (mod-ctx x q))))

  (defthmd pmod-congruence
    (implies
     (and
      (integerp q)
      (integerp x)
      (nary::bind-context
       (equal z (mod-ctx x q))))
     (equal (pmod x q)
            (pmod z q)))
    :hints (("Goal" :in-theory (enable mod-ctx))))
    
  (defthm pmod-negation
    (implies
     (and (integerp x) (posp q))
     (equal (pmod (- x) q)
            (if (equal (pmod x q) 0) 0
              (- (nmod x q))))))

  (defthm pmod-sum
    (implies
     (and
      (integerp a)
      (integerp b)
      (posp q))
     (equal (pmod (+ a b) q)
            (if (< (+ (pmod a q) (pmod b q)) q)
                (+ (pmod a q) (pmod b q))
              (- (+ (pmod a q) (pmod b q)) q)))))

  ;; We just need the rest of the essential properties
  ;; of pmod/nmod

  (in-theory (disable pmod nmod))

  (in-theory (enable pmod-congruence))
  
  )

(defun smallest-coefficient-pair-p (z k m x q)
  ;; z : universally quantified variable
  ;; k : negative coefficient
  ;; m : positive coefficient
  ;; x : original value
  ;; q : modulus
  (let ((z (nfix z))
        (k (nfix k))
        (m (nfix m))
        (x (nfix x))
        (q (pfix q)))
    (and
     (implies
      (< (- (nmod (* z x) q)) (- (pmod (* m x) q) (nmod (* k x) q)))
      (<= k z))
     (implies
      (and
       (not (equal (pmod z q) 0))
       (< (pmod (* z x) q) (- (pmod (* m x) q) (nmod (* k x) q))))
      (<= m z)))))

(encapsulate
    ()

  (local (in-theory (disable nfix-equiv ifix-equiv pfix-equiv)))
  (local (in-theory (disable ifix nfix pfix abs)))
  
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 1)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 2)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 3)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 4)
  (defcong pfix-equiv equal (smallest-coefficient-pair-p z k m x q) 5)

  (local
   (defthm not-natp-nfix
     (implies
      (not (natp x))
      (equal (nfix x) 0))
     :hints (("Goal" :in-theory (enable nfix)))))

  (defthm smallest-coefficient-pair-p-natp-congruence
    (implies
     (not (natp z))
     (equal (smallest-coefficient-pair-p z k m x q)
            (smallest-coefficient-pair-p 0 k m x q))))
  
)

(defun-sk smallest-coefficient-pair (k m x q)
  (forall (z) (smallest-coefficient-pair-p (nfix z) k m x q))
  :strengthen t)

(encapsulate
    ()

  (local (in-theory (disable nth smallest-coefficient-pair-p)))

  (defun smallest-coefficient-pair-equiv (k1 m1 x1 q1 k2 m2 x2 q2)
    (and (nfix-equiv k1 k2)
         (nfix-equiv m1 m2)
         (nfix-equiv x1 x2)
         (pfix-equiv q1 q2)))

  (quant::congruence smallest-coefficient-pair (k m x q)
    (forall (z) (smallest-coefficient-pair-p (nfix z) k m x q))
    :hyps smallest-coefficient-pair-equiv)

  )

(in-theory (disable smallest-coefficient-pair))

(defthmd smallest-coefficient-pair-implication
  (implies
   (smallest-coefficient-pair     k m x q)
   (smallest-coefficient-pair-p z k m x q))
  :hints (("Goal" :use smallest-coefficient-pair-necc)))

;; (defthm times-zero
;;   (equal (* 0 x) 0))

;; (defthm zero-or-one
;;   (implies
;;    (and
;;     (integerp q)
;;     (< 2 q)
;;     (natp m)
;;     (natp x)
;;     (smallest-coefficient-pair 0 m x q))
;;    (or (equal m 1)
;;        (equal m 0)))
;;   :rule-classes nil
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (disable smallest-coefficient-pair-implication)
;;            :use (:instance smallest-coefficient-pair-implication
;;                            (k 0)
;;                            (z 1)))
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable pmod)))))

(defun delta (n m)
  (abs (- (ifix n) (ifix m))))

(in-theory (disable smallest-coefficient-pair-p))

(defun non-trivial-modulus (q)
  (declare (type t q))
  (and (integerp q)
       (< 2 q)))

(include-book "arithmetic-5/top" :dir :system)

(defthm pmod-zero
  (equal (pmod 0 q) 0)
  :hints (("Goal" :in-theory (enable pmod))))

(include-book "coi/util/in-conclusion" :dir :system)
(include-book "coi/util/skip-rewrite" :dir :system)

(defthm force-pmod-rewriting
  (implies
   (and
    (syntaxp (symbolp z))
    (in-conclusion-check (equal (pmod z q) k) :top t)
    (integerp z)
    (posp q))
   (equal (equal (pmod z q) k)
          (hide (rewrite-equiv (equal (mod-ctx z q) k)))))
  :hints (("Goal" :expand ((:free (x) (hide x))))
          (and stable-under-simplificationp
               '(:in-theory (enable pmod mod-ctx)))))
          
(defthmd smallest-coefficient-pair-invariant-1
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (smallest-coefficient-pair k m x q)
    (posp z)
    (< k q)
    (< m q)
    (<= (- (nmod (* k x) q)) (pmod (* m x) q))
    )
   (smallest-coefficient-pair-p z k (+ k m) x q))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :use (smallest-coefficient-pair-implication
                 (:instance smallest-coefficient-pair-implication
                            (z (delta z m)))
                 (:instance smallest-coefficient-pair-implication
                            (z (delta z k)))))
          (and stable-under-simplificationp
               '(:in-theory (enable smallest-coefficient-pair-p)))
          ))

(defthmd smallest-coefficient-pair-invariant-2
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (smallest-coefficient-pair k m x q)
    (posp z)
    (< k q)
    (< m q)
    (< (pmod (* m x) q) (- (nmod (* k x) q)))
    )
   (smallest-coefficient-pair-p z (+ k m) m x q))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :use (smallest-coefficient-pair-implication
                 (:instance smallest-coefficient-pair-implication
                            (z (delta z m)))
                 (:instance smallest-coefficient-pair-implication
                            (z (delta z k)))
                 #+joe
                 (:instance smallest-coefficient-pair-implication
                            (z (- q k)))
                 #+joe
                 (:instance smallest-coefficient-pair-implication
                            (z (- q m)))))
          (and stable-under-simplificationp
               '(:in-theory (enable smallest-coefficient-pair-p)))
          ;; (and stable-under-simplificationp
          ;;      '(:in-theory (enable drop-pmod)))
          ;; (and stable-under-simplificationp
          ;;      '(:in-theory (enable zed
          ;;                           pmod-congruence
          ;;                           nmod-congruence
          ;;                           nary::mod-rules)))
          ))

dag

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm smod-negation
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

;; (local (include-book "arithmetic-5/top" :dir :system))

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
;; :monitor (:rewrite smod-plus) '(:target :go)
;; :brr t

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm smod-times-mod
    (implies
     (and (integerp x) (integerp n) (integerp q))
     (equal (smod (* x (mod n q)) q)
            (smod (* x n) q)))
    :hints (("Goal" :in-theory (enable smod))))
  
  (defthm smod-zero
    (equal (smod 0 q) 0)
    :hints (("Goal" :in-theory (enable smod))))

  (local (in-theory (enable equal-smod-zero-x smod-plus)))
  
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
      (<= (mabs (* k x) q) (mabs (* m x) q))
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
      (<= (mabs (* k x) q) (mabs (* m x) q))
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
      (<= (mabs (* m x) q) (mabs (* k x) q))
      )
     (smallest-coefficient-pair (+ k m) m x q))
    :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-commutes)
                                    (smallest-coefficients-next-step))
             :use (:instance smallest-coefficients-next-step
                             (k m)
                             (m k)))))

  )
  
(def::un step-minimal-fraction (k m x q)
  (declare (xargs :signature ((natp natp integerp posp) natp natp)))
  ;; k is the negative coefficient (< (smod (* k x) q) 0)
  ;; m is the positive coefficient (< 0 (smod (* m x) q))
  (if (< (- (smod (* k x) q)) (smod (* m x) q))
      (mv k (+ k m))
    (mv (+ k m) m)))

;; (encapsulate
;;     ()

;;   (local (include-book "arithmetic-5/top" :dir :system))

;;   (defthm lt-mod-reduction
;;     (implies
;;      (and
;;       (natp x)
;;       (integerp q)
;;       (< x q))
;;      (equal (mod x q) x)))
     
;;   (defthm pull-negation
;;     (equal (* x (- y))
;;            (- (* x y))))

;;   )
  
;; (skip-proofs
;;  (defthm zed
;;    (iff (EQUAL (SMOD (* M X) Q)
;;                (- (SMOD (* K X) Q)))
;;         (equal (mod m q)
;;                (mod (- k) q)))))



(defthm smallest-coefficient-pair-step-minimal-fraction
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (smallest-coefficient-pair k m x q)
    (< (smod (* k x) q) 0)
    (< 0 (smod (* m x) q))
    (< k q)
    (< m q))
   (mv-let (k m) (step-minimal-fraction k m x q)
     (smallest-coefficient-pair k m x q)))
  :otf-flg t
  :hints ((and stable-under-simplificationp
               '(:use (smallest-coefficients-next-step-commutes
                       smallest-coefficients-next-step)))))
  
      
|#
