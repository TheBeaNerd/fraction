(in-package "ACL2")

(include-book "generic-mod-property")
(include-book "coi/util/skip-rewrite" :dir :system)
(include-book "nary")

(defun negp (x)
  (declare (type t x))
  (and (integerp x)
       (< x 0)))

(defun neg-fix (x)
  (if (negp x) x -1))

(defun neg-equiv (x y)
  (equal (neg-fix x)
         (neg-fix y)))

(defthm negp-neg-fix
  (implies
   (negp x)
   (equal (neg-fix x) x)))

(defequiv neg-equiv)

(defthm negp-implies
  (implies
   (negp x)
   (and (integerp x)
        (< x 0)))
  :rule-classes (:forward-chaining))

(defun non-trivial-modulus (q)
  (declare (type t q))
  (and (integerp q)
       (< 2 q))) 

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

  (defthm pmod-zero
    (equal (pmod 0 q) 0))
  
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
          
  (in-theory (disable pmod nmod))
  
  (in-theory (enable pmod-congruence))
  
  )

(defun minimal-fractions-pair-p (z k n m p x q)
  ;; z : universally quantified variable
  ;; k : negative coefficient
  ;; m : positive coefficient
  ;; x : original value
  ;; q : modulus
  (let ((z (pfix z))
        (k (nfix k))
        (n (neg-fix n))
        (m (nfix m))
        (p (nfix p))
        (x (nfix x))
        (q (pfix q)))
    (and
     (implies
      (< (- (nmod (* z x) q)) (- p n))
      (<= k z))
     (implies
      (and
       (not (equal (pmod z q) 0))
       (< (pmod (* z x) q) (- p n)))
      (<= m z)))))

(defun smallest-coefficient-pair-p (z k m x q)
  ;; z : universally quantified variable
  ;; k : negative coefficient
  ;; m : positive coefficient
  ;; x : original value
  ;; q : modulus
  (let ((z (pfix z))
        (k (nfix k))
        (m (nfix m))
        (x (nfix x))
        (q (pfix q)))
    (minimal-fractions-pair-p z k (nmod (* k x) q) m (pmod (* m x) q) x q)))

(encapsulate
    ()

  (local (in-theory (disable nfix-equiv ifix-equiv pfix-equiv)))
  (local (in-theory (disable ifix nfix pfix abs)))
  
  (defcong pfix-equiv equal (smallest-coefficient-pair-p z k m x q) 1)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 2)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 3)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 4)
  (defcong pfix-equiv equal (smallest-coefficient-pair-p z k m x q) 5)

  ;; (local
  ;;  (defthm not-natp-nfix
  ;;    (implies
  ;;     (not (natp x))
  ;;     (equal (nfix x) 0))
  ;;    :hints (("Goal" :in-theory (enable nfix)))))

  ;; (defthm smallest-coefficient-pair-p-natp-congruence
  ;;   (implies
  ;;    (not (natp z))
  ;;    (equal (smallest-coefficient-pair-p z k m x q)
  ;;           (smallest-coefficient-pair-p 0 k m x q))))
  
)

(defun-sk smallest-coefficient-pair (k m x q)
  (forall (z) (smallest-coefficient-pair-p (pfix z) k m x q))
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
    (forall (z) (smallest-coefficient-pair-p (pfix z) k m x q))
    :hyps smallest-coefficient-pair-equiv)

  )

(in-theory (disable smallest-coefficient-pair))

(defthmd smallest-coefficient-pair-implication
  (implies
   (smallest-coefficient-pair     k m x q)
   (smallest-coefficient-pair-p z k m x q))
  :hints (("Goal" :use smallest-coefficient-pair-necc)))

(in-theory (disable smallest-coefficient-pair-p))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()
     
     (local
      (defun delta (n m)
        (abs (- (ifix n) (ifix m)))))
     
     (defthmd smallest-coefficient-pair-invariant-1-helper
       (implies
        (and
         (natp k)
         (natp m)
         (natp x)
         (non-trivial-modulus q)
         (generic-invertible-p x q)
         (smallest-coefficient-pair k m x q)
         (posp a)
         (< k q)
         (< m q)
         (<= (- (nmod (* k x) q)) (pmod (* m x) q))
         )
        (smallest-coefficient-pair-p a k (+ k m) x q))
       :hints (("Goal" :do-not-induct t
                :do-not '(generalize eliminate-destructors)
                :use ((:instance smallest-coefficient-pair-implication
                                 (z a))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a m)))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a k)))))
               (and stable-under-simplificationp
                    '(:in-theory (enable smallest-coefficient-pair-p)))
               ))
     
     (defthmd smallest-coefficient-pair-invariant-2-helper
       (implies
        (and
         (natp k)
         (natp m)
         (natp x)
         (non-trivial-modulus q)
         (generic-invertible-p x q)
         (smallest-coefficient-pair k m x q)
         (posp a)
         (< k q)
         (< m q)
         (< (pmod (* m x) q) (- (nmod (* k x) q)))
         )
        (smallest-coefficient-pair-p a (+ k m) m x q))
       :hints (("Goal" :do-not-induct t
                :do-not '(generalize eliminate-destructors)
                :use ((:instance smallest-coefficient-pair-implication
                                 (z a))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a m)))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a k)))))
               (and stable-under-simplificationp
                    '(:in-theory (enable smallest-coefficient-pair-p)))
               ))
     
     ))

  (defthm smallest-coefficient-pair-invariant-1
    (implies
     (and
      (natp k)
      (natp m)
      (natp x)
      (non-trivial-modulus q)
      (generic-invertible-p x q)
      (smallest-coefficient-pair k m x q)
      (< k q)
      (< m q)
      (<= (- (nmod (* k x) q)) (pmod (* m x) q)))
     (smallest-coefficient-pair k (+ k m) x q))
    :hints (("Goal" :in-theory (disable pfix)
             :expand ((smallest-coefficient-pair k (+ k m) x q)))
            (and stable-under-simplificationp
                 '(:use (:instance smallest-coefficient-pair-invariant-1-helper
                                   (a (pfix (SMALLEST-COEFFICIENT-PAIR-WITNESS K (+ K M) X Q))))))))
  
  (defthm smallest-coefficient-pair-invariant-2
    (implies
     (and
      (natp k)
      (natp m)
      (natp x)
      (non-trivial-modulus q)
      (generic-invertible-p x q)
      (smallest-coefficient-pair k m x q)
      (< k q)
      (< m q)
      (< (pmod (* m x) q) (- (nmod (* k x) q)))
      )
     (smallest-coefficient-pair (+ k m) m x q))
    :hints (("Goal" :in-theory (disable pfix)
             :expand ((smallest-coefficient-pair (+ k m) m x q)))
            (and stable-under-simplificationp
                 '(:use (:instance smallest-coefficient-pair-invariant-2-helper
                                   (a (pfix (SMALLEST-COEFFICIENT-PAIR-WITNESS (+ K M) M X Q))))))))
  )

(defthmd smallest-coefficient-pair-implies-minimal-fractions-pair-p
  (implies
   (and
    (posp z)
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (smallest-coefficient-pair k m x q))
   (minimal-fractions-pair-p z k (nmod (* k x) q) m (pmod (* m x) q) x q))
  :hints (("Goal" :use smallest-coefficient-pair-implication
           :in-theory (enable smallest-coefficient-pair-p))))

(in-theory (disable minimal-fractions-pair-p))

(def::un step-minimal-fractions-pair (k n m p)
  (declare (xargs :signature ((natp negp natp natp) natp negp natp natp)))
  (if (< p (- n)) (mv (+ k m) (+ n p) m p)
    (mv k n (+ k m) (+ n p))))

(defthm smallest-coefficient-pair-step-minimal-fractions-pair
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (generic-invertible-p x q)
    (< k q)
    (< m q)
    (smallest-coefficient-pair k m x q)
    (equal n (nmod (* k x) q))
    (equal p (pmod (* m x) q)))
   (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
     (and (smallest-coefficient-pair k m x q)
          (equal n (nmod (* k x) q))
          (equal p (pmod (* m x) q)))))
  :hints (("Subgoal 1" :use (smallest-coefficient-pair-invariant-1))
          ("Subgoal 2" :use (smallest-coefficient-pair-invariant-2))))


(encapsulate
    ()

  (local
   (defthm smallest-coefficient-pair-p-init-helper
     (implies
      (and
       (posp z)
       (natp x)
       (non-trivial-modulus q))
      (and (smallest-coefficient-pair-p z 0 1 x q)
           (smallest-coefficient-pair-p z 1 0 x q)))
     :hints (("Goal" :in-theory (enable MINIMAL-FRACTIONS-PAIR-P
                                        smallest-coefficient-pair-p)))))

  (defthm smallest-coefficient-pair-init
    (implies
     (and
      (natp x)
      (non-trivial-modulus q))
     (and (smallest-coefficient-pair 0 1 x q)
          (smallest-coefficient-pair 1 0 x q)))
    :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair)
                                    (PFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-1)))))
  
  )
  
;;
;;
;;

(defthmd magnitude-invariant
  (implies
   (and
    (natp k)
    (integerp n)
    (< n 0)
    (natp m)
    (natp p)
    (equal (- (* k p) (* m n)) c))
   (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
           (equal (- (* k p) (* m n)) c))))

(encapsulate
    ()

  (defun lt-sqrt (x q)
    (< (* x x) q))
     
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()

     (defun num-equal (x y)
       (equal x y))
     
     (defun prod (x y)
       (* x y))
     
     (defthmd magnitude-invariant-helper
       (implies
        (and
         (natp k)
         (integerp n)
         (< n 0)
         (natp m)
         (natp p)
         (num-equal (- (prod k p) (prod m n)) c))
        (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
                (num-equal (- (prod k p) (prod m n)) c))))
     
     (defthm negative-product
       (equal (- (prod x y))
              (prod x (- y))))
     
     (defthm posp-prod
       (implies
        (and
         (posp x)
         (posp y))
        (posp (prod x y))))
     
     (defthmd lte-square-lte
       (implies
        (and
         (natp a)
         (natp b)
         (<= (* a a) (* b b)))
        (<= a b))
       :hints (("Goal" :nonlinearp t)))
     
     (defthmd lte-property
       (implies
        (and
         (natp a)
         (natp b)
         (natp c)
         (<= a b)
         (<= a c))
        (<= (* a a) (* b c)))
       :hints (("Goal" :nonlinearp t)))
     
     (defthm product-of-nlt-sqrt
       (implies
        (and
         (natp x)
         (natp y)
         (natp c)
         (not (lt-sqrt x c))
         (not (lt-sqrt y c)))
        (<= c (prod x y)))
       :hints (("Goal" :use ((:instance lte-property
                                        (a c)
                                        (b (* x x))
                                        (c (* y y))
                                        )
                             (:instance lte-square-lte
                                        (a c)
                                        (b (* x y)))
                             ))))

     (defthm not-num-equal-1
       (implies
        (and
         (posp x)
         (posp y)
         (<= c x))
        (not (num-equal (+ x y) c))))
     
     (defthm not-num-equal-2
       (implies
        (and
         (posp x)
         (posp y)
         (<= c y))
        (not (num-equal (+ x y) c))))
     
     (defthm negative-lt-sqrt
       (implies
        (< n 0)
        (equal (lt-sqrt n c)
               (lt-sqrt (- n) c))))
     
     (in-theory (disable prod num-equal lt-sqrt))
     
     (defthm one-fraction-lt-sqrt-helper-1
       (implies
        (and
         (posp k)
         (integerp n)
         (< n 0)
         (posp m)
         (posp p)
         (natp c)
         (not (equal p (- n)))
         (num-equal (- (prod k p) (prod m n)) c)
         (lt-sqrt k c)
         (lt-sqrt m c)
         (not (lt-sqrt (+ k m) c))
         (not (lt-sqrt p c))
         (not (lt-sqrt n c)))
        nil)
       :rule-classes nil
       :hints (("Goal" :use magnitude-invariant-helper)))

     (defthm one-fraction-lt-sqrt-helper-2
       (implies
        (and
         (posp k)
         (integerp n)
         (< n 0)
         (posp m)
         (posp p)
         (natp c)
         (not (equal p (- n)))
         (num-equal (- (prod k p) (prod m n)) c)
         (lt-sqrt k c)
         (lt-sqrt m c)
         (not (lt-sqrt (+ k m) c)))
        (or (lt-sqrt p c)
            (lt-sqrt n c)))
       :rule-classes nil
       :hints (("Goal" :use one-fraction-lt-sqrt-helper-1)))

     ))

  (defthm one-fraction-lt-sqrt
    (implies
     (and
      (posp k)
      (integerp n)
      (< n 0)
      (posp m)
      (posp p)
      (natp c)
      (not (equal p (- n)))
      (equal (- (* k p) (* m n)) c)
      (lt-sqrt k c)
      (lt-sqrt m c)
      (not (lt-sqrt (+ k m) c)))
     (or (lt-sqrt p c)
         (lt-sqrt n c)))
    :rule-classes nil
    :hints (("Goal" :in-theory '(num-equal prod)
             :use one-fraction-lt-sqrt-helper-2)))

  )

;; k n m p
;; (equal (- (* k p) (* m n)) q)
;; 1 -v 0 Q
;; (equal (- (* 1 Q) (* 0 -v)) q)
;; 0 -Q 1 v
;; (equal (- (* 0 v) (* 1 Q)) q)
;;
;; I think we need to modify our invaiant.
;; - it will simplify things in the long run.
;;

;; 1 -v 1 Q-v

