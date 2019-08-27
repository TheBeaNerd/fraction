(in-package "ACL2")

(encapsulate
     (
      ((invertible-p * *) => *)
      ((inv * *) => *)
      )
   
   (local (defun invertible-p (x p)
            (declare (ignore x p))
            nil))
   
   (local (defun inv (x p)
            (declare (ignore x p))            
            0))

   (defthm integerp-inv
     (integerp (inv x p)))
   
   (defthm modular-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (invertible-p x p))
      (equal (mod (* (inv x p) x) p)
             (mod 1 p))))
   
   (defthm invertible-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (invertible-p x p))
      (invertible-p (inv x p) p)))

   #+joe
   (defthm double-inverse
     (implies
      (and
       (integerp x)
       (natp p)
       (invertible-p x p))
      (equal (mod (inv (inv x p) p) p)
             (mod x p))))

   )

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (local (include-book "arithmetic-5/top" :dir :system))
     
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
         (invertible-p x p))
        (equal (mod (* (inv x p) x a) p)
               (mod a p)))
       :otf-flg t
       :hints (("Goal" :in-theory '(modular-inverse)
                :use (:instance equal-mod-product-reduction-1
                                (a (* (inv x p) x))
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
       (invertible-p x p)
       (natp p)
       (equal (mod (* x a) p) (mod (* x b) p)))
      (equal (mod a p) (mod b p)))
     :hints (("Goal" :in-theory '(inv-product-assoc integerp-inv)
              :use (:instance equal-mod-product-reduction-1
                              (a (* x a))
                              (b (* x b))
                              (x (inv x p)))))))

  (defthm equal-mod-product-reduction
    (implies
     (and
      (integerp x)
      (integerp a)
      (integerp b)
      (invertible-p x p)
      (natp p))
     (equal (equal (mod (* a x) p) (mod (* b x) p))
            (equal (mod a p) (mod b p))))
    :hints (("Goal" :in-theory (disable mod)
             :use (equal-mod-product-reduction-2
                   equal-mod-product-reduction-1))))
   
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm mod-rule-1
    (implies
     (and
      (integerp z)
      (integerp r)
      (integerp p))
     (equal (mod (+ z (- (* p r))) p)
            (mod z p))))

  (defthm mod-rule-2
    (equal (MOD (* X (- Z)) P)
           (mod (* (- x) z) p)))

  )

(defun posfix (x)
  (if (posp x) x 1))

(defun nzifix (x)
  (let ((x (ifix x)))
    (if (equal x 0) 1 x)))

(defthm posp-posfix
  (posp (posfix x))
  :rule-classes ((:forward-chaining :trigger-terms ((posfix x)))))

(defthm natp-nfix
  (natp (nfix x))
  :rule-classes ((:forward-chaining :trigger-terms ((nfix x)))))

(defthm integerp-ifix
  (integerp (ifix x))
  :rule-classes ((:forward-chaining :trigger-terms ((ifix x)))))

(defthm integerp-nzifix
  (integerp (nzifix x))
  :rule-classes ((:forward-chaining :trigger-terms ((nzifix x)))))

(defthm not-zero-nzifix
  (not (equal (nzifix x) 0))
  :rule-classes ((:forward-chaining :trigger-terms ((nzifix x)))))

(defthm positive-abs
  (<= 0 (abs x))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((abs x)))))

(defthm posp-implies-natp
  (implies
   (posp x)
   (natp x))
  :rule-classes (:forward-chaining))

(defthm posfix-idempotent
  (implies
   (posp x)
   (equal (posfix x) x)))

(defthm nfix-idempotent
  (implies
   (natp x)
   (equal (nfix x) x)))

(defthm ifix-idempotent
  (implies
   (integerp x)
   (equal (ifix x) x)))

(defthm nzifix-idempotent
  (implies
   (and
    (integerp x)
    (not (equal x 0)))
   (equal (nzifix x) x)))

(defthm abs-idempotent
  (implies
   (<= 0 x)
   (equal (abs x) x)))

(defthm natp-abs
  (implies
   (integerp x)
   (natp (abs x)))
  :rule-classes ((:forward-chaining :trigger-terms ((abs x)))))

(in-theory (disable nzifix ifix nfix posp posfix abs))

(defun smod (v p)
  (let ((v (ifix v))
        (p (posfix p)))
    (let ((x (mod v p)))
      (if (<= (* 2 x) p) x
        (- (- p x))))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm integerp-smod
    (integerp (smod v p))
    :rule-classes (:rewrite
                   (:forward-chaining :trigger-terms ((smod v p)))))

  (defthm smod-mod
    (implies
     (posp p)
     (equal (mod (smod v p) p)
            (mod (ifix v) p))))
  
  )

(defun sign (x)
  (if (< (ifix x) 0) -1 1))

(defun mabs (v p)
  (abs (smod v p)))

(defthm integerp-mabs
  (integerp (mabs v p))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((mabs v p)))))

(defthm positive-mabs
  (<= 0 (mabs v p))
  :rule-classes (:rewrite 
                 :linear
                 (:forward-chaining :trigger-terms ((mabs v p)))))

(defun msign (v p)
  (sign (smod v p)))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm mabs-positive
    (<= 0 (mabs v p))
    :rule-classes (:linear))
  
  )

(in-theory (disable mabs))

;; You want to subtract mod from N to give a smaller number.

(defun diff (n m)
  (- n m))

(defun pdiv (n d)
  (let ((d (nzifix d))
        (n (ifix n)))
    (let ((n (abs n))
          (d (abs d)))
      (let ((m (mod n d)))
        (/ (diff n m) d)))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm inner
    (implies
     (and (natp x) (natp p))
     (<= (mod x p) x))
    :hints (("Goal" :in-theory (enable mod)))
    :rule-classes :linear)
  
  (defthm non-negative-pdiv
    (<= 0 (pdiv n d))
    :hints (("Goal" :in-theory (disable mod DISTRIBUTIVITY)))
    :rule-classes (:linear
                   (:forward-chaining :trigger-terms ((pdiv n d)))))

  (local
   (defthm diff-as-product
     (equal (diff a (mod a x))
            (* x (floor a x)))))

  (defthm integerp-pdiv
    (integerp (pdiv n d))
    :hints (("Goal" :in-theory (disable diff)))
    :rule-classes (:rewrite
                   (:forward-chaining :trigger-terms ((pdiv n d)))))
 
  )

(defun pmod (n d)
  (let ((d (nzifix d))
        (n (ifix n)))
    (let ((s (sign n)))
      (let ((n (abs n))
            (d (abs d)))
        (* s (mod n d))))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm pmod-sign-property-1
    (implies
     (and (integerp p) (<= 0 p))
     (<= 0 (pmod p n)))
    :rule-classes (:rewrite :linear))

  (defthm pmod-sign-property-2
    (implies
     (and (integerp p) (< p 0))
     (<= (pmod p n) 0))
    :rule-classes (:rewrite :linear))

  (defthm pmod-less-prop-0
    (implies
     (and
      (integerp n)
      (<= n 0))
     (<= (+ n (pmod p n)) 0))
    :hints (("Goal" :in-theory (enable abs)
             :cases ((equal n 0)))))

  (defthm pmod-greater-prop-0
    (implies
     (and
      (integerp p)
      (<= 0 p))
     (<= 0 (+ p (pmod n p))))
    :hints (("Goal" :in-theory (enable abs)
             :cases ((equal p 0)))))

  (defthm integerp-pmod
    (integerp (pmod n d))
    :rule-classes (:rewrite
                   (:forward-chaining :trigger-terms ((pdiv n d)))))
 
  )
;;  N .........0.....P

;; Even better: I think "mod" tells you all you need to know about the
;; result.  ie: it tells you how to "split" the (smaller) denominator.
;; But how do you know which one should be negative? It does not, on
;; the other hand, tell you the quotient you need to accumulate.

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm pdiv-pmod-relation
    (implies
     (and
      (integerp L)
      (integerp S)
      (not (equal s 0)))
     (equal (* S (pdiv L S))
            (* (sign s) (sign L) (- L (pmod L S)))))
    :hints (("Goal" :in-theory (enable abs))))

  (local
   (defthm pdiv-pmod-relation-test
     (implies
      (and
       (integerp L)
       (integerp S)
       (not (equal s 0)))
      (equal (pmod L S)
             (- L (* (sign s) (sign L) (pdiv L S) S))))
     :hints (("Goal" :in-theory (enable abs)))))
 
  )

(in-theory (disable mod pdiv pmod))

(include-book "coi/util/mv-nth" :dir :system)

;; You are going to add the smaller to the larger .. because they are
;; negations of each other.

(defun minBstep (k N m P)
  (met ((k S m L) (if (< (abs N) (abs P)) (mv k N m P)
                    (mv m P k N)))
    (let ((q (pdiv L S))
          (sign (* (sign L) (sign S))))
      (let ((L (- L (* q sign S)))
            (m (+ m (* q k)))
            (S (- L (* (1+ q) sign S)))
            (k (+ m (* (1+ q) k))))
        (if (< S L) (mv k S m L)
          (mv m L k S))))))

(defun minBstepInvariant(k N m P x Q)
  (and
   (natp x)
   (posp Q)
   (posp k)
   (posp m)
   (integerp N)
   (integerp P)
   (<= N 0)
   (<= 0 P)
   (equal (mod (* k x) Q) (mod N Q))
   (equal (mod (* m x) Q) (mod P Q))))
  
(encapsulate
    ()

  (local (include-book "coi/nary/nary-mod" :dir :system))
  
  (encapsulate
      ()
    
    (local (IN-THEORY (ENABLE NARY::MOD-RULES)))

    (defthmd rewrite-3-helper
      (implies
       (and
        (integerp kx)
        (integerp z)
        (integerp q)
        (equal (mod kx q)
               (mod n q))
        (integerp n))
       (equal (mod (* kx z) q)
              (mod (* n z) q)))
      :hints (("Goal" :in-theory (disable nary::mod-equiv
                                          NARY::OPEN-MOD-EQUIV-IN-CONCLUSION 
                                          mod))))

    )

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm rewrite-3
    (implies
     (and
      (integerp k)
      (integerp x)
      (integerp z)
      (integerp q)
      (equal (mod (* k x) q)
             (mod n q))
      (integerp n))
     (equal (mod (* k x z) q)
            (mod (* n z) q)))
    :hints (("Goal" :use (:instance rewrite-3-helper
                                    (kx (* k x))))))

  )
  
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm mod-less-than-modulus
    (implies
     (and
      (integerp v)
      (integerp q)
      (< 0 q))
     (< (mod v q) q)))
  
  (defthm sum-less-than-double
    (implies
     (and
      (integerp a)
      (integerp b)
      (integerp x)
      (< 0 x)
      (< a x)
      (< b x))
     (< (+ a b) (* 2 x))))
  
  (defthm minBstep-property
    (implies
     (and
      (< 0 P)
      (< N 0)
      (minBstepInvariant k N m P x Q))
     (minBstepInvariant (val 0 (minBstep k N m P))
                        (val 1 (minBstep k N m P))
                        (val 2 (minBstep k N m P))
                        (val 3 (minBstep k N m P))
                        x
                        Q)))
  
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthmd mabs-plus-lt-reduction
    (implies
     (and
      (posp q)
      (integerp n)
      (integerp p)
      )
     (iff (< (mabs (+ n p) q) (mabs n q))
          ;; If p is zero, this is uninteresting.
          (if (equal (smod p q) 0) nil
            ;; This is also just boring.
            (if (equal (+ (smod N Q) (smod P Q)) 0) (< 0 (mabs n q))
              ;; Are p and n of opposite sign?
              (if (not (equal (msign p q) (msign n q)))
                  ;; The usual case.
                  (if (<= (mabs p q) (mabs n q)) t
                    ;; We can change n's sign.
                    (< (mabs p q) (* 2 (mabs n q))))
                ;; If n is in the 1st quandrant, forget it.
                (if (<= (* 4 (mabs n q)) q) nil
                  ;; Is it big enough to lap into the 3rd quadrant?
                  (< (- q (mabs n q)) (+ (mabs n q) (mabs p q)))))))))
    :otf-flg t
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (posp abs mabs smod) nil))))

  (defthmd mabs-plus-lte-reduction
    (implies
     (and
      (posp q)
      (integerp n)
      (integerp p)
      )
     (iff (< (mabs n q) (mabs (+ n p) q))
          (not
           ;; If p is zero, this is uninteresting.
           (if (equal (smod p q) 0) t
             ;; This is also just boring.
             (if (equal (+ (smod N Q) (smod P Q)) 0) (<= 0 (mabs n q))
               ;; Are p and n of opposite sign?
               (if (not (equal (msign p q) (msign n q)))
                   ;; The usual case.
                   (if (<= (mabs p q) (mabs n q)) t
                     ;; We can change n's sign.
                     (<= (mabs p q) (* 2 (mabs n q))))
                 ;; If n is in the 1st quandrant, forget it.
                 (if (< (* 4 (mabs n q)) q) nil
                   ;; Is it big enough to lap into the 3rd quadrant?
                   (<= (- q (mabs n q)) (+ (mabs n q) (mabs p q))))))))))
    :otf-flg t
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (posp abs mabs smod) nil))))

  )

(local (include-book "arithmetic-5/top" :dir :system))

(defthm mabs-less-than-sum
  (implies
   (and
    (natp kx)
    (natp ex)
    (natp mx)
    (posp q)
    (not (equal (msign kx q) (msign mx q)))
    (equal (msign kx q) (msign ex q))
    (< (mabs kx q) (mabs mx q))
    (< (mabs ex q) (mabs mx q))
    (< (mabs kx q) (mabs ex q))
    )
   (< (mabs (+ ex mx) q)
      (mabs (+ kx mx) q)))
  :hints (("Goal" :in-theory (enable abs mabs msign smod))))


(defthmd smod-plus-msign-preservation
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (< (* 4 (mabs (* m x) q)) q)
    (< (* 4 (mabs (* k x) q)) q)
    (not (equal (msign (* k x) q)
                (msign (* m x) q)))
    (< (mabs (* k x) q) (mabs (* m x) q))
    )
   (equal (msign (* (+ m k) x) q)
          (msign (* m x) q)))
  :hints (("Goal" :in-theory (enable smod abs mabs))))

(defthmd smod-plus-msign-difference
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (< (* 4 (mabs (* m x) q)) q)
    ;;(< (* 4 (mabs (* k x) q)) q)
    (< (mabs (* (+ m k) x) q) (mabs (* m x) q))
    )
   (not (equal (msign (* k x) q)
               (msign (* m x) q))))
  :hints (("Goal" :in-theory (enable smod abs mabs))))

(defund sign-smallest-coefficient-p (n k x q)
  (let ((n (nfix n))
        (k (nfix k))
        (x (nfix x))
        (q (posfix q)))
    (implies
     (and
      (equal (msign (* n x) q)
             (msign (* k x) q))
      (< (mabs (* n x) q)
         (mabs (* k x) q)))
     (< k n))))

(defun-sk sign-smallest-coefficient (k x q)
  (forall (n) (sign-smallest-coefficient-p n k x q)))

(in-theory (disable sign-smallest-coefficient))

(defthmd sign-smallest-coefficient-implication
  (implies
   (and
    (natp n)
    (natp k)
    (natp x)
    (posp q)
    (sign-smallest-coefficient k x q))
   (sign-smallest-coefficient-p n k x q))
  :hints (("Goal" :use sign-smallest-coefficient-necc)))

;;
;;       |< m
;;       |
;;       |<m+k
;;     e>|<m+e = n
;;     k>|
;;       |
;; ------+------
;;
;; (n < k) => ((||n|| > ||k||) or (n == m))
;; (n < m) => ((||n|| > ||m||) or (n == k))
;;
(defund smallest-coefficient-pair-p (n k m x q)
  (let ((n (nfix n))
        (k (nfix k))
        (m (nfix m))
        (x (nfix x))
        (q (posfix q)))
    (implies
     (and (not (equal (smod (* n x) q) 0))
          (< (mabs (* n x) q) (+ (mabs (* k x) q) (mabs (* m x) q))))
     (and (implies (equal (msign (* n x) q) (msign (* k x) q)) (< k n))
          (implies (equal (msign (* n x) q) (msign (* m x) q)) (< m n))))))

(defun-sk smallest-coefficient-pair (k m x q)
  (forall (n) (smallest-coefficient-pair-p n k m x q)))

(in-theory (disable smallest-coefficient-pair))

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

(defthm smod-commutes-plus-small
  (implies
   (and
    (integerp a)
    (integerp b)
    (posp q)
    (< (* 4 (mabs a q)) q)
    (< (* 4 (mabs b q)) q))
   (equal (smod (+ a b) q)
          (+ (smod a q)
             (smod b q))))
  :hints (("Goal" :in-theory (enable abs mabs))))

(defthm smod-commutes-plus-different
  (implies
   (and
    (integerp a)
    (integerp b)
    (posp q)
    (not (equal (msign a q) (msign b q))))
   (equal (smod (+ a b) q)
          (+ (smod a q)
             (smod b q))))
  :hints (("Goal" :in-theory (enable abs mabs))))

(defthm smod-commutes-multiplication
  (implies
   (and
    (integerp a)
    (posp q)
    (force (< (* 4 (mabs a q)) q)))
   (equal (smod (* 2 a) q)
          (+ (smod a q)
             (smod a q))))
  :hints (("Goal" :use (:instance smod-commutes-plus-small
                                  (b a)))
           ))

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

(in-theory (disable smod))

(defun delta (n m)
  (- (ifix n) (ifix m)))

(defthm integerp-delta
  (integerp (delta n m))
  :rule-classes ((:forward-chaining :trigger-terms ((delta n m)))))

(defthm linear-delta
  (implies
   (and
    (integerp m)
    (integerp n)
    (<= 0 m)
    (< m n))
   (and (< 0 (delta n m))
        (<= (delta n m) n)))
  :rule-classes (:linear))

(in-theory (disable delta))

(defun ith (n x)
  (if (not (consp x)) nil
    (if (zp n) (car x)
      (ith (1- n) (cdr x)))))

(defun gspec (id)
  (let ((spec (ith 1 id)))
    (and (equal (ith 0 spec) 2)
         (equal (ith 1 spec) 3))))

(defun not-hide (clause)
  (if (not (consp clause)) nil
    (or (equal (ith 0 (car clause)) 'hide)
        (not-hide (cdr clause)))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthmd helper
     (implies
      (and
       (integerp x)
       (integerp y)
       (posp q)
       (equal (mod a q)
              (mod b q)))
      (equal (mod (* a x) q)
             (mod (* b x) q)))))
     
  (defthm smod-of-mod
    (implies
     (and
      (integerp x)
      (integerp y)
      (posp q))
     (equal (smod (* x (mod y q)) q)
            (smod (* x y) q)))
    :hints (("Goal" :in-theory (enable smod)
             :use (:instance helper
                             (x x)
                             (a (mod y q))
                             (b y)))))
  
  )

(defthm mabs-of-mod
  (implies
   (and
    (integerp x)
    (integerp y)
    (posp q))
   (equal (mabs (* x (mod y q)) q)
          (mabs (* x y) q)))
  :hints (("Goal" :in-theory (enable mabs))))
   

(defthm bound-k-m-above
  (implies
   (and
    (smallest-coefficient-pair k m x q)
    (not (equal (smod (* k x) q) 0))
    (not (equal (smod (* m x) q) 0))
    (not (equal (mod k q) (mod m q)))
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    )
   (and (< k q)
        (< m q)))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal" :in-theory (enable mabs abs smallest-coefficient-pair-p)
           :use ((:instance smallest-coefficient-pair-implication
                            (n (mod m q)))
                 (:instance smallest-coefficient-pair-implication
                            (n (mod k q)))))))

(defthm equal-smod-product-reduction
  (implies
   (and
    (posp q)
    (natp n)
    (natp x)
    (invertible-p x q)
    (natp k))
   (equal (equal (smod (* n x) q)
                 (smod (* k x) q))
          (equal (mod n q)
                 (mod k q))))
  :hints (("Goal" :in-theory (e/d (smod) (mod)))))
 
(defthm equal-delta-reduction
  (implies
   (and (integerp n)
        (integerp k))
   (equal (equal (delta n k) k)
          (equal n (* 2 k))))
  :hints (("Goal" :in-theory (enable delta))))

(defstub pred (x) nil)

(encapsulate
    ()

  (local
   (defthm equal-smod-zero-mod
     (implies
      (and
       (integerp k)
       (integerp x)
       (invertible-p x q)
       (posp q))
      (iff (equal (smod (* k x) q) (smod (* 0 x) q))
           (equal (mod k q) (mod 0 q))))
     :hints (("Goal" :in-theory (e/d (posfix smod) (mod))
              :use (:instance equal-mod-product-reduction
                              (x x)
                              (a k)
                              (b 0)
                              (p q))))))

  (defthmd equal-smod-zero-x
    (implies
     (and
      (integerp k)
      (integerp x)
      (invertible-p x q)
      (posp q))
     (iff (equal (smod (* k x) q) 0)
          (equal (mod k q) 0)))
    :hints (("Goal" :in-theory (enable smod mod)
             :use equal-smod-zero-mod)))

  )

(include-book "coi/util/good-rewrite-order" :dir :system)
  
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd smod-mod-congruence
    (implies
     (and
      (equal (mod n q) (mod m q))
      (syntaxp (good-rewrite-order n m))
      (integerp n)
      (integerp m)
      (integerp x)
      (posp q)
      )
     (equal (smod (* n x) q)
            (smod (* m x) q)))
    :hints (("Goal" :in-theory (enable smod))))

  )

(defthm set-of-smallest-coefficients-small-step-1
  (implies
   (and
    (hide (pred n))
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (invertible-p x q)
    ;;(sign-smallest-coefficient k x q)
    ;;(sign-smallest-coefficient m x q)
    (smallest-coefficient-pair k m x q)
    (not (equal (mod k q) (mod m q)))
    (< (* 4 (mabs (* m x) q)) q)
    (< (* 4 (mabs (* k x) q)) q)
    (not (equal (msign (* m x) q) (msign (* k x) q)))
    ;;(< (smod (* k x) q) 0)
    ;;(< 0 (smod (* m x) q))
    (natp N)
    ;;
    (< (mabs (* k x) q) (mabs (* m x) q))
    )
   (smallest-coefficient-pair-p n k (+ m k) x q))
  :otf-flg t
  :hints (("Goal" :do-not-induct t :in-theory (enable nfix abs mabs smallest-coefficient-pair-p)
           :use (
                 bound-k-m-above
                 smallest-coefficient-pair-implication)
           )
          (and stable-under-simplificationp
               '(:use ((:instance smallest-coefficient-pair-implication
                                  (n (delta n m))))))
          (and stable-under-simplificationp
               '(:use ((:instance smallest-coefficient-pair-implication
                                  (n (delta n k))))))
          (and stable-under-simplificationp
               #+joe
               (not 
                (and
                 (equal (ith 0 (ith 1 id)) 2)
                 (or (equal (ith 1 (ith 1 id)) 20)
                     (equal (ith 1 (ith 1 id)) 19))))
               '(:cases ((< n q))
                        :expand (:free (x) (hide x))
                        :in-theory (enable smod-mod-congruence
                                           delta abs mabs)))
          ;;
          ;; You have done all you can .. in the case that N = 2k, 
          ;; you are screwed.
          ;;
          ;; Both failure cases in this proof are degenerate values
          ;; of N: 
          ;;
          ;; ((delta n k) = K)
          ;; - I'm not sure about this one .. 
          ;;
          ;; (EQUAL (SMOD (* X (DELTA N K)) Q) 0)
          ;; - this needs to imply (n != k)
          ;;
          #+joe
          ("Subgoal 2.19" :expand ((delta n k)
                                   (delta n m))
           :cases ((< n q)))
          #+joe
          ("Subgoal 2.20" ;;:in-theory (enable test2 delta)
           :cases ((< (+ m k) (* 2 k))))
          #+joe
          (and stable-under-simplificationp
               '(:in-theory (enable test2 delta)))
          ;;
          ;;       |
          ;;       |
          ;;       |< m
          ;;       |
          ;;       |< m+k
          ;; N=2k >|
          ;;       |
          ;;     k>|
          ;;       |
          ;; ------+------
          ;;
          ;; So what is the problem?  Well, how does 
          ;;
          ;; 
          ;;
          ;; 0         k     m    N=2k                       Q
          ;; |---------^-----^----^------------------------^----
          ;;
          ;; (IMPLIES (AND (< (SMOD (* X (DELTA (* 2 K) M)) Q) 0)
          ;;               (<= (+ (SMOD (* M X) Q)
          ;;                      (SMOD (* X (DELTA (* 2 K) M)) Q))
          ;;                   (SMOD (* K X) Q))
          ;;               (< K Q)
          ;;               (< M Q)
          ;;               (< M (* 2 K))
          ;;               (INTEGERP K)
          ;;               (INTEGERP M)
          ;;               (INTEGERP X)
          ;;               (<= 0 X)
          ;;               (INTEGERP Q)
          ;;               (< 0 Q)
          ;;               (INVERTIBLE-P X Q)
          ;;               (SMALLEST-COEFFICIENT-PAIR K M X Q)
          ;;               (NOT (EQUAL K M))
          ;;               (< (* 4 (SMOD (* M X) Q)) Q)
          ;;               (< (* -4 (SMOD (* K X) Q)) Q)
          ;;               (< 0 (SMOD (* M X) Q))
          ;;               (INTEGERP (* 2 K))
          ;;               (< 0 K)
          ;;               (< (- (SMOD (* K X) Q))
          ;;                  (SMOD (* M X) Q))
          ;;               (NOT (EQUAL (SMOD (* K X) Q) 0))
          ;;               (<= (SMOD (* K X) Q) 0)
          ;;               (<= 0 (+ (SMOD (* K X) Q) (SMOD (* M X) Q)))
          ;;               (< (* -2 (SMOD (* K X) Q))
          ;;                  (SMOD (* M X) Q)))
          ;;          (< M K))
          ))

#|
          ;;
          (and stable-under-simplificationp
               (not (gspec id))
               '(:in-theory (enable delta abs mabs)))
          (and stable-under-simplificationp
               (gspec id)
               '(:cases ((hide 
                          (rewrite-equiv 
                           (equal (smod (* n x) q) 
                                  (+ (smod (* m x) q) (smod (* (delta n m) x) q))))))))
          (and (not-hide clause)
               `(:expand (:free (x) (hide x))
                         :in-theory (enable abs mabs delta)))
          ;;
          ;; This subgoal says it is sufficient to be less than 2*|m|
          ;;
          ;; ie: the following is implicitly true:
          ;;
          ;; (<= (+ (mabs (* m x) q) (mabs (* k x) q)) (mabs (* x (delta n m)) q))
          ;;
          ;;       |< 2*m
          ;;       |
          ;;     d>|
          ;;       |< |m|+|k|
          ;;       |
          ;;       |
          ;;       |< m
          ;;       |
          ;;       |<m+k
          ;;       |
          ;;   m+d>|
          ;;     k>|
          ;;       |
          ;; ------+------
          ;;
          ;; Subgoal 2.3.1''
          ;; (IMPLIES (AND (HIDE (REWRITE-EQUIV (EQUAL (SMOD (* N X) Q)
          ;;                                           (+ (SMOD (* M X) Q)
          ;;                                              (SMOD (* (DELTA N M) X) Q)))))
          ;;               (< (SMOD (* X (DELTA N M)) Q) 0)
          ;;               (< (+ (SMOD (* M X) Q)
          ;;                     (SMOD (* X (DELTA N M)) Q))
          ;;                  0)
          ;;               (<= (+ (SMOD (* M X) Q)
          ;;                      (SMOD (* X (DELTA N M)) Q))
          ;;                   (SMOD (* K X) Q))
          ;;               (< K N)
          ;;               (< M N)
          ;;               (INTEGERP K)
          ;;               (<= 0 K)
          ;;               (INTEGERP M)
          ;;               (<= 0 M)
          ;;               (INTEGERP X)
          ;;               (<= 0 X)
          ;;               (POSP Q)
          ;;               (SMALLEST-COEFFICIENT-PAIR K M X Q)
          ;;               (< (* 4 (SMOD (* M X) Q)) Q)
          ;;               (< (* -4 (SMOD (* K X) Q)) Q)
          ;;               (< (SMOD (* K X) Q) 0)
          ;;               (< 0 (SMOD (* M X) Q))
          ;;               (INTEGERP N)
          ;;               (<= 0 N)
          ;;               (< (- (SMOD (* K X) Q))
          ;;                  (SMOD (* M X) Q))
          ;;               (NOT (EQUAL N K))
          ;;               (NOT (EQUAL N (+ K M)))
          ;;               (<= 0 (+ (SMOD (* K X) Q) (SMOD (* M X) Q)))
          ;;               (< (- (SMOD (* X (DELTA N M)) Q))
          ;;                  (* 2 (SMOD (* M X) Q))))
          ;;          (< (+ K M) N))
          ;;
          ;; Seems like we want to talk about |m+d| relative to |k| ..
          ;;
          (and stable-under-simplificationp
               '(:use (:instance smallest-coefficient-pair-implication
                                 (n (delta n k)))))
          (and stable-under-simplificationp
               '(:expand (:free (x) (hide x))
                         :in-theory (enable delta abs mabs)))
          ))
#+joe((
          (and stable-under-simplificationp
               `(:cases ((<= (mabs (* x (+ m (delta n m))) q)
                             (mabs (* x (+ m          k )) q)))))
          (and stable-under-simplificationp
               (let ((spec (ith 1 id)))
                 (and (equal (ith 0 spec) 2)
                      (equal (ith 1 spec) 3)
                      (equal (ith 2 spec) 1)
                      ;;
                      (equal (ith 4 spec) 1)
                      ))
               '(:expand (:Free (x) (hide x))
                         :in-theory (enable delta abs mabs)))
          ;;
          ;;
          ))
|#
