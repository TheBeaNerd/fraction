(in-package "ACL2")

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

#+joe
(defthmd rewrite-value
  (implies
   (and
    (equal (smod p q) v)
    (integerp p)
    (integerp q)
    (integerp v)
    (integerp n)
    (equal z (smod (+ n v) q))
    (syntaxp (not (equal z `(smod (+ ,n ,p) ,q)))))
   (equal (smod (+ n p) q)
          z)))

#+joe
(encapsulate
    ()

  (local (include-book "coi/nary/nary-mod" :dir :system))
  (local (IN-THEORY (ENABLE NARY::MOD-RULES)))
  (defthm smod-smod
    (implies
     (integerp p)
     (equal (smod (+ n (smod p q)) q)
            (smod (+ n p) q)))
    :hints (("Goal" :in-theory (enable ifix))))

  )

#+joe
(defthm negative-lower-bounds
  (implies
   (and
    (< (smod n q) 0)
    (natp q))
   (< (- q) (* 2 (smod n q))))
  :hints (("Goal" :in-theory (enable posfix)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((smod n q)))))

#+joe
(defthm positive-upper-bounds
  (implies
   (and
    (< 0 (smod n q))
    (natp q))
   (and
    (< (smod n q) q)
    (<= (* 2 (smod n q)) q)))
  :hints (("Goal" :in-theory (enable posfix)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((smod n q)))))
  
#+joe
(defthm alt-smod-fact
  (IMPLIES (AND (INTEGERP Q)
                (< 0 Q)
                (INTEGERP N)
                (INTEGERP P)
                (< (SMOD (+ N P) Q) 0)
                (< (SMOD N Q) 0)
                (< (SMOD P Q) 0))
           (< (SMOD (+ N P) Q) (SMOD N Q)))
  :rule-classes (:linear))

#+joe
(defthm same-msign-less-than-reduction
  (implies
   (and
    (posp q)
    (integerp n)
    (integerp p)
    )
   (iff (and (< (mabs (+ n p) q) (mabs n q))
             (equal (msign (+ n p) q) (msign n q)))
        (if (equal (mabs n q) (mabs p q))
            (and (equal (+ (mod n q) (mod p q)) q)
                 (< 0 (mabs n q))
                 (equal 1 (msign n q)))
          (and (not (equal (mod p q) 0))
               (not (equal (msign n q) (msign p q)))
               (< (mabs p q) (mabs n q))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (posp abs mabs) (smod)))))

#+joe
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  ;; Can you make a smaller value (of the same sign) from n?
  ;; 
  
  ;; So .. it is impossible to make a new value with the
  ;; same sign except under exceptional conditions.
  
  (defthm same-msign-lt-reduction
    (implies
     (and
      (posp q)
      (integerp n)
      (integerp p)
      )
     (iff (and (< (mabs (+ n p) q) (mabs n q))
               (equal (msign (+ n p) q) (msign n q)))
          (if (equal (mabs n q) (mabs p q))
              (and (equal (+ (mod n q) (mod p q)) q)
                   (< 0 (mabs n q))
                   (equal 1 (msign n q)))
            (and (not (equal (mod p q) 0))
                 (not (equal (msign n q) (msign p q)))
                 (< (mabs p q) (mabs n q))))))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable posp abs mabs))))

  (defthm standard-differential-reduction
    (implies
     (and
      (posp q)
      (integerp n)
      (integerp p)
      (not (equal (msign n q) (msign p q)))
      (< (mabs p q) (mabs n q))
      )
     (iff (< (mabs (+ n p) q) (mabs n q))
          (not (equal (mod p q) 0))))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable posp mabs abs))))

  )


;; How about making values with the opposite sign?
;; That seems like a challenging part of the proof.

;; Well, for sufficiently small values it is, in fact, not possible.

;; 0..............x..............|

(defun smallest-coefficient-p (q k x p)
  (implies
   (and 
    (equal (msign (* k x) p) 
           (msign (* q x) p))
    (< (mabs (* q x) p)
       (mabs (* k x) p)))
   (< k q)))

(in-theory (disable smallest-coefficient-p))

(defun-sk smallest-coefficient (k x p)
  (forall (q) (smallest-coefficient-p (nfix q) (nfix k) (nfix x) (posfix p))))

(in-theory (disable smallest-coefficient))

(defthmd smallest-coefficient-implication
  (implies
   (and
    (natp q)
    (smallest-coefficient k x p)
    (natp k)
    (natp x)
    (posp p))
   (smallest-coefficient-p q k x p))
  :hints (("Goal" :use (:instance smallest-coefficient-necc))))

(local (include-book "arithmetic-5/top" :dir :system))

(in-theory (disable smod))

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


(defthm smod-plus-msign-preservation
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

#+dag
(defthm set-of-smallest-coefficients-small-step-1
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (SMALLEST-COEFFICIENT K X Q)
    (SMALLEST-COEFFICIENT M X Q)
    (< (* 4 (mabs (* m x) q)) q)
    (< (* 4 (mabs (* k x) q)) q)
    (< (smod (* k x) q) 0)
    (< 0 (smod (* m x) q))
    (natp N)
    ;;
    (< (mabs (* k x) q) (mabs (* m x) q))
    )
   (smallest-coefficient-p N (+ m k) x q))
  :otf-flg t
  :hints (("Goal" :use smod-plus-msign-preservation
           :cases ((< (MABS (+ (* K X) (* M X)) Q)
                      (MABS (* M X) Q))))
          ("Subgoal 2" :use (:instance mabs-plus-lt-reduction
                                       (q q)
                                       (n (* M X))
                                       (p (* K X))))
          (and stable-under-simplificationp
               '(:in-theory (enable smallest-coefficient-p)))
          (and stable-under-simplificationp
               '(:cases ((<= n m))))
          ("Subgoal 1.1" ;;:in-theory (disable smallest-coefficient-p)
           :use (:instance smallest-coefficient-implication
                           (q n)
                           (k m)
                           (x x)
                           (p q)
                           )
           )
          (and stable-under-simplificationp
               '(:cases ((equal (msign (* k x) q) (msign (* (- n m) x) q)))))

          ("Subgoal 1.2.1" ;; (- n m) has same sign as k
           :use (
                 (:instance smallest-coefficient-implication
                            (q (- n m))
                            (k k)
                            (x x)
                            (p q)
                            )
                 ))
          ;; Same sign as k
          ;; ("Subgoal 1.1" :cases ((< n k)))
          ;; ("Subgoal 1.1.1" :use ((:instance smallest-coefficient-implication
          ;;                                   (q n)
          ;;                                   (x x)
          ;;                                   (p q)
          ;;                                   (k k)
          ;;                                   )
          ;;                        (:instance mabs-plus-lte-reduction
          ;;                                   (q q)
          ;;                                   (n (* m x))
          ;;                                   (p (* k x))
          ;;                                   )
          ;;                        ))
          ))
