(in-package "ACL2")

(include-book "smallest-coefficient-step")
(include-book "smallest-coefficient-init")

;; (defun good-coefficient (k q)
;;   (and 
;;    (posp k)
;;    (< k q)))

;; k*x =  v
;; m*x = -v

;; i*x =  1

;; (i*v)*x = v

;; i*v = k
;; i*


;; Given that x has a unique inverse, I, and negative inverse, J ..
;;
;; I think you can show that (J,I) are (smallest-coefficient-pair-p J I m x q)
;;
;; You may then need to prove the inverse of your 'step' formula.
;;
;; From that you can deducer that, if v is not 1, then (k,m) are not smallest-coefficient-pair-p.
;;

;;
;; k -v | v  m
;;      |
;; J -1 | 1  I
;;

;;
;; If (k = -m) either ( | (* k x) % q | == 1 ) or k,m is not a minimal pair.
;;
(defun all-minimal-pairs (k m x q)
  (declare (xargs :hints (("Goal" :in-theory (enable posfix nfix)))
                  :measure (+ (nfix (- (posfix q) (nfix k)))
                              (nfix (- (posfix q) (nfix m))))))
  (let ((k (nfix k))
        (m (nfix m))
        (x (nfix x))
        (q (posfix q)))
    (if (or (equal k 0) (equal m 0)) nil
      (if (or (<= q k) (<= q m)) nil
        (if (< (mabs (* k x) q) (mabs (* m x) q))
            (cons (list k m) (all-minimal-pairs k (+ k m) x q))
          (if (< (mabs (* m x) q) (mabs (* k x) q))
              (cons (list k m) (all-minimal-pairs (+ k m) m x q))
            ;;
            ;; k = (- m) % p
            ;;
            ;; Also .. I think (mabs (* k x) q) == 1
            ;;
            ;; Unfortunately, proving this might require knowledge
            ;; about (gcd x q)
            ;;
            (list (list k m))))))))


(defun all-smallest-coefficient-pair-p (list x q)
  (if (not (consp list)) t
    (let ((x (nfix x))
          (q (posfix q)))
      (let ((km (car list)))
        (let ((k (nfix (car km)))
              (m (nfix (cadr km))))
          (and (smallest-coefficient-pair k m x q)
               (all-smallest-coefficient-pair-p (cdr list) x q)))))))

(defthm all-smallest-coefficient-pair-all-minimal-fractions
  (implies
   (and
    (posp q)
    (natp k)
    (natp m)
    (natp x)
    (generic-invertible-p x q)
    (not (equal (msign (* m x) q) (msign (* k x) q)))
    (smallest-coefficient-pair k m x q)
    )
   (all-smallest-coefficient-pair-p (all-minimal-pairs k m x q) x q))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable mabs abs)))))



(defun strip-k (list)
  (if (not (consp list)) nil
    (cons (nfix (car (car list)))
          (strip-k (cdr list)))))

(defun strip-m (list)
  (if (not (consp list)) nil
    (cons (nfix (cadr (car list)))
          (strip-m (cdr list)))))

(defun <-all (x list)
  (if (not (consp list)) t
    (and (< (nfix x) (nfix (car list)))
         (<-all x (cdr list)))))

(defthm <-all-k-all-minimal-pairs
  (implies
   (< (nfix z) (nfix k))
   (<-all z (strip-k (all-minimal-pairs k m x q)))))

(defthm <-all-m-all-minimal-pairs
  (implies
   (< (nfix z) (nfix m))
   (<-all z (strip-m (all-minimal-pairs k m x q)))))

(defun increasing-list (x list)
  (if (not (consp list)) t
    (if (= (nfix x) (nfix (car list)))
        (increasing-list x (cdr list))
      (<-all x list))))

(defthm increasing-list-k-all-minimal-pairs
  (implies
   (<= (nfix z) (nfix k))
   (increasing-list z (strip-k (all-minimal-pairs k m x q)))))

(defthm increasing-list-m-all-minimal-pairs
  (implies
   (<= (nfix z) (nfix m))
   (increasing-list z (strip-m (all-minimal-pairs k m x q)))))

(defun all-increasing-list (list)
  (if (not (consp list)) t
    (and (increasing-list (car list) (cdr list))
         (all-increasing-list (cdr list)))))

(defthm all-increasing-list-strip-k-all-minimal-pairs
  (and (all-increasing-list (strip-k (all-minimal-pairs k m x q)))
       (all-increasing-list (strip-m (all-minimal-pairs k m x q)))))

(defun one-bigger-than-both (k m list)
  (if (not (consp list)) t
    (or (and (equal (nfix k) (nfix (car (car list))))
             (< (nfix k) (nfix (cadr (car list))))
             (< (nfix m) (nfix (cadr (car list)))))
        (and (equal (nfix m) (nfix (cadr (car list))))
             (< (nfix k) (nfix (car (car list))))
             (< (nfix m) (nfix (car (car list))))))))

(defthm one-bigger-than-both-all-minimal-pairs
  (implies
   (and
    (posp k)
    (posp m))
   (and (one-bigger-than-both k m (all-minimal-pairs (+ k m) m x q))
        (one-bigger-than-both k m (all-minimal-pairs k (+ k m) x q))))
  :hints (("Goal" :expand ((all-minimal-pairs (+ k m) m x q)
                           (all-minimal-pairs k (+ k m) x q)))))
  
(defthm one-bigger-than-both-nil
  (one-bigger-than-both k m nil))

(in-theory (disable one-bigger-than-both))

(defun all-one-bigger-than-both (list)
  (if (not (consp list)) t
    (and (one-bigger-than-both (nfix (car (car list))) (nfix (cadr (car list))) (cdr list))
         (all-one-bigger-than-both (cdr list)))))

(defthm all-one-bigger-than-both-all-minimal-pairs
  (all-one-bigger-than-both (all-minimal-pairs k m x q)))

(defun pair-member-p (k m list)
  (if (not (consp list)) nil
    (or (and (equal (nfix k) (nfix (car  (car list))))
             (equal (nfix m) (nfix (cadr (car list)))))
        (pair-member-p k m (cdr list)))))

(defthm pair-member-all-smallest-coefficient-pair-p-implies-smallest-coefficient-pair
  (implies
   (and
    (natp x)
    (posp q)
    (natp k)
    (natp m)
    (all-smallest-coefficient-pair-p list x q)
    (pair-member-p k m list))
   (smallest-coefficient-pair k m x q)))

(defthm <-all-strip-k-implies-not-pair-member-p
  (implies
   (<-all k (strip-k list))
   (not (pair-member-p k m list))))

(defthm <-all-strip-m-implies-not-pair-member-p
  (implies
   (<-all m (strip-m list))
   (not (pair-member-p k m list))))

;; dag
;; (defthm <-all-strip-k-implies-not-pair-member-p
;;   (implies
;;    (and
;;     (< k b))
;;    (iff (pair-member-p k m (all-minimal-pairs a b x q))
;;         (and (equal k a)
;;              (equal m (+ b (* z k)))))))

;; (defaxiom equal-mabs-reduction
;;   (iff (equal (mabs (* m x) q)
;;               (mabs (* k x) q))
;;        (or (equal m k)
;;            (equal m (- q k)))))

;; ;; This theorem is important because it is the start of "we find all
;; ;; minimal fractions"
;; (defthm all-minimal-pairs-is-complete
;;   (implies
;;    (and
;;     (natp k)
;;     (natp m)
;;     (natp a)
;;     (natp b)
;;     (natp x)
;;     (posp q)
;;     (smallest-coefficient-pair k m x q)
;;     (smallest-coefficient-pair a b x q)
;;     (<= m a)
;;     (<= k b))
;;    (pair-member-p a b (all-minimal-pairs k m x q)))
;;   :hints (("Subgoal *1/25.1" :in-theory (enable SMALLEST-COEFFICIENT-PAIR-P)
;;            :use (:instance smallest-coefficient-pair-implication
;;                            (n b)))))



;; (defun minimal-pair-ordering-p (list)
;;   (if (not (consp list))

;; (defthm not-equal-msign-implies-not-equal-mabs
;;   (implies
;;    (and
;;     (natp k)
;;     (natp m)
;;     (natp x)
;;     (posp q)
;;     (< k q)
;;     (< m q)
;;     (not (equal (msign (* k x) q) (msign (* m x) q)))
;;     (equal (mabs (* k x) q) (mabs (* m x) q)))
;;    (equal (mabs (* (+ k m) x) q) 0))
;;   :hints (("Goal" :in-theory (enable abs mabs))))



;; (defthm
;;   (implies
;;    (and
;;     (<= (* k k) q)
;;     (<= (* m m) q)
;;     (<= q (* (smod (* k x) q) (smod (* k x) q)))
;;     (<= q (* (smod (* m x) q) (smod (* m x) q)))
;;     )
;;    ;; one will have both
;;    (at-least-one-small-fraction (all-minimal-fractions k m x q) q)))


;; Consider x, an invertiable integer mod M.  If D*x = N % M then x can
;; be expressed as the fraction N/D.  Clearly x has many fractional
;; representations.  In this paper we define a notion of minimal
;; fractions and show that we can compute the set of minimal fractions
;; for x.  Finally we prove that x can be expressed as a (possibly
;; negative) fraction whose integral components, N and D, are both less
;; than or equal to sqrt(M).

;; (defun good (x y q)
;;   (let ((sx (* x x))
;;         (sy (* y y)))
;;     (if (and (< sx q) (< sy q))
;;         (+ sx sy)
;;       (+ q sx sy))))

;; (skip-proofs
;; (defun min-fraction-rec (k n m p q)
;;   (declare (xargs :measure (nfix (+ n p))))
;; ;;  (prog2$
;; ;;   (cw "~p0" (list k n m p))
;;    (cond
;;     ((or (<= n 1)
;;          (<= p 1))
;;      (if (< (good n k q) (good p m q))
;;          (/ (- n) k)
;;        (/ p m)))
;;     ((< n p)
;;      (let ((np (- p n))
;;            (nm (+ m k)))
;;        (if (< (good p m q) (good np nm q))
;;            (if (< (good n k q) (good p m q))
;;                (/ (- n) k)
;;              (/ p m))
;;          (min-fraction-rec k n nm np q))))
;;     (t
;;      (let ((nn (- n p))
;;            (nk (+ k m)))
;;        (if (< (good n k q) (good nn nk q))
;;            (if (< (good n k q) (good p m q))
;;                (/ (- n) k)
;;              (/ p m))
;;          (min-fraction-rec nk nn m p q))))))
;; )

;; (defun posfix (x)
;;   (if (posp x) x 1))

;; (defun smod (v p)
;;   (let ((v (ifix v))
;;         (p (posfix p)))
;;     (let ((x (mod v p)))
;;       (if (<= (* 2 x) p) x
;;         (- (- p x))))))

;; ;; So it looks like we could use the following to initialize
;; ;; the fraction process ..
;; (defun min-fraction (v q)
;;   (let ((s (smod v q)))
;;     (if (< s 0) (min-fraction-rec 1 (- s) 0 q q)
;;       (min-fraction-rec 0 q 1 s q))))
      
;; (defun min-fractions (v q)
;;   (if (zp v) nil
;;     (cons (min-fraction v q)
;;           (min-fractions (1- v) q))))

;; (defun doit(q)
;;   (min-fractions (1- q) q))

(defthm s+-can-be-represented-in-terms-of-s-
  (implies
   (and
    (natp N)
    (natp s+)
    (natp s-)
    (equal s- (1- s+))
    (< N (* s+ s+))
    (< (* s- s-) N))
   (< (- N (* s+ s-)) s+))
  :rule-classes nil)

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun gcdx (n d)
    (declare (xargs :measure (+ (nfix n) (nfix d))
                    :hints (("Goal" :in-theory (enable nfix)))))
    (let ((n (nfix n))
          (d (nfix d)))
      (if (< n d) 
          (if (equal n 0) d
            (gcdx n (mod d n)))
        (if (equal d 0) n
          (gcdx d (mod n d))))))

  )

(defun-sk gcdx-implies-invertible-p ()
  (forall (x q) 
    (implies
     (equal (gcdx x q) 1)
     (generic-invertible-p x q))))

(defthm invertible-p-from-gcdx
  (implies
   (and
    (gcdx-implies-invertible-p)
    (equal (gcdx x q) 1))
   (generic-invertible-p x q))
  :hints (("Goal" :use gcdx-implies-invertible-p-necc))
  :rule-classes (:forward-chaining))

(defun mag (n d)
  (max n d))

(defun element (n1 d1 n2 d2)
  (list (list* n1 d1 (mag (abs n1) d1)) (list* n2 d2 (mag (abs n2) d2))))

;;(include-book "coi/defung/defung" :dir :system)

(defun minimal-fraction-list-rec (k m x q)
  (declare (xargs :measure (1+ (min (nfix (- (nfix q) (nfix k))) (nfix  (- (nfix q) (nfix m)))))
                  :hints (("Goal" :in-theory (enable nfix))))) ;;(declare (xargs :default-value (element 1 x 1 x)))
  (let ((k (nfix k))
        (m (nfix m))
        (q (nfix q)))
    (if (or (< q (+ k m)) (zp k) (zp m)) nil
      (let ((n (- (smod (* k x) q)))
            (p (smod (* m x) q)))
        (let ((element (element (- n) k p m)))
          (if (< n p)
              (let ((nm (+ k m)))
                (cons element (minimal-fraction-list-rec k nm x q)))
            (let ((nk (+ k m)))
              (cons element (minimal-fraction-list-rec nk m x q)))))))))

(defun minimal-fraction-list (x q)
  (let ((g (gcdx x q)))
    (if (not (equal g 1)) (list (element 0 1 0 1))
      (let ((x (smod x q)))
        (if (or (equal x 0) (equal x 1) (equal x -1)) (list (element x 1 x 1))
          (let ((c (smallest-coefficient 0 (mod x q) q)))
            (met ((k m x) (if (< x 0) (mv 1 c (+ q x)) (mv c 1 x)))
              (minimal-fraction-list-rec k m x q))))))))

(defun minimal-fractions-list-rec (x q)
  (if (zp x) nil
    (let ((zed (minimal-fraction-list x q)))
      (cons zed (minimal-fractions-list-rec (1- x) q)))))

(defun minimal-fractions-list (q)
  (minimal-fractions-list-rec (1- q) q))

(defun minimal-fraction-rec (k m x q)
  (declare (xargs :measure (1+ (min (nfix (- (nfix q) (nfix k))) (nfix  (- (nfix q) (nfix m)))))
                  :hints (("Goal" :in-theory (enable nfix)))))
  (let ((k (nfix k))
        (m (nfix m))
        (q (nfix q)))
  (let ((n (- (smod (* k x) q)))
        (p (smod (* m x) q)))
    (if (or (< q (+ k m)) (zp k) (zp m)) (mv p m)
      (cond
       ((< n p)
        (let ((nm (+ k m)))
          (if (< (mag  p m)
                 (mag (smod (* nm x) q) nm))
              (if (< (mag n k) (mag p m))
                  (mv (- n) k)
                (if (< (mag p m) (mag n k))
                    (mv p m)
                  (if (< m k) (mv p m) (mv (- n) k))))
            (minimal-fraction-rec k nm x q))))
       (t
        (let ((nk (+ k m)))
          (if (< (mag  n k)
                 (mag (- (smod (* nk x) q)) nk))
              (if (< (mag p m) (mag n k))
                  (mv p m)
                (if (< (mag n k) (mag p m))
                    (mv (- n) k)
                  (if (< m k) (mv p m) (mv (- n) k))))
            (minimal-fraction-rec nk m x q)))))))))

(defun minimal-fraction (x q)
  (let ((g (gcdx x q)))
    (if (not (equal g 1)) (mv 0 1)
      (let ((x (smod x q)))
        (if (or (equal x 0) (equal x 1) (equal x -1)) (mv x 1)
          (let ((c (smallest-coefficient 0 (mod x q) q)))
            (met ((k m x) (if (<= x 0) (mv 1 c (+ q x)) (mv c 1 x)))
              (met ((n d) (minimal-fraction-rec k m x q))
                (mv n d)))))))))

(defun minimal-fractions-rec (x q)
  (if (zp x) nil
    (met ((n d) (minimal-fraction x q))
      (cons (cons n d) (minimal-fractions-rec (1- x) q)))))

(defun minimal-fractions (q)
  (minimal-fractions-rec (1- q) q))


(defun partition-denominators (d x q)
  (if (zp d) (mv nil nil)
    (let ((d (1- d)))
      (met ((nlist plist) (partition-denominators d x q))
        (let ((n (smod (* d x) q)))
          (if (< n 0) (mv (cons d nlist) plist)
            (mv nlist (cons d plist))))))))

(defthm len-sum
  (equal (+ (len (mv-nth 0 (partition-denominators d x q)))
            (len (mv-nth 1 (partition-denominators d x q))))
         (nfix d))
  :hints (("Goal" :in-theory (enable nfix))))

(defthm one-is-largest
  (or (<= (nfix d) (* 2 (len (mv-nth 0 (partition-denominators d x q)))))
      (<= (nfix d) (* 2 (len (mv-nth 1 (partition-denominators d x q))))))
  :hints (("Goal" :do-not-induct t
           :use len-sum)))

(defun min-value (xlist)
  (if (not (consp xlist)) 0
    (if (not (consp (cdr xlist))) (car xlist)
      (let ((m (min-value (cdr xlist))))
        (min (car xlist) m)))))
      
(defun max-value (xlist)
  (if (not (consp xlist)) 0
    (if (not (consp (cdr xlist))) (car xlist)
      (let ((m (max-value (cdr xlist))))
        (max (car xlist) m)))))

(defstub min-delta (xlist) nil)

(defthm
  (equal (m2 (<-sort list))
         (min-delta list)))

(skip-proofs
 (defthmd max-delta
   (implies
    (nat-listp xlist)
    (<= (* (len xlist) (min (min-value xlist) (min-delta xlist))) (max-value xlist))))
 )

(defun mabs-values (dlist x q)
  (if (not (consp dlist)) nil
    (cons (mabs (* (car dlist) x) q)
          (mabs-values (cdr dlist) x q))))

(defun lte-halfp (xlist q)
  (if (not (consp xlist)) t
    (and (<= (* 2 (car xlist)) q)
         (lte-halfp (cdr xlist) q))))

(include-book "arithmetic-5/top" :dir :system)

(defthm lte-halfp-mabs-values
  (implies
   (posp q)
   (lte-halfp (mabs-values dlist x q) q))
  :hints (("Goal" :in-theory (enable abs mabs smod))))

(defthmd lte-halfp-max-value
  (implies
   (and
    (natp q)
    (nat-listp xlist)
    (lte-halfp xlist q))
   (<= (* 2 (max-value xlist)) q)))

(defthm max-delta-instance
  (implies
   (and
    (natp q)
    (nat-listp xlist)
    (lte-halfp xlist q))
   (<= (* 2 (len xlist) (min (min-value xlist) (min-delta xlist))) q))
  :hints (("Goal" :do-not-induct t
           :use (max-delta lte-halfp-max-value))))

(skip-proofs
(defthm smod-negative
  (implies
   (integerp a)
   (equal (smod (- a) q)
          (- (smod a q))))
  :hints (("Goal" :in-theory (enable smod))))
)
(in-theory (disable smod-commutes-negation))

(defthm re-fix-if
  (implies
   (and
    (posp j)
    (< j q)
    (posp q)
    (integerp x)
    (generic-invertible-p x q))
   (iff (IF (< 0 (SMOD (* j x) Q)) a b)
        (IF (< (SMOD (* J X) Q) 0) b a)))
  :hints (("Goal" :cases ((equal (smod (* j x) q) 0))
           :in-theory (enable equal-smod-zero-x))))

(defthmd test
  (implies
   (and
    (natp x)
    (posp q)
    (generic-invertible-p x q)
    (posp i)
    (posp j)
    (< j q)
    (< i q)
    (equal (msign (* i x) q)
           (msign (* j x) q)))
   (equal (mabs (* (abs (- i j)) x) q)
          (abs (- (mabs (* i x) q) (mabs (* j x) q)))))
  :hints (("Goal" :in-theory (enable abs mabs))))

(defun delta-sign (i j x q)
  (sign (- (smod (* (max i j) x) q) (smod (* (min i j) x) q))))

(thm
  (implies
   (and
    (natp x)
    (posp q)
    (generic-invertible-p x q)
    (posp i)
    (posp j)
    (< i q)
    (< j q)
    (equal (msign (* i x) q)
           (msign (* j x) q))
    )
   (equal (msign (* (abs (- i j)) x) q)
          (delta-sign i j x q)))
  :hints (("Goal" :in-theory (enable abs msign)))) 

(defthm
  

;; (equal (* k x) p)

;; k = number of elements
;; If k < s and m < s then one of p or q must be greater than s
;;
;; (* k p) = M - (* m q)
;;
;; K starts out small, p starts out large
;; 
;; (k + m)(p - q) = M - (* m q)
;;
;; The product of k and p is less than q.
;; 
;; - kq + mp = mq
;;
;; mp - kq = mq

;; kp = M - mq
;;
;; (k+m)(p-q) = M - mq
;; kp-kq+mp-mq = M-mq
;; M-mq-kq+mp=M
;; -mq-kq+mp = 0
;; m(p-q) - kq = 0
;; 

;; (len xlist) is 

#+joe
(defthm smallest-coefficient-bounds-min-difference
  (implies
   (and
    (natp x)
    (posp q)
    (generic-invertible-p x q)
    (natp d1)
    (natp d2)
    ;;(< d1 q)
    ;;(< d2 q)
    (not (equal (msign (* d1 x) q)
                (msign (* d2 x) q)))
    (smallest-coefficient-pair d1 d2 x q)
    (posp i)
    (posp j)
    (< i q)
    (< j q)
    (equal (msign (* i x) q)
           (msign (* j x) q))
    (not (equal i j))
    #+joe
    (or (and (equal (msign (* (abs (- i j)) x) q) (msign (* d1 x) q)) (< (abs (- i j)) d1))
        (and (equal (msign (* (abs (- i j)) x) q) (msign (* d2 x) q)) (< (abs (- i j)) d2)))
    #+joe
    (or (and (equal (msign (* (abs (- i j)) x) q) (msign (* d1 x) q)) (< i d1) (< j d1))
        (and (equal (msign (* (abs (- i j)) x) q) (msign (* d2 x) q)) (< i d2) (< j d2)))
    (or (and (equal (delta-sign i j x q) (msign (* d1 x) q)) (< i d1) (< j d1))
        (and (equal (delta-sign i j x q) (msign (* d2 x) q)) (< i d2) (< j d2)))
    )
   (<= (+ (mabs (* d1 x) q) (mabs (* d2 x) q))
       (mabs (* (abs (- i j)) x) q) ;; (abs (- (mabs (* i x) q) (mabs (* j x) q)))
       ))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (smallest-coefficient-pair-commutes msign nfix abs mabs SMALLEST-COEFFICIENT-PAIR-P)
                           (smallest-coefficient-pair-necc
                            GENERIC-INVERTIBLE-REDUCES-EQUAL-SMOD-0))
           :use (
                 (:instance smallest-coefficient-pair-necc
                            (k d1)
                            (m d2)
                            (n (abs (- i j)))
                            )
                 
                 ))
          ))
          

;; (defthm
;;   (implies
;;    (and
;;     (natp d1)
;;     (natp d2)
;;     (natp x)
;;     (natp q)
;;     (smallest-coefficient-pair d1 d2 x q))
;;    (and (equal (min-value (mv-nth 0 (partition-denominators (+ d1 d2) x q)))
;;                (if (< (msign (* d1 x) q) 0) (mabs (* d1 x) q) (mabs (* d2 x) q)))
;;         (equal (min-value (mv-nth 0 (partition-denominators (+ d1 d2) x q)))
;;                (if (< 0 (msign (* d2 x) q) 0) (mabs (* d2 x) q) (mabs (* d1 x) q))))))

;; ;; If you have 

;; ;; (defun isqrt-rec (x q)
;; ;;   (declare (xargs :measure (1+ (nfix (- (nfix q) (nfix x))))))
;; ;;   (let ((x (nfix x))
;; ;;         (q (nfix q)))
;; ;;     (if (zp q) 0
;; ;;       (if (zp x) (isqrt-rec 1 q)
;; ;;         (let ((nx (1+ x)))
;; ;;           (if (< q (* nx nx)) x
;; ;;             (isqrt-rec nx q)))))))

;; ;; (defthm isqrt-property
;; ;;   (implies
;; ;;    (and
;; ;;     (natp x)
;; ;;     (natp q)
;; ;;     (<= (* x x) q))
;; ;;    (<= (* (isqrt-rec x q)
;; ;;           (isqrt-rec x q)) q)))

;; ;; (defthm isqrt-is-maximal
;; ;;   (implies
;; ;;    (and
;; ;;     (<= (* y y) q)
;; ;;     (<= y (isqrt-rec x q)))))

;; (defun i-sqrt (q)
;;   (isqrt-rec 1 q))

;; (defun lt-sqrt (x q)
;;   (< (* x x) q))

;; (defthm smallest-coefficient-pair-bound
;;   (and
;;     (natp d1)
;;     (natp d2)
;;     (natp x)
;;     (natp q)
;;     (smallest-coefficient-pair d1 d2 x q)

;; (defthm minimal-coefficient-bound
;;   (implies
;;    (and
;;     (natp d1)
;;     (natp d2)
;;     (natp x)
;;     (natp q)
;;     (smallest-coefficient-pair d1 d2 x q)
;;     (not (equal (msign (* d1 x) q)
;;                 (msign (* d2 x) q)))
;;     (lt-sqrt d1 q)
;;     (lt-sqrt d2 q)
;;     (not (lt-sqrt (+ d1 d2) q)))
;;    (let ((n1 (mabs (* d1 x) q))
;;          (n2 (mabs (* d2 x) q)))
;;      (or (< (* n1 n1) q)
;;          (< (* n2 n2) q)))))
