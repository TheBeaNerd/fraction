(in-package "ACL2")

(include-book "smallest-coefficient-step")

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
          (and (smallest-coefficient-pair k m (nfix x) (posfix q))
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

;; (defthm s+-can-be-represented-in-terms-of-s-
;;   (implies
;;    (and
;;     (natp N)
;;     (natp s+)
;;     (natp s-)
;;     (equal s- (1- s+))
;;     (< N (* s+ s+))
;;     (< (* s- s-) N))
;;    (< (- N (* s+ s-)) s+))
;;   :rule-classes nil)

