;;
;; Copyright (C) 2020, David Greve
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;;
(in-package "ACL2")

(defun >=all (x xlist)
  (if (not (consp xlist)) t
    (let ((a (nfix (car xlist))))
      (and (>= (nfix x) a)
           (>=all x (cdr xlist))))))

(defun <=all (x xlist)
  (if (not (consp xlist)) t
    (let ((a (nfix (car xlist))))
      (and (<= (nfix x) a)
           (<=all x (cdr xlist))))))

(defun >=listp (xlist)
  (if (not (consp xlist)) t
    (and (>=all (car xlist) (cdr xlist))
         (>=listp (cdr xlist)))))

(defun >=insert (x xlist)
  (if (not (consp xlist)) (list x)
    (if (>= x (car xlist)) (cons x xlist)
      (cons (car xlist) (>=insert x (cdr xlist))))))

(defthm >=all->=insert
  (implies
   (and
    (natp x)
    (natp z)
    (>=all z xlist)
    (>= z x))
   (>=all z (>=insert x xlist))))

(defthm >=listp->=insert
  (implies
   (and
    (natp x)
    (nat-listp xlist)
    (>=listp xlist))
   (>=listp (>=insert x xlist))))

(defun union-2 (x xlist y ylist)
  (declare (xargs :measure (+ (len xlist) (len ylist))))
  (cond
   ((>= x y)
    (if (not (consp xlist)) (cons x (cons y ylist))
      (cons x (union-2 (car xlist) (cdr xlist) y ylist))))
   (t
    (if (not (consp ylist)) (cons y (cons x xlist))
      (cons y (union-2 x xlist (car ylist) (cdr ylist)))))))

(defthm union-2-to->=insert
  (implies
   (and
    (true-listp ylist)
    (true-listp xlist)
    (not (consp xlist)))
   (equal (union-2 x xlist y ylist)
          (>=insert x (cons y ylist)))))
 
(defthm >=all-union-2
  (implies
   (and
    (natp z)
    (natp x)
    (natp y)
    (>= z x)
    (>= z y)
    (nat-listp xlist)
    (nat-listp ylist)
    (>=all x xlist)
    (>=listp xlist)
    (>=all y ylist)
    (>=listp ylist))
   (>=all z (union-2 x xlist y ylist)))
  :hints (("Goal" :induct (union-2 x xlist y ylist))))

(defthm >=list-union-2
  (implies
   (and
    (natp x)
    (natp y)
    (nat-listp xlist)
    (nat-listp ylist)
    (>=all x xlist)
    (>=listp xlist)
    (>=all y ylist)
    (>=listp ylist))
   (>=listp (union-2 x xlist y ylist)))
  :hints (("Goal" :induct (union-2 x xlist y ylist)
           :expand (union-2 x xlist y ylist))))

(defun onion (xlist ylist)
  (if (not (consp xlist)) ylist
    (if (not (consp ylist)) xlist
      (union-2 (car xlist) (cdr xlist) (car ylist) (cdr ylist)))))

(defthm >=listp-onion
  (implies
   (and
    (nat-listp xlist)
    (nat-listp ylist)
    (>=listp xlist)
    (>=listp ylist))
   (>=listp (onion xlist ylist))))

(in-theory (disable onion))

(defun mindelta-1 (min x xlist)
  (if (not (consp xlist)) (min min x)
    (let ((xmin (- x (car xlist))))
      (if (and (<= min xmin) (<= min x))
          (mindelta-1 min (car xlist) (cdr xlist))
        (let ((min (min x xmin)))
          (mindelta-1 min (car xlist) (cdr xlist)))))))

(defthm mindelta-1-lower-bound
  (implies
   (and
    (natp min)
    (natp x)
    (nat-listp xlist)
    (>=all x xlist)
    (>=listp xlist)
    )
   (<= 0 (mindelta-1 min x xlist)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((mindelta-1 min x xlist))))
  :hints (("Goal" :induct (mindelta-1 min x xlist)
           :expand (mindelta-1 min x xlist))))

(defthm integerp-mindelta-1
  (implies
   (and
    (integerp min)
    (integerp x)
    (integer-listp xlist))
   (integerp (mindelta-1 min x xlist)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((mindelta-1 min x xlist)))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm mindelta-1-min-bound
  (implies
   (and
    (natp min)
    (natp x)
    (nat-listp xlist)
    (>=listp xlist)
    (>=all x xlist))
   (<= (mindelta-1 min x xlist) min))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((mindelta-1 min x xlist))))
  :hints (("Goal" :induct (mindelta-1 min x xlist)
           :expand (mindelta-1 min x xlist))))

(defthmd max-mindelta-1
  (implies
   (and
    (natp min)
    (natp x)
    (nat-listp xlist)
    (>=listp xlist)
    (>=all x xlist))
   (<= (* (1+ (len xlist)) (mindelta-1 min x xlist)) x))
  :hints (("Goal" :induct (mindelta-1 min x xlist)
           :do-not-induct t
           :expand (MINDELTA-1 MIN X XLIST))
          (and stable-under-simplificationp
               '(:nonlinearp t))))

(defun mindelta (xlist)
  (if (not (consp xlist)) 0
    (mindelta-1 (* 2 (car xlist)) (car xlist) (cdr xlist))))

(defthm mindelta-less-than-all
  (implies
   (and
    (natp x)
    (natp min)
    (nat-listp xlist)
    (>=listp xlist)
    (>=all x xlist))
   (and (<= (mindelta-1 min x xlist) min)
        (<= (mindelta-1 min x xlist) x)
        (<=all (mindelta-1 min x xlist) xlist)))
  :hints (("Goal" :induct (mindelta-1 min x xlist)
           :expand (mindelta-1 min x xlist)))
  :rule-classes ((:forward-chaining :trigger-terms ((mindelta-1 min x xlist)))))

(defthm irrelevant-min
  (implies
   (and
    ;; Assuming x is non-zero ..
    ;; technically we only really care about (pos-listp xlist)
    (posp x)
    (natp min)
    (nat-listp xlist)
    (>=listp xlist)
    (>=all x xlist)
    (<= (* 2 x) min))
   (< (mindelta-1 min x xlist) min))
  :hints (("Goal" :expand (mindelta-1 min x xlist)
           :do-not-induct t)))

;;
;; Consider the largest number in the list, N = (car xlist) 
;;
;; The minimum delta in the list is bounded above by N/(len list)
;;
;; 
(defthm max-mindelta
  (implies
   (and
    (nat-listp xlist)
    (>=listp xlist))
   (<= (* (len xlist) (mindelta xlist)) (car xlist)))
  :hints (("Goal" :use (:instance max-mindelta-1
                                  (min (* 2 (car xlist)))
                                  (x   (car xlist))
                                  (xlist (cdr xlist))
                                  )
           :do-not-induct t)))

;;
;; This works much better ..
;;

(defun md2 (x list)
  (if (not (consp list)) x
    (let ((min (md2 (car list) (cdr list))))
      (min (min x (- x (car list))) min))))

(defthm md2-lower-bound
  (implies
   (and
    (natp x)
    (nat-listp xlist)
    (>=all x xlist)
    (>=listp xlist))
   (natp (md2 x xlist)))
  :hints (("Goal" :induct (md2 x xlist))))

(defthm <=all-chaining
  (implies
   (and
    (<=all x xlist)
    (<= y x)
    (natp x)
    (natp y))
   (<=all y xlist)))
   
(defthm md2-upper-bound
  (implies
   (and
    (natp x)
    (nat-listp xlist)
    (>=all x xlist)
    (>=listp xlist))
   (and (<=all (md2 x xlist) xlist)
        (<= (md2 x xlist) x)))
  :hints (("Goal" :induct (md2 x xlist)))
  :rule-classes ((:forward-chaining :trigger-terms ((md2 x xlist)))))

(defthmd max-md2
  (implies
   (and
    (natp x)
    (nat-listp xlist)
    (>=listp xlist)
    (>=all x xlist))
   (<= (* (1+ (len xlist)) (md2 x xlist)) x))
  :hints (("Goal" :induct (md2 x xlist)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:nonlinearp t))))

(defun md (xlist)
  (if (not (consp xlist)) 0
    (md2 (car xlist) (cdr xlist))))

(defthm max-md
  (implies
   (and
    (nat-listp xlist)
    (>=listp xlist))
   (<= (* (len xlist) (md xlist)) (nfix (nth 0 xlist))))
  :hints (("Goal" :use (:instance max-md2
                                  (x   (car xlist))
                                  (xlist (cdr xlist))
                                  )
           :do-not-induct t)))

(defun md2-index (x list)
  (if (not (consp list)) 0
    (let* ((index (md2-index (car list) (cdr list)))
           (min   (md2 (car list) (cdr list))))
      (let ((mx (min x (- x (car list)))))
        (if (<= min mx) (1+ index)
          0)))))

(defthm natp-md2-index
  (natp (md2-index x list))
  :rule-classes (:rewrite 
                 (:forward-chaining :trigger-terms ((md2-index x list)))))

(defthm md2-index-upper-bound
  (< (md2-index x list) (1+ (len list)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((md2-index x list)))))

(defthm nfix-idempotnent
  (implies
   (natp x)
   (equal (nfix x) x)))

(defthm nth-special-case
  (implies
   (natp n)
   (equal (nth (+ 2 n) (cons x list))
          (nth n (cdr list))))
  :hints (("Goal" :expand (nth (+ 2 n) (cons x list)))))

(defun md-pair (a b list)
  (min (nfix (nth a list))
       (nfix (- (nfix (nth a list)) (nfix (nth b list))))))

(defthm md2-to-nth
  (implies
   (and
    (natp x)
    (nat-listp list)
    (>=listp list)
    (>=all x list))
   (equal (md2 x list)
          (let ((index (md2-index x list))
                (xlist (cons x list)))
            (md-pair index (1+ index) xlist))))
  :hints (("Goal" :induct (md2-index x list)
           :in-theory (disable nfix nth)
           :do-not-induct t)))

(in-theory (disable md-pair))

(defun md-index (list)
  (if (not (consp list)) 1
    (md2-index (car list) (cdr list))))

(defthm natp-nth
  (implies
   (and
    (nat-listp list)
    (natp i)
    (< i (len list)))
   (natp (nth i list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((nth i list)))))

(defthm md-to-nth
  (implies
   (and
    (nat-listp list)
    (>=listp list))
   (equal (md list)
          (let ((index (md-index list)))
            (md-pair index (1+ index) list))))
  :hints (("Goal" :do-not-induct t)))

(defun >=order (list)
  (if (not (consp list)) nil
    (>=insert (car list)
              (>=order (cdr list)))))

(defthm nat-listp->=order
  (implies
   (nat-listp list)
   (nat-listp (>=order list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((>=order list)))))

(defthm >=listp->=order
  (implies
   (nat-listp list)
   (>=listp (>=order list)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((>=order list)))))

(defthm member->=insert
  (iff (member a (>=insert x list))
       (or (equal a x)
           (member a list))))

(defthm ordering-preserves-membership
  (iff (member a (>=order list))
       (member a list)))

(defun value-index (value list)
  (if (not (consp list)) 1
    (if (equal value (car list)) 0
      (1+ (value-index value (cdr list))))))

(defthm value-index-membership-relation
  (iff (< (value-index value list) (len list))
       (member value list)))

(defthm md-lte-md-pair
  (implies
   (nat-listp list)
   (equal (md (>=order list))
          (let ((index (md-index (>=order list))))
            (md-pair index (1+ index) (>=order list))))))

;; (defun >=sort (list)
;;   (if (not (consp list)) nil
;;     (>=insert (car list) (>=sort (cdr list)))))

;; (defun min-delta-v (list)
;;   (if (not (consp list)) 0
;;     (if (not (consp (cdr list))) (car list)
;;       (let ((res (min-delta-v (cdr list))))
;;         (min (abs (- (car list) (cadr list))) res)))))

;; (defun min-seq (list)
;;   (if (not (consp list)) 0
;;     (if (not (consp (cdr list))) (car list)
;;       (min (- (car list) (cadr list))
;;            (min-seq (cdr list))))))

;; (defthm min-delta-v-is-min-seq-sort
;;   (implies
;;    (nat-listp list)
;;    (equal (min-delta-v list)
;;           (min-seq (>=sort list)))))
 
;; It looks like we just need something like:
;;(implies
;; (and
;;  (sorted-p list)
;;  (equal (min-seq (>=insert x list))
;;         (min (min-seq list)
;;              (min-delta x list)))))

;;dag
;; (defun zp-value-index (value list)
;;   (if (zp value) (len list)
;;     (value-index value list)))

;; (nth i (>=order list))


;; (defthm z-alpha
;;   (implies
;;    (nat-listp list)
;;    (equal (nfix (nth (zp-value-index (nfix (nth b (>=order list))) list) list))
;;           (nfix (nth b (>=order list))))))


;;   k < sqrt(Q)
;;   m < sqrt(Q)
;;   k+m > sqrt(Q)
;; |----------------------------
;;   (mabs (* k x) q) < sqrt(Q)
;;   (mabs (* m x) q) < sqrt(Q)

;; minimum delta:
;; max(k,m)

;; If we have considered N=max(k,m) coefficients, 
;; the only difference less than min(|k|,|m|) 
;; is (possibly) max(|k|,|m|) - min(|k|,|m|)
;; (ie: the next residual).

;; ie: all of the differences are greater than or
;; equal to max(|k|,|m|) - min(|k|,|m|)

;; I think we can extrapolate i/j from an arbitrary
;; n

;; L = min(|k|,|m|,abs(|k|-|m|)) is the lower bound
;; on the difference between any value less than
;; the max(k,m)
;; 
;; This bounds the difference between abs(|i|-|j|)
;; to be greater than some value.
;;
;; We then using the counting argument to show that
;; there is an upper bound.
;;


;; (defthm zed
;;   (implies
;;    (and
;;     (natp n)
;;     (posp q)
;;     (natp k)
;;     (natp m)
;;     (natp x)
;;     (smallest-coefficient-pair-p n k m x q)
;;     (not (equal (msign (* m x) q) (msign (* k x) q)))
;;     (not (equal (mod n q) 0))
;;     (or (and (equal (msign (* n x) q) (msign (* k x) q)) (< n k))
;;         (and (equal (msign (* n x) q) (msign (* m x) q)) (< n m))))
;;    (<= (+ (mabs (* k x) q) (mabs (* m x) q))
;;        (mabs (* n x) q)))
;;   :hints (("Goal" :in-theory (enable smallest-coefficient-pair-p))))


;; k: Vk
;; m: Vm

;; If they are opposite sign, you can add them to get
;; your result.

;; If they are the same sign, you can subtract them to
;; induce the 

;; k is less than S but Vk is greater.
;; m is less than S but vm is greater.
;; k+m is greater than S but (Vi + Vj) is less.
;; 
;; Conclusion: there must be a number (n) between k|m
;; and k+m such that Vn is less than S
;;
;; I think our conclusion is stronger than that because
;; we only have N/2 (signed/unsigned) open slots.
;;

;; (defun minde-1 (min x list)
;;   (if (not (consp list)) (min min x)
;;     (minde-1 (min min (abs (- x (car list)))) (cdr list))))

;; (defun minde-2 (min list)
;;   (if (not (consp list)) min
;;     (let ((min (minde-1 min (car list) (cdr list))))
;;       (minde-2 min (cdr list)))))

;; (defun minde (list)
;;   (if (not (consp list)) 0
;;     (minde-2 (car list) (cdr list))))

;; (defun-sk min-delta-index (i j)
;;   (forall (k m) (<= (abs (- (nth i list) (nth j list))) (abs (- (nth k list) (nth m list))))))

;; ;; And now you want to prove an upper bound on the
;; ;; mindelta based on the size of the list.
;; (defun-sk min-delta (value)
;;   (forall (k m) (<= (nfix value) (abs (- (nfix (nth k list)) (nfix (nth m list)))))))


;; (defun renumber (list)
;;   (if (not (consp list)) nil
    
;; (>=count a list)



;; (+ (>=count a list) (>=count a 

;; (defun renumber (i list)
;;   (if (not (consp list)) 1
;;     (if (zp i) 

;; (defthm
;;   (implies
;;    (< 1 (count a xlist))
;;    (equal (mindelta xlist) 0)))

;; (nth i list)

;; (nth i (order list)) = (nth (>=count (nth i (order list))) list)

;; (nth (>=count (nth i list)) (order list)) = (nth i list)

;; (nth i (order list)) = (nth (find (nth i (order list)) list) list)

;; (defthm
;;   (implies
;;    (< (nfix i) (len list))
;;    (equal (nth i (order list))
;;           (nth (find (nth i (order list)) list) list))))

;; (defthm mindelta-1-fixpoint
;;   (implies
;;    (and
;;     (natp x)
;;     (natp min)
;;     (nat-listp xlist)
;;     (>=listp xlist)
;;     (>=all x xlist)
;;     (equal (mindelta-1 min x xlist) x))
;;    (and (implies (consp xlist) (equal x 0))
;;         (<= x min)))
;;   :rule-classes nil
;;   :hints (("Goal" :expand (mindelta-1 min x xlist)
;;            :do-not-induct t)))

;; (defun mindelta-1-index (delta min x xlist)
;;   (if (not (consp xlist)) (if (< min x) 0 delta)
;;     (let ((xmin (- x (car xlist))))
;;       (if (and (<= min xmin) (<= min x))
;;           (mindelta-1-index (1+ delta) min (car xlist) (cdr xlist))
;;         (+ delta (1- (mindelta-1-index 1 (min x xmin) (car xlist) (cdr xlist))))))))

;; (defun repeat-value (value n)
;;   (if (zp n) nil
;;     (cons value (repeat-value value (1- n)))))

;; (defun pad (min x delta xlist)
;;   (cons (+ x min) (append (repeat-value x delta) (cons x xlist))))

;; (defthm nth-delta-append-repeat-value
;;   (implies
;;    (and
;;     (natp delta)
;;     (natp n))
;;    (equal (nth (+ delta n) (append (repeat-value x delta) y))
;;           (nth n y))))

;; (defthm natp-mindelta-1-index
;;   (implies
;;    (posp delta)
;;    (natp (mindelta-1-index delta min x xlist)))
;;   :rule-classes (:rewrite 
;;                  (:forward-chaining :trigger-terms ((mindelta-1-index delta min x xlist)))))

;; (defthm mindelta-1-index-bound
;;   (implies
;;    (posp delta)
;;    (<= (mindelta-1-index delta min x xlist)
;;        (+ delta 1 (len xlist))))
;;   :rule-classes (:linear
;;                  (:forward-chaining :trigger-terms ((mindelta-1-index delta min x xlist)))))

;; (defthm mindelta-as-nth-difference
;;   (implies
;;    (and
;;     (natp x)
;;     (natp min)
;;     (posp delta)
;;     (nat-listp xlist)
;;     (>=listp xlist)
;;     (>=all x xlist))
;;    (equal (mindelta-1 min x xlist)
;;           (let ((index (mindelta-1-index delta min x xlist)))
;;             (let ((recon (pad min x delta xlist)))
;;               (- (nfix (nth index      recon))
;;                  (nfix (nth (1+ index) recon)))))))
;;   :hints (("Goal" :in-theory (disable nfix nth)
;;            :induct (mindelta-1-index delta min x xlist)
;;            :do-not-induct t)))
;; dag
;; (implies
;;  (<= (* 2 x) min)
;;  (equal (mindelta-1 min x xlist)
;;         (let ((value (mindelta-1 min x xlist)))
;;           (let ((recon (if (equal value x) (list x)
;;                          (pad x delta xlist))))
;;             (let ((index (value-index value x recon)))
;;               (- (nfix (nth index recon))
;;                  (nfix (nth (1+ index) recon)))))))

;; (equal (nfix (nth i (>=order list)))
;;        (let ((value (nfix (nth i (>=order list)))))
;;          (let ((index (if (zp value) (len list) (value-index value list))))
;;            (nfix (nth i list)))))

;; (equal (mindelta xlist)
;;        (- (nth (larger-index xlist) xlist)
;;           (nth (smaller-index xlist) xlist)))

;; ;; So, because xlist is sorted, min delta will
;; ;; always be a simple sequence.
;; (defun mindelta-1 (min x xlist)
;;   (if (not (consp xlist)) (min min x)
;;     (let ((min (min (min min x) (- x (car xlist)))))
;;       (mindelta-1 min (car xlist) (cdr xlist)))))

;; dag

;;    (all-equal x xlist)))

;; (defthm
;;   (equal (mindelta-1 min x xlist)
;;          (let ((ylist (pad x delta xlist)))
;;            (- (nfix (nth (mindelta-1-index delta min x xlist) (pad min 0 delta xlist))

;; (defun larger-index (xlist)
;;   (if (not (consp xlist)) 1
;;     (larger-index-1 (car xlist) (car xlist) (cdr xlist))))

