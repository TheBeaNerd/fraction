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

(defun all-same-sign (c x q)
  (declare (xargs :measure (nfix c)
                  :hints (("Goal" :in-theory (enable nfix posfix)))))
  (let ((c  (nfix c))
        (x  (nfix x))
        (q  (posfix q)))
    (if (equal (* 2 (mabs x q)) q) nil
      (if (<= c 1) t
        (and (equal (msign (* c x) q) (msign x q))
             (all-same-sign (1- c) x q))))))

(defthm all-same-sign-msign-implication
  (implies
   (and
    (natp x)
    (natp z)
    (posp q)
    (posp c)
    (all-same-sign c x q)
    (integerp k0)
    (<= 1 k0)
    (<= k0 c))
   (equal (msign (* k0 x) q)
          (msign x q)))
  :hints (("Goal" :in-theory (enable posp)
           :induct (all-same-sign c x q))))

(defthm all-same-sign-1
  (equal (all-same-sign 1 x q)
         (not (equal (* 2 (mabs (nfix x) (posfix q))) (posfix q)))))

(defthmd mod-multiplication-commutes
  (implies
   (and
    (posp q)
    (natp x)
    (natp c)
    (all-same-sign c x q)
    (force (not (equal (* 2 (mabs x q)) q))))
   (equal (mod (* c x) q)
          (if (zp c) 0
            (if (< 0 (msign x q))
                (* c (mod x q))
              (+ (* (1- c) (- q))
                 (* c (mod x q)))))))
  :hints (("Goal" :in-theory (disable msign)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :induct (all-same-sign c x q))
          (and stable-under-simplificationp
               '(:expand (all-same-sign (+ -1 c) x q)))
          (and stable-under-simplificationp
               '(:cases ((equal c 1))))
          (and stable-under-simplificationp
               '(:in-theory (enable mabs msign smod)))
          ))

(encapsulate
    ()

  (local
   (defthm smod-plus-1-all-same-sign
     (implies
      (and
       (posp q)
       (natp x)
       (natp c)
       (equal (msign (* c x) q)
              (msign x q))
       (equal (msign (+ (- x) (* c x)) q)
              (msign x q))
       (not (equal (* 2 (mabs x q)) q))
       )
      (equal (smod (* c x) q)
             (+ (smod x q)
                (smod (+ (- x) (* c x)) q))))
     :hints (("Goal" :use (:instance smod-plus-same-sign
                                     (a (* (1- c) x))
                                     (b x)
                                     (q q)))))
   )

  (defthm smod-multiplication-commutes
    (implies
     (and
      (posp q)
      (natp x)
      (natp c)
      (not (equal (* 2 (mabs x q)) q))
      (all-same-sign c x q))
     (equal (smod (* c x) q)
            (* c (smod x q))))
    :hints (("Goal" :in-theory (disable msign))
            (and stable-under-simplificationp
                 '(:expand (all-same-sign (+ -1 c) x q)))
            (and stable-under-simplificationp
                 '(:cases ((equal c 1))))
            (and stable-under-simplificationp
                 '(:cases ((equal c 0))))
            ))

  )

(defthmd mod-multiplication-commutes-when-all-not-equal
  (implies
   (and
    (posp q)
    (natp x)
    (natp c)
    (all-same-sign c x q)
    (posp k0)
    (<= k0 c)
    (force (not (equal (* 2 (mabs x q)) q))))
   (equal (mod (* k0 x) q)
          (if (< 0 (msign x q))
              (* k0 (mod x q))
            (if (zp k0) 0
              (+ q (* k0 (+ (- q) (mod x q))))))))
  :hints (("Goal" :induct (all-same-sign c x q)
           :in-theory (enable mod-multiplication-commutes)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm smod-multiplication-commutes-when-all-not-equal
  (implies
   (and
    (posp q)
    (natp x)
    (natp c)
    (all-same-sign c x q)
    (natp k0)
    (<= k0 c)
    (force (not (equal (* 2 (mabs x q)) q))))
   (equal (smod (* k0 x) q)
          (* k0 (smod x q)))))

(defthm mabs-multiplication-commutes-when-all-not-equal
  (implies
   (and
    (posp q)
    (natp x)
    (natp c)
    (all-same-sign c x q)
    (natp k0)
    (<= k0 c)
    (force (not (equal (* 2 (mabs x q)) q))))
   (equal (mabs (* k0 x) q)
          (* k0 (mabs x q))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable abs mabs))))

(defthm all-same-sign-multiples-larger-than-x
  (implies
   (and
    (natp c)
    (natp x)
    (posp q)
    (all-same-sign c x q)
    (integerp k0)
    (< 1 k0)
    (<= k0 c)
    (force (not (equal (mabs x q) 0)))
    (force (not (equal (* 2 (mabs x q)) q))))
   (< (mabs x q) (mabs (* k0 x) q)))
  :hints (("Goal" :do-not-induct t)))

(defun ndiv (n d)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n))
        (d (posfix d)))
    (if (zp d) 0
      (if (< n d) 0
        (1+ (ndiv (- n d) d))))))

(defthm ndiv-n-n
  (implies
   (posp n)
   (equal (ndiv n n) 1)))

(defthm ndiv-upper-bound
  (implies
   (and
    (natp n)
    (integerp d))
   (<= (ndiv n d) n))
  :rule-classes (:linear))

(defthm ndiv-upper-bound-strict
  (implies
   (and
    (integerp n)
    (<= 1 n)
    (integerp d)
    (< 1 d))
   (< (ndiv n d) n))
  :rule-classes (:linear))

(defun nmod (n d)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n))
        (d (posfix d)))
    (if (zp d) 0
      (if (< n d) n
        (nmod (- n d) d)))))

(defthm nmod-bound
  (implies
   (and
    (natp n)
    (posp d))
   (and (< (nmod n d) d)
        (<= 0 (nmod n d))))
  :rule-classes (:linear))

(defthm ndiv-times-d
  (implies
   (and
    (natp n)
    (natp d))
   (equal (* (ndiv n d) d) (if (equal d 0) 0 (- n (nmod n d)))))
  :hints (("Goal" :in-theory (enable posfix))))

(defthm ndiv-times-bound
  (implies
   (and
    (natp n)
    (natp d))
   (<= (* (ndiv n d) d) n))
  :rule-classes (:linear))

dag
(defun all-same-sign-bound (z c x q)
  (declare (xargs :measure (nfix c)
                  :hints (("Goal" :in-theory (enable nfix posfix)))))
  (let ((z  (nfix z))
        (c  (nfix c))
        (x  (nfix x))
        (q  (posfix q)))
    (if (equal (* 2 (mabs x q)) q) nil
      (if (<= c z) t
        (and (equal (msign (* c x) q) (msign x q))
             (all-same-sign-bound z (1- c) x q))))))

(defthm checkmate
  (implies
   (and
    (posp q)
    (posp n)
    (<= n q))
   (equal (ndiv (+ (- n) q) n)
          (1- (ndiv q n))))
  :hints (("Goal" :expand (ndiv q n))))
  
(defthmd <-rule-1
  (implies
   (and
    (posp q)
    (natp n))
   (iff (< q (+ n z))
        (< (+ (* (ndiv q n) n) (nmod q n)) (+ n z)))))

(defthm <-div
  (implies
   (and
    (posp q)
    (natp k)
    (posp n)
    (< n q))
   (iff (< k (ndiv q N))
        (< (* k N) q)))
  :hints (("Goal" :induct (ndiv q n)
           :in-theory (e/d (posfix) ((:definition ndiv))))))

(defthm all-same-sign-div-2
  (implies
   (and
    (posp q)
    (natp N)
    (< (* 2 N) q)
    (integerp k)
    (< 1 k)
    (< (* 2 k) (div q N)))
   (all-same-sign k n q))
  :hints (("Goal" :induct (all-same-sign k n q)
           :do-not-induct t)))


dag

(defun init-k (c x q)
  (declare (xargs :measure (nfix (- (posfix q) (nfix c)))))
  (let ((c (nfix c))
        (x (nfix x))
        (q (posfix q)))
    (if (equal (* 2 (mabs x q)) q) 0
      (if (<= q c) 0
        (if (not (equal (msign (* (1+ c) x) q) (msign x q))) c
          (init-k (1+ c) x q))))))

DAG: we are having some trouble reasoning about all this.


(defthm init-k-is-just-div
  (implies
   (and
    (posp q)
    (posp x)
    (natp c)
    (<= c (div q (* 2 x)))
    (not (equal (* 2 (mabs x q)) q)))
   (and (<= c (init-k c x q))
        (<= (div q (* 2 x)) c)))
  :hints (("Goal" :in-theory (e/d (abs smod mabs) (msign)))))

;; So, because our induction 

(defthm all-same-sign-init-k
  (implies
   (and
    (natp c)
    (natp x)
    (posp q)
    (all-same-sign c x q))
   (all-same-sign (init-k c x q) x q))
  :hints (("Goal" :in-theory (disable msign))))

(defthm all-init-k-multiples-larger-than-x
  (implies
   (and
    (natp x)
    (posp q)
    (integerp k0)
    (< 1 k0)
    (<= k0 (init-k 0 x q))
    (force (not (equal (mabs x q) 0)))
    (force (not (equal (* 2 (mabs x q)) q))))
   (< (mabs x q) (mabs (* k0 x) q)))
  :hints (("Goal" :do-not-induct t)))

(defun all-different-sign (k x q)
  (declare (xargs :measure (nfix k)))
  (let ((k (nfix k))
        (x (nfix x))
        (q (posfix q)))
    (if (<= k 1) nil
      (and (not (equal (msign x q) (msign (* k x) q)))
           (let ((k (1- k)))
             (if (equal (msign x q) (msign (* k x) q))
                 (all-same-sign k x q)
               (all-different-sign k x q)))))))

(defthm backwards-sum-reduction
  (implies
   (and
    (integerp x)
    (not (equal (* 2 (mabs x q)) q))
    (equal (msign z q) (msign (+ (- x) z) q))
    (integerp z)
    (posp q))
   (equal (+ (smod x q) (smod (+ (- x) z) q))
          (smod z q)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable mabs abs smod))))

(encapsulate
    ()
  
  (local
   (defthmd all-same-sign-product-commutes-helper
     (implies
      (and
       (natp k)
       (natp x)
       (posp q)
       (not (equal (msign (* (1+ k) x) q) (msign x q)))
       (all-same-sign k x q))
      (equal (smod (* (1+ k) x) q)
             (* (- (msign x q)) (+ q (- (* (1+ k) (mabs x q)))))))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d (mabs abs smod) ()))
             (and stable-under-simplificationp
                  '(:in-theory (enable mabs abs smod MOD-MULTIPLICATION-COMMUTES)))
             )))

  (defthm all-same-sign-product-commutes
    (implies
     (and
      (posp k)
      (natp x)
      (posp q)
      (not (equal (msign (* k x) q) (msign x q)))
      (all-same-sign (1- k) x q))
     (equal (smod (* k x) q)
            (* (- (msign x q)) (+ q (- (* k (mabs x q)))))))
    :hints (("Goal" :use (:instance all-same-sign-product-commutes-helper
                          (k (1- k))))))
  )

(defthm smod-overflow
  (implies
   (and
    (natp k)
    (natp x)
    (posp q)
    (not (equal (* 2 (mabs x q)) q))
    (all-different-sign k x q))
   (equal (smod (* k x) q)
          (* (- (msign x q)) (+ q (- (* k (mabs x q)))))))
  :hints (("Goal" :induct (all-different-sign k x q)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (mabs abs) ()))))

(defun init-m (k x q)
  (declare (xargs :measure (nfix (- (posfix q) (nfix k)))
                  :hints (("Goal" :in-theory (enable nfix posfix)))))
  (let ((k (nfix k))
        (x (nfix x))
        (q (posfix q)))
    (if (or (<= q k) (equal (msign x q) (msign (* (1+ k) x) q))) k
      (if (< (mabs (* (1+ k) x) q) (mabs x q)) k
        (init-m (1+ k) x q)))))

(defthm all-greater-init-m
  (implies
   (and
    (natp k)
    (natp x)
    (posp q)
    (all-different-sign k x q))
   (all-different-sign (init-m k x q) x q))
  :hints (("Goal" :induct (init-m k x q))))



(defthm
  (

dag
(defthm smallest-coefficient-pair-init-k
  (implies
   (and
    (posp q)
    (natp x)
    (generic-invertible-p x q))
   (smallest-coefficient-pair-p n 1 (1+ (init-k 1 x q)) x q))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-p) (msign))
           :do-not-induct t)
          ("Subgoal 3" :in-theory (enable nfix)
           :cases ((equal n 1)))
          ))
dag
(defthm multiple-of-modulus-is-zero
  (implies
   (and (integerp x) (posp q))
   (equal (smod (* x q) q) 0))
  :hints (("Goal" :in-theory (enable smod))))

(defthm smod-smod
  (implies
   (and (integerp x) (posp q))
   (equal (smod (smod x q) q)
          (smod x q)))
  :hints (("Goal" :in-theory (enable smod))))

(defthm smod-plus-2
  (implies
   (and (integerp a) (integerp b) (posp q))
   (equal (smod (+ a (smod b q)) q)
          (smod (+ a b) q)))
  :hints (("Goal" :in-theory (enable smod))))

(defthmd smod-plus-2-push
  (implies
   (and (integerp a) (integerp b) (posp q))
   (equal (smod (+ a b) q)
          (smod (+ a (smod b q)) q)))
  :hints (("Goal" :in-theory (enable smod))))

(defthm rewrite-multiple-of-modulus
  (implies
   (and (integerp a)
        (integerp b)
        (integerp x)
        (posp q))
   (equal (smod (+ a b (* q x)) q)
          (smod (+ a b) q)))
  :INSTRUCTIONS (:PRO (:DV 1)
                      (:REWRITE SMOD-PLUS-2-PUSH)
                      (:DV 1)
                      (:DV 2)
                      (:REWRITE SMOD-PLUS-2-PUSH)
                      (:DV 1)
                      (:DV 2)
                      :X
                      :UP :S
                      :UP :UP
                      :UP (:REWRITE SMOD-PLUS-2)
                      :UP :S))



#|
(skip-proofs
(defthm generic-invertible-p-implies-not-divisible
  (implies
   (generic-invertible-p x q)
   (not (integerp (* (/ q) x))))
  :rule-classes (:forward-chaining)))

(defthm zed
  (implies
   (and
    (pred (hide k0))
    (natp x)
    (posp q)
    (generic-invertible-p x q)
    (same-sign k0 x q)
    (equal (msign (* k0 x) q)
           (msign x q))
    (natp k0)
    (< 1 k0))
   (< (mabs x q) (mabs (* k0 x) q)))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize)
           :induct (same-sign k0 x q))
          (and stable-under-simplificationp
               '(:in-theory (enable abs mabs smod)))))

(defthm same-sign-mabs-implication
  (implies
   (and
    (pred (hide k0))
    ;;(pred (hide c))
    (natp x)
    (posp q)
    (posp c)
    (<= c q)
    (generic-invertible-p x q)
    (same-sign c x q)
    (natp k0)
    (< 1 k0)
    (< k0 c))
   (< (mabs x q) (mabs (* k0 x) q)))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :induct (same-sign c x q))
          (and stable-under-simplificationp
               '(:in-theory (enable mabs smod)))))

(defthm all-smaller-have-large-magnitude
  (implies
   (and
    (natp k0)
    (< 1 k0)
    (natp x)
    (posp q)
    (generic-invertible-p x q)
    (< k0 (init-k c x q))
    (posp c)
    (<= c q)
    (same-sign c x q))
   (< (mabs x q) (mabs (* k0 x) q)))
  :hints (("Goal" :induct (init-k c x q)
           :in-theory (e/d () (msign))
           :do-not-induct t)))

(in-theory (disable same-sign))


|#
