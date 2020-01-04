(in-package "ACL2")

(defun >=all (x xlist)
  (if (not (consp xlist)) t
    (let ((a (nfix (car xlist))))
      (and (>= (nfix x) a)
           (>=all x (cdr xlist))))))

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
    (let ((min (min min (- x (car xlist)))))
      (mindelta-1 min (car xlist) (cdr xlist)))))

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
    (mindelta-1 (car xlist) (car xlist) (cdr xlist))))

(defthm max-mindelta
  (implies
   (and
    (nat-listp xlist)
    (>=listp xlist))
   (<= (* (len xlist) (mindelta xlist)) (nfix (car xlist))))
  :hints (("Goal" :use (:instance max-mindelta-1
                                  (min (car xlist))
                                  (x   (car xlist))
                                  (xlist (cdr xlist))
                                  )
           :do-not-induct t)))
