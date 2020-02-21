(in-package "ACL2")

(defthm natp-implies-non-negative
  (implies
   (natp x)
   (and (integerp x)
        (<= 0 x)))
  :rule-classes (:forward-chaining))

(defthm posp-implies-positive
  (implies
   (posp x)
   (and (integerp x)
        (< 0 x)))
  :rule-classes (:forward-chaining))

(encapsulate
    (
     ((f *) => *)
     ((n)   => *)
     )

  (local 
   (defun f (x)
     (nfix x)))

  (local
   (defun n ()
     0))

  (defthm natp-f
    (natp (f x))
    :rule-classes ((:forward-chaining :trigger-terms ((f x)))))

  (defthm natp-n
    (natp (n))
    :rule-classes ((:forward-chaining :trigger-terms ((n)))))

  (defthm f-is-unique-over-n
    (implies
     (and
      (natp i)
      (natp j)
      (< i (n))
      (< j (n)))
     (iff (equal (f i) (f j))
          (equal i j))))

  )

;;(defun f-x (x) (declare (type t x)) (nfix x))

;;(defattach f f-x)

;;(defun n-x () (declare (xargs :verify-guards t)) 100)

;;(skip-proofs (defattach n n-x))

(defun max-f (n)
  (if (zp n) 0
    (let ((m (max-f (1- n))))
      (if (< (f n) (f m)) m n))))

(defthm max-f-signature
  (implies
   (natp n)
   (natp (max-f n)))
  :rule-classes ((:forward-chaining :trigger-terms ((max-f n)))))

(defthm max-f-bound
  (implies
   (natp n)
   (<= (max-f n) n))
  :rule-classes (:linear))

(defthm max-f-property
  (implies
   (and
    (natp i)
    (natp n)
    (<= i n))
   (<= (f i) (f (max-f n))))
  :rule-classes :linear)

(defthm max-f-unique-property
  (implies
   (and
    (< n (n))
    (natp n)
    (natp i)
    (<= i n)
    (not (equal i (max-f n))))
   (< (f i) (f (max-f n))))
  :hints (("Goal" :in-theory (disable max-f-property)
           :use max-f-property)))

(defun diff (x y)
  (abs (- (nfix x) (nfix y))))

(defthm diff-signature
  (natp (diff x y))
  :rule-classes ((:forward-chaining :trigger-terms ((diff x y)))))

(defthmd diff-commutes
  (equal (diff x y)
         (diff y x)))

(in-theory (disable diff))

(defun max-delta-f-1 (k n)
  (if (zp n) 0
    (let ((m (max-delta-f-1 k (1- n))))
      (if (< (diff (f k) (f n))
             (diff (f k) (f m)))
          m 
        n))))

(defthm max-delta-f-1-property
  (implies
   (and
    (natp i)
    (natp n)
    (natp k)
    (<= i n))
   (<= (diff (f k) (f i))
       (diff (f k) (f (max-delta-f-1 k n))))))

(defun min-delta-f-1 (k n)
  (if (zp n) 0
    (let ((m (min-delta-f-1 k (1- n))))
      (if (< (diff (f k) (f n))
             (diff (f k) (f m)))
          n
        m))))

(defthm min-delta-f-1-signature
  (implies
   (and
    (natp k)
    (natp n))
   (natp (min-delta-f-1 k n)))
  :rule-classes ((:forward-chaining :trigger-terms ((min-delta-f-1 k n)))))

(defthm min-delta-f-1-bound
  (implies
   (and
    (natp k)
    (natp n)
    (< n k))
   (< (min-delta-f-1 k n) k))
  :rule-classes (:linear))

(defthm min-delta-f-1-property
  (implies
   (and
    (natp i)
    (natp n)
    (natp k)
    (<= i n))
   (<= (diff (f k) (f (min-delta-f-1 k n)))
       (diff (f k) (f i))))
  :rule-classes :linear)

(defun min-f (n)
  (if (zp n) 0
    (let ((m (min-f (1- n))))
      (if (< (f n) (f m)) n m))))

(defthm min-f-signature
  (implies
   (natp n)
   (natp (min-f n)))
  :rule-classes ((:forward-chaining :trigger-terms ((min-f n)))))

(defthm min-f-bound
  (implies
   (natp n)
   (<= (min-f n) n))
  :rule-classes (:linear))

(defthm min-f-property
  (implies
   (and
    (natp i)
    (natp n)
    (<= i n))
   (<= (f (min-f n)) (f i))))

;; Here we go ..
(defun min-delta-f-2 (n)
  (if (zp n) (mv 0 0)
    (let ((m (min-delta-f-1 n (1- n))))
      (mv-let (p q) (min-delta-f-2 (1- n))
              (if (and (not (equal p q))
                       (< (diff (f p) (f q))
                          (diff (f n) (f m)))) (mv p q)
                (mv n m))))))

(in-theory (disable mv-nth))

(defthm min-delta-f-2-signature
  (implies
   (natp n)
   (and (natp (mv-nth 0 (min-delta-f-2 n)))
        (natp (mv-nth 1 (min-delta-f-2 n)))))
  :rule-classes ((:forward-chaining :trigger-terms ((min-delta-f-2 n)))))

(defthm min-delta-f-2-upper-bound
  (implies
   (natp n)
   (and (<= (mv-nth 0 (min-delta-f-2 n)) n)
        (<= (mv-nth 1 (min-delta-f-2 n)) n)))
  :rule-classes (:linear 
                 (:forward-chaining :trigger-terms ((min-delta-f-2 n)))))

(defthm min-delta-result-relation
  (implies
   (natp n)
   (<= (mv-nth 1 (min-delta-f-2 n))
       (mv-nth 0 (min-delta-f-2 n))))
  :rule-classes :linear)

(defthm min-delta-result-strong-relation
  (implies
   (posp n)
   (< (mv-nth 1 (min-delta-f-2 n))
      (mv-nth 0 (min-delta-f-2 n))))
  :rule-classes :linear)

(defthm zero-is-default
  (iff (equal (mv-nth 0 (min-delta-f-2 n))
              (mv-nth 1 (min-delta-f-2 n)))
       (or (not (natp n))
           (equal n 0)))
  :hints (("Goal" :do-not-induct t
           :use (min-delta-result-relation
                 min-delta-result-strong-relation))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))
 
 (local
  (encapsulate
      ()
    
    (defthm min-delta-f-1-instance-1
      (implies (and (natp i)
                    (natp n)
                    (posp k)
                    (force (<= i (- k 1))))
               (<= (diff (f k) (f (min-delta-f-1 k (- k 1))))
                   (diff (f k) (f i))))
      :hints (("goal" :in-theory (disable min-delta-f-1-property)
               :use (:instance min-delta-f-1-property
                               (n (1- k))))))
    
    (defthm min-delta-f-1-instance-2
      (implies (and (natp i)
                    (natp n)
                    (posp k)
                    (force (<= i (- k 1))))
               (<= (diff (f k) (f (min-delta-f-1 k (- k 1))))
                   (diff (f i) (f k))))
      :hints (("goal" :in-theory (e/d (diff-commutes) (min-delta-f-1-instance-1))
               :use min-delta-f-1-instance-1)))
    
    (defthm linear-helper
      (implies
       (and
        (< x y)
        (integerp x)
        (integerp z)
        (integerp y)
        (<= y z))
       (<= x z)))
    
    (defthm diff-commutes-instance
      (implies
       (and (syntaxp (and (quotep x) (quotep y))))
       (equal (diff (f x) (f y))
              (diff (f y) (f x))))
      :hints (("Goal" :in-theory (enable diff-commutes))))
    
    ))

 (defthm min-delta-f-2-works
   (implies
    (and
     (natp n)
     (natp i)
     (natp j)
     (<= i n)
     (<= j n)
     (not (equal i j)))
    (<= (diff (f (mv-nth 0 (min-delta-f-2 n))) (f (mv-nth 1 (min-delta-f-2 n))))
        (diff (f i) (f j))))
   :hints (("Goal" :induct (min-delta-f-2 n)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:cases ((equal i 0))))
           ))

 )

(defun min-f-delta (n)
  (mv-let (a b) (min-delta-f-2 n)
    (diff (f a) (f b))))

(defun min-f-value (n)
  (f (min-f n)))

(defun max-f-value (n)
  (f (max-f n)))

(defthm natp-max-f-value
  (natp (max-f-value n))
  :rule-classes ((:forward-chaining :trigger-terms ((max-f-value n)))))

(defthm natp-min-f-value
  (natp (min-f-value n))
  :rule-classes ((:forward-chaining :trigger-terms ((min-f-value n)))))

(defthm natp-min-f-delta
  (natp (min-f-delta n))
  :rule-classes ((:forward-chaining :trigger-terms ((min-f-delta n)))))

(defthm min-f-value-decreasing
  (<= (min-f-value n) (min-f-value (1- n)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((min-f-value n)))))
  
(defthm min-f-delta-decreasing
  (implies
   (and (integerp n) (< 1 n))
   (<= (min-f-delta n) (min-f-delta (1- n))))
  :rule-classes (:linear 
                 (:forward-chaining :trigger-terms ((min-f-delta n))))
  :hints (("Goal" :do-not-induct t)))

(defthm max-f-value-decreasing
  (<= (max-f-value (1- n)) (max-f-value n))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((max-f-value n)))))

(in-theory (disable min-f-value min-f-delta max-f-value))
(in-theory (disable (min-f-value) (min-f-delta) (max-f-value)))

(include-book "arithmetic-5/top" :dir :system)

(defun nat-induction (n)
  (if (zp n) n
    (nat-induction (1- n))))

;; So this isn't going well .. we need a different approach.

(defun next-largest (k n)
  (if (zp n) (nfix (if (< (f k) (f n)) n k))
    (let ((m (next-largest k (1- n))))
      (if (not (< (f k) (f m))) (nfix (if (< (f k) (f n)) n k))
        (if (not (< (f k) (f n))) m
          (if (< (f m) (f n)) m n))))))

(defthm next-largest-signature
  (natp (next-largest k n)))

(encapsulate
    ()

  (local
   (defthmd next-largest-bound-helper
     (implies
      (and (natp n) (natp k))
      (<= (next-largest k n) (max k n)))))

  (defthm next-largest-bound-1
    (implies
     (and (natp n) (natp k) (<= k n))
     (<= (next-largest k n) n))
    :hints (("Goal" :use next-largest-bound-helper))
    :rule-classes (:linear
                   (:forward-chaining :trigger-terms ((next-largest k n)))))

  (defthm next-largest-bound-2
    (implies
     (and (natp n) (natp k) (<= n k))
     (<= (next-largest k n) k))
    :hints (("Goal" :use next-largest-bound-helper))
    :rule-classes (:linear
                   (:forward-chaining :trigger-terms ((next-largest k n)))))

  )
   
(defthm next-largest-is-not-smaller
  (implies
   (and (natp k) (natp n))
   (<= (f k) (f (next-largest k n))))
  :rule-classes :linear)

#+joe
(defthm next-largest-fixpoint
  (implies
   (and
    (natp k)
    (natp n)
    (<= (f k) (f n))
    (< n (n)))
   (iff (equal k (next-largest k n))
        (equal k (max-f n))))
  :hints (("Goal" :induct (next-largest k n))))

(defthm next-largest-is-larger
  (implies
   (and
    (natp k)
    (natp n)
    (not (equal k (next-largest k n))))
   (< (f k) (f (next-largest k n)))))

(defthm next-largest-base-case
  (implies
   (and (natp n) (natp k) (< n (n)) (< k (n)))
   (iff (equal k (next-largest k n))
        (<= (f (max-f n)) (f k)))))

(defthmd next-largest-is-larger-if-one-exists
  (implies
   (and
    (< (f k) (f i))
    (natp n)
    (natp i)
    ;;(natp k)
    (<= i n))
   (< (f k) (f (next-largest k n)))))

(defthm next-largest-is-larger-if-not-max
  (implies
   (and
    (< n (n))
    (natp n)
    (natp k)
    (<= k n)
    (not (equal k (max-f n))))
   (< (f k) (f (next-largest k n))))
  :hints (("Goal" :do-not-induct t
           :use (:instance next-largest-is-larger-if-one-exists
                           (i (max-f n))))))

(defthmd next-largest-is-next
  (implies
   (and
    (< (f k) (f i))
    (natp n)
    (natp i)
    ;;(natp k)
    (<= i n)
    )
   (<= (f (next-largest k n))
       (f i)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((f (next-largest k n)))))
  :hints (("Goal" :induct (next-largest k n)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:cases ((equal i n))))
          (and stable-under-simplificationp
               `(:use (:instance next-largest-is-larger-if-one-exists
                                 (n (1- n)))))
          ))

(defthm next-largest-is-strictly-smaller-unless-equal
  (implies
   (and
    (< n (n))
    (< k (n))
    (natp n)
    (natp i)
    (natp k)
    (<= i n)
    (< (f k) (f i)))
   (or (equal i (next-largest k n))
       (< (f (next-largest k n))
          (f i))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((< k n))
           :use next-largest-is-next)))

;; Every value n has a unique next largest value.
;; Every unique value of next largest has an n.
;; There is a bijection between n and ordered n.

(defun nth-k (i k n)
  (declare (xargs :measure (nfix (- (f (max-f n)) (f k)))
                  :hints (("Goal" :do-not-induct t))))
  (if (not (and (natp n) (natp k))) 0
    (if (or (<= (n) n) (< n k)) (max-f n)
      (if (zp i) (nfix k)
        (if (<= (f (max-f n)) (f k)) (max-f n)
          (let ((k (next-largest k n)))
            (nth-k (1- i) k n)))))))

(defthm natp-nth-k
  (natp (nth-k i k n)))

(defthm nth-k-upper-bound
  (implies
   (natp n)
   (<= (nth-k i k n) n))
  :rule-classes :linear)

(defthm weak-nth-k-base-ordering
  (implies
   (and
    (natp n)
    (natp i)
    (natp m)
    (< n (n))
    (<= m n))
   (<= (f m) (f (nth-k i m n)))))

(defthm strong-nth-k-base-ordering
  (implies
   (and
    (natp n)
    (natp i)
    (natp m)
    (< n (n))
    (<= m n)
    (< 0 i)
    (< (f m) (f (max-f n))))
   (< (f m) (f (nth-k i m n)))))

(defthm nth-k-nth-k
  (implies
   (and
    (natp m)
    (<= m n)
    (natp i)
    (natp j))
   (equal (nth-k i (nth-k j m n) n)
          (nth-k (+ i j) m n))))

(encapsulate
    ()

  (local
   (defthmd strong-nth-k-ordering-helper
     (implies
      (and
       (natp n)
       (natp i)
       (< 0 i)
       (natp k)
       (< n (n))
       (<= k n)
       (< (f (nth-k j k n)) (f (max-f n))))
      (< (f (nth-k j k n)) (f (nth-k i (nth-k j k n) n))))
     :hints (("Goal" :do-not-induct t
              :in-theory (disable nth-k-nth-k)))))

  (defthm strong-nth-k-ordering
    (implies
      (and
       (natp n)
       (natp i)
       (natp j)
       (< j i)
       (natp k)
       (< n (n))
       (<= k n)
       (< (f (nth-k j k n)) (f (max-f n))))
      (< (f (nth-k j k n)) (f (nth-k i k n))))
    :hints (("Goal" :do-not-induct t
             :use (:instance strong-nth-k-ordering-helper
                             (i (- i j))))))

  )

;; (defun ord-of-i (i n)
;;   (if (equal (f i) (f n)) (nfix n)
;;     (if (equal (f i) (f (min-f n))) 0
;;       (if (zp n) 0
;;         (if (< (f n) (f i)) (1+ (ord-of-i i (1- n)))
;;           (ord-of-i i (1- n)))))))

;; max
;;
;; v
;;
;; min

;; dag
;; (defthm ord-of-i-next-largest
;;   (implies
;;    (and
;;     (natp n)
;;     (natp k)
;;     (<= k n))
;;    (equal (ord-of-i (next-largest k n) n)
;;           (1+ (ord-of-i k n)))))

;; (defthm ord-of-i-steps-to-m
;;   (equal (ord-of-i (steps-to-m m k n) n)
;;          (- (ord-of-i m n)
;;             (ord-of-i k n))))

;; All N of the original value are between *min* and *max*
;;
;; forall (i: 0 <= i <= N): (f *min*) <= (f i) <= (f *max*)
;;
;; forall (j: 0 <= j <= N): (f *min*) = (nth 0) <= (nth j) <= (nth N) = (f *max*)
;;
;; What would it mean for there to be more than N (nth ) values?
;; - it would mean that there is a (nth i) value that does not
;;   represent a value of the form (f i).  However, every nth 
;;   less than .. more to the point (f (nth j)) < (f *max*).
;;   Well, if i is greater than n, we can just return *max*.
;;   Also, if we get to *max*, it becomes a fixpoint.
;;
;; What if there were less than N (nth ) values?
;; - there is a (f i) that cannot be expressed as (nth i)
;;   (but that is easy) .. right.
;;
;; (< (nth j) (nth i))
;;
;; (= (ord (nth i)) i)
;; 
;; if M were less than N, there there is a value not visited
;; by 
;; 
;; (nth i) visits all of the values between i and j
;;
;; (forall (f i) : exists (j) (nth j) == (f i)
;;
;; If (f k) < (f j) is less than we will get there eventually.
;;
;; We would like to say it will happen in less than n steps.
;;
;; In the worst case, every other value is between (f k) and (f j)
;;
;; Every value between 0 and k are between
;;

;; (defun find-ord (i k n)
;;   (if (equal (nth-ord i *min* n) k) i
;;     (find-ord (1+ i) 

;; (defun nth-ord (i k n)
;;   (if (zp i) (min-f n)
;;     (let ((z (nth-ord (1- i) n)))
;;       (next-largest z n))))

;; (nth-ord (find-ord i k n) k n)


;; (defthm ord-nth-ord
;;   (equal (ord (nth-ord i n) n)
;;          i))

;; (defun zed (k n)
  

;; (defun f (m n)
;;   (if (end ) 0
;;     ((qual (f m)

(defun steps-to-m (m k n)
  (declare (xargs :measure (nfix (- (f (max-f n)) (f k)))
                  :hints (("Goal" :do-not-induct t))))
  (if (<= (f m) (f k)) 0
    (if (not (and (natp k) (natp m) (natp n))) 0
      (if (or (<= (n) n) (< n k) (< n m)) 0
        (if (<= (f (max-f n)) (f k)) 0
          (let ((k (next-largest k n)))
            (1+ (steps-to-m m k n))))))))

(defthm steps-to-m-signature
  (natp (steps-to-m m k n))
  :rule-classes ((:forward-chaining :trigger-terms ((steps-to-m m k n)))))

(encapsulate
    ()

  (local
   (defthm equal-common-value
     (implies
      (and
       (equal (f k) 0)
       (not (equal k m))
       (natp k)
       (natp m)
       (< k (n))
       (< m (n)))
      (not (equal (f m) 0)))
     :hints (("Goal" :use (:instance f-is-unique-over-n
                                     (i k)
                                     (j m))))))

  (defthm nth-k-steps-to-m
    (implies
     (and
      (natp n)
      (< n (n))
      (natp k)
      (<= k n)
      (natp m)
      (<= m n)
      ;; Every m between k and max-f has an index
      (<= (f m) (f (max-f n)))
      (<= (f k) (f m)))
     (equal (nth-k (steps-to-m m k n) k n) m))
    :hints (("Goal" :induct (steps-to-m m k n)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (disable next-largest-is-next)
                              :use (:instance next-largest-is-next
                                              (i m)
                                              )))))

  )

;; So .. if steps-to-m is greater than n .. (nth-k (steps) k n) has duplicates

(encapsulate
    ()

  (local (include-book "pigeon"))

  (local
   (encapsulate
       ()

     (encapsulate
         (
          ((bound) => *)
          )
       
       (local
        (defun bound () 1))
       
       (defthm natp-bound
         (posp (bound))
         :rule-classes ((:forward-chaining :trigger-terms ((bound)))))
       )

     (defun nth-fn (i)
       (let ((n (1- (bound))))
         (nth-k i (min-f n) n)))
     
     (pigeon::hole-proof nth-fn (bound))
     
     ))
  
  (defun-sk exists-nth-duplicates (m n)
    (exists (a b) (and (natp a)
                       (natp b)
                       (<= a m)
                       (<= b m)
                       (not (equal a b))
                       (equal (nth-k a (min-f n) n) (nth-k b (min-f n) n)))))

  (in-theory (disable exists-nth-duplicates))

  (defthm nth-k-pigeon-hole-proof
    (implies
     (and
      (integerp m)
      (natp n)
      (< (1+ n) m))
     (exists-nth-duplicates m n))
    :otf-flg t
    :hints (("Goal" :use (:functional-instance (:instance NTH-FN-PIGEON-HOLE-PROPERTY
                                                          (pigeon::m m))
                                               (nth-fn (lambda (i) (nth-k i (min-f n) n)))
                                               (bound (lambda () (1+ (nfix n))))
                                               (EXISTS-NTH-FN-DUPLICATES 
                                                (lambda (x) (exists-nth-duplicates x n)))
                                               (EXISTS-NTH-FN-DUPLICATES-witness 
                                                (lambda (x) (exists-nth-duplicates-witness x n)))
                                               ))
            (and stable-under-simplificationp
                 '(:use (:instance exists-nth-duplicates-suff
                                   (n n)
                                   (a pigeon::a)
                                   (m pigeon::m)
                                   (b pigeon::b))))
            (and stable-under-simplificationp
                 '(:in-theory (enable exists-nth-duplicates)))))
  
  )

;; We want to show that (steps-to-m m k n) is less then N

;; Or do we just want to show that (nth-k) is <= (max-f n)
;; - that sounds easy

(defthm steps-to-m-nth-k
  (implies
   (and
    (natp n)
    (< n (n))
    (natp k)
    (<= k n)
    (natp i)
    (<= i (steps-to-m (max-f n) k n)))
   (equal (steps-to-m (nth-k i k n) k n) i))
  :hints (("Goal" :induct (nth-k i k n)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:use (:instance strong-nth-k-base-ordering
                                 (m k))))
          ))

(defthmd equal-zero-implies-equal
  (implies
   (and
    (equal (f I) 0)
    (equal (f J) 0)
    (natp I)
    (natp J)
    (< I (n))
    (< J (n)))
   (equal I J))
  :hints (("goal" :use (:instance F-IS-UNIQUE-OVER-N
                                  )))
  :rule-classes :forward-chaining)
