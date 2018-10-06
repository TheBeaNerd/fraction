##
## The functions in this file were motivated by the following
## observation.  You can start with a list containing only (1,1).  You
## can iterate that list by adding each two adjacent numbers and
## placing their sum between them,
##
## (1 1)
## (1 2 1)
## (1 3 2 3 1)
## (1 4 3 5 2 5 3 4 1)
##
## etc.
##
## If you look as these as the denominators of normalized
## fractions, the numbers appear in "order" ..
##
## (0/1             1/2             1/1)
## (0/1     1/3     1/2     2/3     1/1)
## (0/1 1/4 1/3 2/5 1/2 3/5 2/3 3/4 1/1)
##
## Note: all of the /5 fractions aren't there yet ..
##
## (1 5 4 7 3 8 5 7 2 7 5 8 3 7 4 5 1)
##
## There we go .. now we have all the /5's
##
## Note, too, that this process will never generate denormal
## fractions.  For example, 2/4 does not appear in the list.
##
## Even more curious: You can space the elements in the list according
## to a metric that maps them onto the fractions they represent.  If
## you are adding n and m, the new entry can be placed in the location
## n/(n+m) between them ie: closer to the larger denominator.  This
## can be done using fractions (the leftmost is at location 0.0 and
## the rightmost is at 1.0) or using any number range (the left is 0
## and the right is P).
##
## Well, we tried this for various values of P and tried to identify
## the best fraction for representing a given number x between 0 and
## P.  Doing so revealed a pattern and led to the functions below.
## The "d" arguments correspond to the denominator.  The "n" arguments
## correspond to the numerator (the location beween 0 and P).
##
## As it turns out, the functions below compute more than just the
## best fraction for a value between 0 and P.  They compute the
## modular inverse of x mod P.  Ultimately I think this is just a slow
## variant of euclids algorithm in fancy wrapping.
##
def c2rec(n1,d1,n2,d2):
    print n1,"/",d1," ",(- n2),"/",d2
    if ((n1 <= 1) or (n2 <= 1)):
        return min(n1,n2)
    if (n2 <= n1):
      return c2rec(n1-n2,d1+d2,n2,d2)
    if (n1 < n2):
      return c2rec(n1,d1,n2-n1,d1+d2)
    else:
      return n1

def c2(x,p):
    return c2rec(x,1,p,0)

##
## a/b = c/d
## 
## a + k(c) = b + k(d)
## k(c-d) = (b-a)
## k = (b-a)/(c-d)
## k = -(a-b)/-(d-c)
## k = (a-b)/(d-c)
##
## c + m(a) = d + m(b)
## m(a-b) = (d-c)
## m = (d-c)/(a-b)
##
## e' = a + k(c) - b + k(d)
## e' = (a-b) - k(c-d)
## 

def sign(x):
    return (0 if (x == 0) else (1 if (x > 0) else -1))

def div(n,d):
    sn = sign(n)
    sd = sign(d)
    s = sd*sn
    n = sn*n
    d = sd*d
    q = n / d
    m = n % d
    if (m*2 > d):
        q = q + 1
    return s*q

def same_rec(a,b,c,d):
    print a,b," ",c,d
    x = (a-b)
    y = (d-c)
    if (abs(y)<=1):
        return y
    q = div(x,y)
    return same_rec(c,d,a+q*c,b+q*d)

def same(a,b,c,d):
    x = abs(a-b)
    y = abs(d-c)
    if (x<y):
        return same_rec(c,d,a,b)
    return same_rec(a,b,c,d)

def s2(x,p):
    return same_rec(x,1,p,0)

## c2(113,5233)
