#!/usr/bin/env python3
import math
import sys

def smod(x,q):
    x = x % q
    return x if 2*x <= q else x - q

def div(n,d):
    return n//d

def quotients(x,q):
    mn = smod(x,q)
    m  = 1
    mx = q if mn < 0 else -q
    k  = 0
    res = []
    while (mx != 0 and mn != 0):
        q = div(abs(mx),abs(mn))
        res += [q]
        ##print(" {}/{}  {}  {}/{}".format(mx,k,q,mn,m))
        (mx,k,mn,m) = (mn, m, mx + q*mn, k + q*m)
    if mx == 0:
        return (res,mn)
    else:
        return (res,mx)

## m*mx - k*mn = C
## m*(mx + mn) - (k + m)*mn = C
## m*mx + m*mn - k*mn - m*mn = C
## m*mx - k*mn = C

## m*mx + k*mn = C
## m*mx + a*m*mn = C
## m(mx + a*mn) = C
## mx + a*mn = C/m
## make a >= 1
## as mn gets smaller, mx gets bigger faster
## 
## m + am = s+
## m(1+a) = s+
## m = s+/(1+a)
## 
## can both mx and mn be greater than s- ?
## mx(1 + a*b) = C/m
## mx = 

## m*mx <= Q/2 or k*mn <= Q/2

## m*P + k*R <= Q
## P + R = m
## P = m - R
##
## m*(m - R) + a*m*R <= Q
## mm - mR + a*m*R <= Q
## mm + (a-1)*R <= Q
##
## R <= (Q - mm)/(a-1)

def fracs(x,q):
    mn = smod(x,q)
    m  = 1
    mx = q if mn < 0 else -q
    s  = 1 if mn < 0 else -1
    k  = 0
    while (mx != 0 and mn != 0):
        #print("{} {} {} {} : {}".format(mn,m,mx,k,s*(m*mx-k*mn)))
        if (((mx * mx) < q) and ((k * k) < q)):
            return (mx,k)
        if (((mn * mn) < q) and ((m * m) < q)):
            return (mn,m)
        if abs(mn) > abs(mx):
            (mn,m) = (mx + mn, k + m)
        else:
            (mx,k) = (mx + mn, k + m)
    return (0,0)

def defrac(p):
    for v in range(1,p):
        (n,d) = fracs(v,p)
        print("{} : {}/{}".format(v,n,d))
    return 0

def dequote(p):
    for v in range(1,p):
        (res,g) = quotients(v,p)
        print("{} : {} {}".format(v,res,g))

def follow1(v,p):
    x = v
    for _ in range(100):
        (n,d) = fracs(x,p)
        print("{}/{}".format(n,d))
        y = n*d
        if (y == x):
            break
        x = y

def follow(f1,f2):
    p = f1*f2
    hist = {}
    dcnt = {}
    miss = 0
    for v in range(1,p):
        x = v
        for i in range(1,1000):
            (n,d) = fracs(x,p)
            y = n*d
            if (y == x):
                break
            if n == 0 or n == 0:
                break
            if abs(n) == f1 or abs(n) == f2:
                break
            if d == f1 or d == f2:
                break
            if i % 70 == 0:
                y = y * 16
            x = y
        dcnt[i] = dcnt.get(i,0) + 1
        if n != 0 and n != 0:
            if abs(n) != f1 and abs(n) != f2:
                if d != f1 and d != f2:
                    if d != 1:
                        miss += 1
                        (n0,d0) = fracs(v,p)
                        print("{} : {}/{} {}/{}".format(v,n0,d0,n,d))
        hist[n] = 1 + hist.get(n,0)
        hist[d] = 1 + hist.get(d,0)
    for i in range(int(math.sqrt(p)) + 1):
        print("{} : {}".format(i,hist.get(i,0) + hist.get(-i,0)))
    acc = 0.0
    for index in range(1000):
        acc += dcnt.get(index,0)
        print("{} {}".format(index,acc/p))
    return miss

if __name__ == "__main__":
    sys.exit(defrac(17))
