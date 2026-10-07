"""Exact finite sanity checks for the analytic conformal-diamond counterexample.

No Lean invocation. Universal claims are proved in the accompanying note.
"""
from fractions import Fraction as F
from itertools import product, combinations
import json


def transform(a, z):
    t, x, y = z
    den = (1 + a*t)**2 - a*a*(x*x + y*y)
    num = ((t+a)*(1+a*t)-a*(x*x+y*y), (1-a*a)*x, (1-a*a)*y)
    dden = (2*a*(1+a*t), -2*a*a*x, -2*a*a*y)
    dnum = ((1+a*a+2*a*t, -2*a*x, -2*a*y),
            (F(0), 1-a*a, F(0)), (F(0), F(0), 1-a*a))
    jac = tuple(tuple((dnum[i][j]*den-num[i]*dden[j])/den**2
                      for j in range(3)) for i in range(3))
    return tuple(n/den for n in num), jac, (1-a*a)/den


def determinant(m):
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
            -m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
            +m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))


def inside(z):
    t, x, y = z
    return abs(t)<1 and x*x+y*y < (1-abs(t))**2


def chronology(p, q):
    dt, dx, dy = (q[i]-p[i] for i in range(3))
    return dt>0 and dt*dt>dx*dx+dy*dy


def main():
    a = F(1, 100)
    low, high = ((1-a)/(1+a))**3, ((1+a)/(1-a))**3
    lip = 6*a*high*(1+2*a)/(1-a)**2
    assert F(1, 2)<low<1<high<F(3, 2) and lip<2
    points = [tuple(F(v, 6) for v in p) for p in product(range(-4, 5), repeat=3)]
    points = [p for p in points if inside(p)]
    images = []
    eta = (-1, 1, 1)
    for p in points:
        q, jac, omega = transform(a, p)
        assert inside(q) and transform(-a, q)[0] == p
        assert determinant(jac) == omega**3 > 0
        for i, j in product(range(3), repeat=2):
            assert sum(eta[k]*jac[k][i]*jac[k][j] for k in range(3)) == (
                eta[i]*omega**2 if i == j else 0)
        rho = transform(-a, q)[2]**3
        assert low <= rho <= high
        images.append(q)
    for i, j in combinations(range(len(points)), 2):
        assert chronology(points[i], points[j]) == chronology(images[i], images[j])
        assert chronology(points[j], points[i]) == chronology(images[j], images[i])
    assert transform(-a, (F(1), F(0), F(0)))[2]**3 == high
    print(json.dumps({"status": "PASS", "points": len(points),
                      "directed_pair_checks": len(points)*(len(points)-1),
                      "a": str(a), "density_lower": str(low),
                      "density_upper": str(high), "lipschitz_upper": str(lip),
                      "scope": "finite rational algebra checks; analytic proof in note"}, indent=2))


if __name__ == "__main__":
    main()
