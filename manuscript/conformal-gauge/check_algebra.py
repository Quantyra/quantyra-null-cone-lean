"""Supplementary exact manuscript algebra; does not invoke Lean.

Requires SymPy 1.14.0. Identities are polynomial checks; analytic domains,
probability transport and universal theorem scope come from the written
proofs and the retained GCP acceptance, not from this script.
"""
import json
from fractions import Fraction as Q
from pathlib import Path
import sympy as s

checks = []
def zero(expression, name):
    assert s.expand(expression) == 0, name
    checks.append(name)

a, t, x, y, T, X, Y, r, k, w = s.symbols('a t x y T X Y r k w')
c = 1-a*a
D = (1+a*t)**2-a*a*(x*x+y*y)
N = (t+a)*(1+a*t)-a*(x*x+y*y)
A = s.Matrix([N,c*x,c*y])
p = s.Matrix([t,x,y]); q = s.Matrix([T,X,Y]); E = s.diag(-1,1,1)
B = D*A.jacobian(p)-A*s.Matrix([[s.diff(D,z) for z in p]])
bilinear = B.T*E*B-c*c*D*D*E
for i in range(3):
    for j in range(3):zero(bilinear[i,j],f'Cartesian conformal polynomial {i}{j}')
zero(B.det()-c**3*D**3,'Cartesian determinant polynomial')
sub = {t:T,x:X,y:Y}
Dq = D.xreplace(sub); Aq=A.xreplace(sub)
diff = Aq*D-A*Dq
zero((diff.T*E*diff)[0]-c*c*D*Dq*((q-p).T*E*(q-p))[0],
     'two-point Lorentz separation numerator')
inverse_den = (D-a*N)**2-a*a*c*c*(x*x+y*y)
zero(inverse_den-c*c*D,'inverse denominator numerator')
zero((N-a*D)*(D-a*N)+a*c*c*(x*x+y*y)-t*inverse_den,'inverse time numerator')
for z in (x,y):zero(c*c*z*D-z*inverse_den,f'inverse spatial numerator {z}')
Dr=(1+a*t)**2-a*a*r*r; Nr=(t+a)*(1+a*t)-a*r*r
for sign in (-1,1):zero((Nr+sign*c*r)*(1+a*(t+sign*r))-Dr*(t+sign*r+a),f'null formula {sign}')
literature=((1+w)-k*(1-w))/((1+w)+k*(1-w))
parameter=(1-k)/(1+k)
assert s.cancel(literature-(w+parameter)/(1+parameter*w))==0
assert s.cancel(-literature.xreplace({w:-w,k:1/k})-(w+parameter)/(1+parameter*w))==0
checks.extend(['CHM plus null parameter conversion','CHM minus null sign conversion'])
aa=Q(1,100); low=((1-aa)/(1+aa))**3; high=((1+aa)/(1-aa))**3
assert Q(1,2)<low<1<high<Q(3,2)
assert Q(9,10)<(1-aa)**2<(1+aa)**2<Q(11,10)
assert 2*aa+6*aa**2<=Q(3,100)
assert Q(363,100)/Q(9,10)**6<=7
assert 7*Q(3,100)<2
anchor=((1-aa*aa)/(1-aa/2)**2)**3
assert anchor==(Q(39996,39601))**3>1
checks.extend(['exact density interval','reciprocal-cube interval and constant',
               'Euclidean denominator/density Lipschitz constants','exact interior anchor'])
result={'status':'PASS','sympy_version':s.__version__,'identities_and_bounds':checks,
        'density_lower':str(low),'density_upper':str(high),'density_lipschitz_bound':'21/100',
        'anchor_density_minus_one':str(anchor-1),'lean_invocations':0,
        'scope':'exact algebra only; written domain/probability proofs and accepted GCP Lean evidence are separate'}
Path(__file__).with_name('algebra-check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(result,indent=2))
