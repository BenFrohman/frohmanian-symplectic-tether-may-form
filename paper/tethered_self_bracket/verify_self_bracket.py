# Sympy check: so(3)* Lie-Poisson bracket + Frohmanian tether T(F,G) = -k w <Pi_u dF, Pi_u dG>
import sympy as sp
m1,m2,m3,k,w=sp.symbols('m1 m2 m3 kappa w',real=True)
m=sp.Matrix([m1,m2,m3])
def grad(F): return sp.Matrix([sp.diff(F,v) for v in (m1,m2,m3)])
def LP(F,G): return (-m.dot(grad(F).cross(grad(G))))       # {F,G}_LP = -m.(dF x dG)
u=sp.Matrix([1,0,0])
def Pi(x): return x-(u.dot(x)/u.dot(u))*u
def T(F,G): return -k*w*Pi(grad(F)).dot(Pi(grad(G)))
def tb(F,G): return sp.expand(LP(F,G)+T(F,G))
F=m2; G=m3; Hf=m1*m2*m3
# LP: antisymmetric, Jacobi
assert sp.simplify(LP(F,G)+LP(G,F))==0
for (a,b,c) in [(m1**2,m2*m3,m3),(Hf,m1+m2**2,m3**3)]:
    assert sp.simplify(LP(a,LP(b,c))+LP(b,LP(c,a))+LP(c,LP(a,b)))==0
# Casimir C=|m|^2 is LP-central
C=m.dot(m); assert all(sp.simplify(LP(C,X))==0 for X in (m1,m2,m3))
# self-bracket
print('{F,F}_LP =',LP(F,F)); print('{F,F}_tethered =',tb(F,F))
assert tb(F,F)==-k*w
print('numeric kappa=3/2,w=2:',tb(F,F).subs({k:sp.Rational(3,2),w:2}))
print('{C,m2}_tethered (Casimir not central) =',sp.factor(tb(m2,C)))
assert sp.simplify(tb(m2,C))!=0
print('OK')
