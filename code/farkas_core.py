#!/usr/bin/env python3
"""Exact Farkas support discovery/reconstruction for EELS2 old-LP certification.

Numerical LP solving is used only to discover candidate infeasibility and a dual
support.  A branch is certified only after Fraction-exact verification of
    y >= 0,  y^T A = 0,  y^T b < 0.
"""
from fractions import Fraction as Q
from hashlib import sha256
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
import sympy as sp
from exact_model import canonical_le


def compressed_inequalities(lp, rows=(), eqs=()):
    """Deterministic exact Ax<=b, including base system and variable bounds.

    Every row is first canonicalized by positive integer scaling.  Equalities
    become two inequalities.  Identical canonical LHS rows retain the smallest
    RHS.  The final system is sorted by LHS, so row indices are deterministic.
    """
    raw=[]
    for d,b in list(lp.base_rows)+list(rows):
        r,bb=canonical_le(d,b); raw.append((r,int(bb)))
    for d,b in list(lp.base_eqs)+list(eqs):
        r,bb=canonical_le(d,b); raw.append((r,int(bb)))
        r,bb=canonical_le({k:-v for k,v in d.items()},-b); raw.append((r,int(bb)))
    for j,(lo,hi) in enumerate(lp.bounds):
        r,bb=canonical_le({j:-1},-lo); raw.append((r,int(bb)))
        r,bb=canonical_le({j: 1}, hi); raw.append((r,int(bb)))

    best={}
    for r,b in raw:
        if r not in best or b<best[r]: best[r]=b
    return [(dict(r),Q(best[r])) for r in sorted(best)]


def system_hash(ineq):
    payload=[[[[int(j),int(Q(v).numerator),int(Q(v).denominator)] for j,v in sorted(d.items())],
              [int(Q(b).numerator),int(Q(b).denominator)]] for d,b in ineq]
    return sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest()


def primal_float_status(ineq,nvars):
    """HiGHS primal screen.  Status 2 means candidate infeasibility only."""
    m=len(ineq); A=lil_matrix((m,nvars),dtype=float); b=np.empty(m)
    for i,(d,rhs) in enumerate(ineq):
        for j,v in d.items(): A[i,j]=float(v)
        b[i]=float(rhs)
    r=linprog(np.zeros(nvars),A_ub=A.tocsr(),b_ub=b,
              bounds=[(None,None)]*nvars,method='highs',
              options={'presolve':False})
    return int(r.status)


def _spq(q):
    q=Q(q); return sp.Rational(q.numerator,q.denominator)


def _reconstruct_on_support(ineq,nvars,support,y0):
    rows=[]; rhs=[]
    for j in range(nvars):
        rows.append([_spq(ineq[i][0].get(j,Q(0))) for i in support]); rhs.append(sp.Integer(0))
    rows.append([sp.Integer(1)]*len(support)); rhs.append(sp.Integer(1))
    M=sp.Matrix(rows); rr=sp.Matrix(rhs)
    try:
        sol,params=M.gauss_jordan_solve(rr)
    except Exception:
        return None
    if params.rows*params.cols:
        # Historical exactifier fallback: fit free parameters to the numerical
        # basic point, then exact verification below decides validity.
        syms=sorted(set().union(*[v.free_symbols for v in sol]),key=str)
        if syms:
            eqs=[]
            for k,val in enumerate(sol):
                q=Q(float(y0[support[k]])).limit_denominator(10**8)
                eqs.append(sp.Eq(val,sp.Rational(q.numerator,q.denominator)))
            ss=sp.solve(eqs,syms,dict=True)
            if not ss: return None
            sol=sol.subs(ss[0])
    ys=[Q(0)]*len(ineq)
    for idx,val in zip(support,sol):
        if getattr(val,'free_symbols',None): return None
        try:q=Q(int(val.p),int(val.q))
        except Exception:return None
        if q<0:return None
        ys[idx]=q
    return ys


def verify_farkas(ineq,nvars,y):
    if len(y)!=len(ineq) or any(Q(q)<0 for q in y): return None
    for j in range(nvars):
        s=sum((Q(y[i])*Q(ineq[i][0].get(j,Q(0))) for i in range(len(ineq))),Q(0))
        if s!=0:return None
    dot=sum((Q(y[i])*Q(ineq[i][1]) for i in range(len(ineq))),Q(0))
    return dot if dot<0 else None


def exact_farkas(ineq,nvars,dual_tol=-1e-10,support_tols=(1e-9,1e-8,1e-7,1e-6)):
    """Return an exactly verified Farkas multiplier or None."""
    m=len(ineq); A=np.zeros((m,nvars),dtype=float); b=np.empty(m)
    for i,(d,rhs) in enumerate(ineq):
        for j,v in d.items(): A[i,j]=float(v)
        b[i]=float(rhs)
    Aeq=np.vstack([A.T,np.ones(m)]); beq=np.r_[np.zeros(nvars),1.0]
    r=linprog(b,A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*m,
              method='highs',options={'presolve':False})
    if r.status!=0 or r.fun>=dual_tol:return None
    for tol in support_tols:
        supp=[i for i,v in enumerate(r.x) if v>tol]
        if not supp:continue
        y=_reconstruct_on_support(ineq,nvars,supp,r.x)
        if y is None:continue
        dot=verify_farkas(ineq,nvars,y)
        if dot is not None:return y
    return None


def certificate_record(ineq,nvars,y):
    dot=verify_farkas(ineq,nvars,y)
    if dot is None:raise ValueError('invalid exact certificate')
    supp=[i for i,q in enumerate(y) if q]
    return {'system_sha256':system_hash(ineq),'m':len(ineq),'n':nvars,
            'support':supp,
            'y':[[Q(y[i]).numerator,Q(y[i]).denominator] for i in supp],
            'yb':[dot.numerator,dot.denominator]}


def certify_system(lp,rows=(),eqs=()):
    ineq=compressed_inequalities(lp,rows,eqs)
    st=primal_float_status(ineq,len(lp.names))
    if st!=2:return st,None
    y=exact_farkas(ineq,len(lp.names))
    if y is None:return st,None
    return st,certificate_record(ineq,len(lp.names),y)
