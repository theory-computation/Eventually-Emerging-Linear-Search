#!/usr/bin/env python3
from dataclasses import dataclass
from fractions import Fraction
from math import gcd
from functools import reduce

Q = Fraction

@dataclass(frozen=True)
class E:
    name: str
    kind: str
    sign: int = 0
    level: int = -1
    comp: int = -1
    z: Fraction = Q(0)
    pq: str = ""

def first_hit_reps(X, C):
    """Exact reflection-reduced first-hit interleavings."""
    X = tuple(map(Q, X))
    C = Q(C)
    L = len(X)
    seq = []

    def dfs(ip, im, lb):
        if lb > C:
            return
        if ip == L and im == L:
            yield tuple(seq)
            return

        if not seq:
            seq.append(E("Fp0", "F", 1, 0))
            yield from dfs(1, 0, lb)
            seq.pop()
            return

        if ip < L:
            nlb = lb
            if im > 0:
                nlb = max(nlb, Q(1) + Q(2) * X[im-1] / X[ip])
            seq.append(E(f"Fp{ip}", "F", 1, ip))
            yield from dfs(ip+1, im, nlb)
            seq.pop()

        if im < L:
            nlb = lb
            if ip > 0:
                nlb = max(nlb, Q(1) + Q(2) * X[ip-1] / X[im])
            seq.append(E(f"Fm{im}", "F", -1, im))
            yield from dfs(ip, im+1, nlb)
            seq.pop()

    yield from dfs(0, 0, Q(1))


def _lcm(a, b):
    return abs(a*b) // gcd(a,b) if a and b else 0

def canonical_le(row, rhs):
    """
    Canonical positive integer scaling of an inequality row <= rhs.
    We never multiply inequalities by a negative scalar.
    """
    row = {int(k): Q(v) for k,v in row.items() if Q(v) != 0}
    rhs = Q(rhs)

    dens = [v.denominator for v in row.values()] + [rhs.denominator]
    L = reduce(_lcm, dens, 1)

    ir = {k:int(v*L) for k,v in row.items()}
    ib = int(rhs*L)

    vals = [abs(v) for v in ir.values() if v] + ([abs(ib)] if ib else [])
    g = reduce(gcd, vals) if vals else 1
    if g > 1:
        ir = {k:v//g for k,v in ir.items()}
        ib //= g

    return tuple(sorted(ir.items())), ib

def canonical_eq(row, rhs):
    row, rhs = canonical_le(row, rhs)
    if row:
        first = row[0][1]
        if first < 0:
            row = tuple((k,-v) for k,v in row)
            rhs = -rhs
    elif rhs < 0:
        rhs = -rhs
    return row, rhs


class ExactLP:
    def __init__(self, seq, X, C, ratio, depth):
        self.seq = list(seq)
        self.X = list(map(Q, X))
        self.C = Q(C)
        self.ratio = ratio.lower()
        self.depth = depth

        self.fpos = {e.name:i for i,e in enumerate(seq)}
        self.events = {e.name:e for e in seq}

        for comp in range(1, depth+1):
            for z in (Q(-1),Q(1)):
                tag = "m" if z < 0 else "p"
                for pq in ("P","Q"):
                    e = E(f"{pq}{comp}{tag}", "B",
                          comp=comp, z=z, pq=pq)
                    self.events[e.name] = e

        B = max(self.C*x for x in self.X)
        extra = [
            self.C*(self.C*self.X[i] + 1)
            for i in range(1, depth+1)
        ]
        if extra:
            B = max(B, max(extra))

        self.names = []
        self.vi = {}
        self.bounds = []

        for e in self.events.values():
            for q in ("t","L","R"):
                self.vi[(q,e.name)] = len(self.names)
                self.names.append(f"{q}:{e.name}")
                self.bounds.append(
                    (Q(0),B) if q=="t" else (-B,B)
                )

        self.base_rows = []
        self.base_eqs = []
        self._build_base(self.base_rows,self.base_eqs)

    def idx(self,q,e):
        return self.vi[(q,e.name if isinstance(e,E) else e)]

    @staticmethod
    def le(rows,d,rhs):
        rows.append(({k:Q(v) for k,v in d.items()},Q(rhs)))

    @staticmethod
    def eq(eqs,d,rhs):
        eqs.append(({k:Q(v) for k,v in d.items()},Q(rhs)))

    def speed(self,rows,a,b):
        ta,tb=self.idx("t",a),self.idx("t",b)
        for q in ("L","R"):
            pa,pb=self.idx(q,a),self.idx(q,b)
            self.le(rows,{pb:1,pa:-1,tb:-1,ta:1},0)
            self.le(rows,{pa:1,pb:-1,tb:-1,ta:1},0)

    def _build_base(self,r,e):
        for ev in self.events.values():
            t,L,R=self.idx("t",ev),self.idx("L",ev),self.idx("R",ev)
            self.le(r,{L:1,t:-1},0)
            self.le(r,{L:-1,t:-1},0)
            self.le(r,{R:1,t:-1},0)
            self.le(r,{R:-1,t:-1},0)
            self.le(r,{L:1,R:-1},0)

        for ev in self.seq:
            x=self.X[ev.level]
            self.eq(
                e,
                {self.idx("R" if ev.sign>0 else "L",ev):1},
                x if ev.sign>0 else -x,
            )
            self.le(
                r,
                {
                    self.idx("t",ev):1,
                    self.idx("R",ev):1,
                    self.idx("L",ev):-1,
                },
                self.C*x,
            )

        for a,b in zip(self.seq[:-1],self.seq[1:]):
            self.le(r,{self.idx("t",a):1,self.idx("t",b):-1},0)
            self.speed(r,a,b)

    def H(self,comp):
        return self.events[
            max(
                (f"Fm{comp}",f"Fp{comp}"),
                key=lambda n:self.fpos[n]
            )
        ]

    def slot_rows(self,ev,s):
        rows=[]
        t=self.idx("t",ev)
        n=len(self.seq)

        if s>0:
            f=self.seq[s-1]
            self.le(rows,{self.idx("t",f):1,t:-1},0)
            self.speed(rows,f,ev)

        if s<n:
            f=self.seq[s]
            self.le(rows,{t:1,self.idx("t",f):-1},0)
            self.speed(rows,ev,f)

        plus=[f for f in self.seq[s:] if f.sign>0]
        minus=[f for f in self.seq[s:] if f.sign<0]

        if plus:
            self.le(
                rows,
                {self.idx("R",ev):1},
                min(self.X[f.level] for f in plus),
            )
        if minus:
            self.le(
                rows,
                {self.idx("L",ev):-1},
                min(self.X[f.level] for f in minus),
            )
        return rows

    def relaxed_visit_rows(self,ev,z):
        rows=[]
        self.le(rows,{self.idx("L",ev):1},Q(z))
        self.le(rows,{self.idx("R",ev):-1},-Q(z))
        return rows

    def update_noslot(self,comp,z,old_record,relaxed=True):
        rows=[]
        eqs=[]
        z=Q(z)
        tag="m" if z<0 else "p"
        P=self.events[f"P{comp}{tag}"]
        Qe=self.events[f"Q{comp}{tag}"]
        H=self.H(comp)

        if relaxed:
            rows += self.relaxed_visit_rows(P,z)
            rows += self.relaxed_visit_rows(Qe,z)

        self.le(rows,{self.idx("t",P):1,self.idx("t",H):-1},0)
        self.le(rows,{self.idx("t",H):1,self.idx("t",Qe):-1},0)
        self.speed(rows,P,Qe)

        rhs=self.C*abs(z) if self.ratio=="ea" else Q(0)
        self.le(
            rows,
            {
                self.idx("t",Qe):1,
                self.idx("R",Qe):1,
                self.idx("L",Qe):-1,
                self.idx("t",P):-self.C,
            },
            rhs,
        )

        F0=self.events["Fp0" if z>0 else "Fm0"]
        self.le(
            rows,
            {self.idx("t",F0):1,self.idx("t",P):-1},
            0,
        )

        if old_record is not None:
            oldP,oldQ=old_record
            self.le(
                rows,
                {self.idx("t",oldQ):1,self.idx("t",P):-1},
                0,
            )

        return rows,eqs,P,Qe

    def event_slot_rows(
        self,ev,s,prior_assigned=(),external_assigned=()
    ):
        rows=self.slot_rows(ev,s)

        for old,sold in list(prior_assigned)+list(external_assigned):
            if sold<s:
                self.speed(rows,old,ev)
            elif s<sold:
                self.speed(rows,ev,old)
        return rows

    def update_common(
        self,comp,z,sp,sq,old_record,prior_assigned,
        relaxed=True,external_assigned=()
    ):
        rows,eqs,P,Qe=self.update_noslot(
            comp,z,old_record,relaxed=relaxed
        )
        rows += self.event_slot_rows(
            P,sp,prior_assigned,external_assigned
        )
        rows += self.event_slot_rows(
            Qe,sq,prior_assigned,external_assigned
        )
        return rows,eqs,P,Qe

    def exact_visitor_eq(self,ev,z,v):
        return [
            (
                {self.idx("L" if v==0 else "R",ev):Q(1)},
                Q(z),
            )
        ]

    def survival_rows(self,comp,z,record):
        rows=[]
        P,Qe=record
        H=self.H(comp)

        self.le(rows,{self.idx("t",P):1,self.idx("t",H):-1},0)
        self.le(rows,{self.idx("t",H):1,self.idx("t",Qe):-1},0)

        rhs=self.C*abs(Q(z)) if self.ratio=="ea" else Q(0)
        self.le(
            rows,
            {
                self.idx("t",Qe):1,
                self.idx("R",Qe):1,
                self.idx("L",Qe):-1,
                self.idx("t",P):-self.C,
            },
            rhs,
        )
        return rows

    def slot_pairs(self,comp,z):
        h=self.fpos[self.H(comp).name]
        f0=self.fpos["Fp0" if z>0 else "Fm0"]
        n=len(self.seq)

        for sp in range(max(0,f0),min(n+1,h+2)):
            for sq in range(max(0,h),n+1):
                yield sp,sq

    def all_base_inequalities(self):
        """
        Convert base rows, equalities, and variable bounds to Ax<=b.
        This is the canonical form used by Farkas certification.
        """
        out=[]

        for d,b in self.base_rows:
            out.append(("base",canonical_le(d,b)))

        for d,b in self.base_eqs:
            out.append(("eq+",canonical_le(d,b)))
            out.append(("eq-",canonical_le({k:-v for k,v in d.items()},-b)))

        for j,(lo,hi) in enumerate(self.bounds):
            out.append(("lb",canonical_le({j:-1},-lo)))
            out.append(("ub",canonical_le({j:1},hi)))

        return out
