#!/usr/bin/env python3
"""Independent exact verifier for one EELS2 old-LP depth-7 class proof.

Trust boundary:
  * standard library only;
  * does NOT import exact_model, farkas_core, exact_producer, scipy, numpy, sympy,
    HiGHS, or any LP/MILP solver;
  * reconstructs the rational model and the deterministic branch tree independently;
  * consumes supplied Farkas certificates exactly at the nodes they claim to close;
  * verifies y >= 0, y^T A = 0, y^T b < 0 using fractions.Fraction;
  * rejects malformed, duplicate, missing-for-closure, or extraneous certificates;
  * accepts only a proof whose entire deterministic class search closes exactly.

This Stage-3 verifier is class-local.  A later theorem-level wrapper must additionally
verify coverage of every first-hit class for EA/FI and aggregate all class proofs.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import reduce
from math import gcd
from hashlib import sha256
from pathlib import Path
import argparse, json, sys

CASES={
'EA':(Q(87,20),[Q(1),Q(7719,1000),Q(15969,1000),Q(3829,200),Q(6147,250),Q(32707,1000),Q(24283,500),Q(27197,500),Q(136059,1000)]),
'FI':(Q(219,50),[Q(1),Q(1241,200),Q(10693,1000),Q(541,40),Q(3103,200),Q(4091,200),Q(28219,1000),Q(6871,125),Q(7928,125)])}
DEPTH=7

@dataclass(frozen=True)
class E:
    name:str
    kind:str
    sign:int=0
    level:int=-1
    comp:int=-1
    z:Q=Q(0)
    pq:str=""

def first_hit_reps(X,C):
    X=tuple(map(Q,X));C=Q(C);L=len(X);seq=[]
    def dfs(ip,im,lb):
        if lb>C:return
        if ip==L and im==L:
            yield tuple(seq);return
        if not seq:
            seq.append(E('Fp0','F',1,0));yield from dfs(1,0,lb);seq.pop();return
        if ip<L:
            nlb=lb
            if im>0:nlb=max(nlb,Q(1)+Q(2)*X[im-1]/X[ip])
            seq.append(E(f'Fp{ip}','F',1,ip));yield from dfs(ip+1,im,nlb);seq.pop()
        if im<L:
            nlb=lb
            if ip>0:nlb=max(nlb,Q(1)+Q(2)*X[ip-1]/X[im])
            seq.append(E(f'Fm{im}','F',-1,im));yield from dfs(ip,im+1,nlb);seq.pop()
    yield from dfs(0,0,Q(1))

def _lcm(a,b):return abs(a*b)//gcd(a,b) if a and b else 0

def canonical_le(row,rhs):
    row={int(k):Q(v) for k,v in row.items() if Q(v)!=0};rhs=Q(rhs)
    dens=[v.denominator for v in row.values()]+[rhs.denominator]
    L=reduce(_lcm,dens,1);ir={k:int(v*L) for k,v in row.items()};ib=int(rhs*L)
    vals=[abs(v) for v in ir.values() if v]+([abs(ib)] if ib else [])
    g=reduce(gcd,vals) if vals else 1
    if g>1:ir={k:v//g for k,v in ir.items()};ib//=g
    return tuple(sorted(ir.items())),ib

def system_hash(ineq):
    payload=[[[[int(j),int(Q(v).numerator),int(Q(v).denominator)] for j,v in sorted(d.items())],
              [int(Q(b).numerator),int(Q(b).denominator)]] for d,b in ineq]
    return sha256(json.dumps(payload,separators=(',',':')).encode()).hexdigest()

class ExactLP:
    def __init__(self,seq,X,C,ratio,depth=DEPTH):
        self.seq=list(seq);self.X=list(map(Q,X));self.C=Q(C);self.ratio=ratio.lower();self.depth=depth
        self.fpos={e.name:i for i,e in enumerate(seq)};self.events={e.name:e for e in seq}
        for comp in range(1,depth+1):
            for z in (Q(-1),Q(1)):
                tag='m' if z<0 else 'p'
                for pq in ('P','Q'):
                    e=E(f'{pq}{comp}{tag}','B',comp=comp,z=z,pq=pq);self.events[e.name]=e
        B=max(self.C*x for x in self.X)
        extra=[self.C*(self.C*self.X[i]+1) for i in range(1,depth+1)]
        if extra:B=max(B,max(extra))
        self.names=[];self.vi={};self.bounds=[]
        for e in self.events.values():
            for q in ('t','L','R'):
                self.vi[(q,e.name)]=len(self.names);self.names.append(f'{q}:{e.name}')
                self.bounds.append((Q(0),B) if q=='t' else (-B,B))
        self.base_rows=[];self.base_eqs=[];self._build_base()
    def idx(self,q,e):return self.vi[(q,e.name if isinstance(e,E) else e)]
    @staticmethod
    def le(rows,d,r):rows.append(({k:Q(v) for k,v in d.items()},Q(r)))
    @staticmethod
    def eq(eqs,d,r):eqs.append(({k:Q(v) for k,v in d.items()},Q(r)))
    def speed(self,rows,a,b):
        ta,tb=self.idx('t',a),self.idx('t',b)
        for q in ('L','R'):
            pa,pb=self.idx(q,a),self.idx(q,b)
            self.le(rows,{pb:1,pa:-1,tb:-1,ta:1},0);self.le(rows,{pa:1,pb:-1,tb:-1,ta:1},0)
    def _build_base(self):
        r,e=self.base_rows,self.base_eqs
        for ev in self.events.values():
            t,L,R=self.idx('t',ev),self.idx('L',ev),self.idx('R',ev)
            self.le(r,{L:1,t:-1},0);self.le(r,{L:-1,t:-1},0);self.le(r,{R:1,t:-1},0);self.le(r,{R:-1,t:-1},0);self.le(r,{L:1,R:-1},0)
        for ev in self.seq:
            x=self.X[ev.level]
            self.eq(e,{self.idx('R' if ev.sign>0 else 'L',ev):1},x if ev.sign>0 else -x)
            self.le(r,{self.idx('t',ev):1,self.idx('R',ev):1,self.idx('L',ev):-1},self.C*x)
        for a,b in zip(self.seq[:-1],self.seq[1:]):
            self.le(r,{self.idx('t',a):1,self.idx('t',b):-1},0);self.speed(r,a,b)
    def H(self,comp):return self.events[max((f'Fm{comp}',f'Fp{comp}'),key=lambda n:self.fpos[n])]
    def slot_rows(self,ev,s):
        rows=[];t=self.idx('t',ev);n=len(self.seq)
        if s>0:
            f=self.seq[s-1];self.le(rows,{self.idx('t',f):1,t:-1},0);self.speed(rows,f,ev)
        if s<n:
            f=self.seq[s];self.le(rows,{t:1,self.idx('t',f):-1},0);self.speed(rows,ev,f)
        plus=[f for f in self.seq[s:] if f.sign>0];minus=[f for f in self.seq[s:] if f.sign<0]
        if plus:self.le(rows,{self.idx('R',ev):1},min(self.X[f.level] for f in plus))
        if minus:self.le(rows,{self.idx('L',ev):-1},min(self.X[f.level] for f in minus))
        return rows
    def relaxed_visit_rows(self,ev,z):
        rows=[];self.le(rows,{self.idx('L',ev):1},Q(z));self.le(rows,{self.idx('R',ev):-1},-Q(z));return rows
    def update_noslot(self,comp,z,old_record,relaxed=True):
        rows=[];eqs=[];z=Q(z);tag='m' if z<0 else 'p';P=self.events[f'P{comp}{tag}'];Qe=self.events[f'Q{comp}{tag}'];H=self.H(comp)
        if relaxed:rows+=self.relaxed_visit_rows(P,z)+self.relaxed_visit_rows(Qe,z)
        self.le(rows,{self.idx('t',P):1,self.idx('t',H):-1},0);self.le(rows,{self.idx('t',H):1,self.idx('t',Qe):-1},0);self.speed(rows,P,Qe)
        rhs=self.C*abs(z) if self.ratio=='ea' else Q(0)
        self.le(rows,{self.idx('t',Qe):1,self.idx('R',Qe):1,self.idx('L',Qe):-1,self.idx('t',P):-self.C},rhs)
        F0=self.events['Fp0' if z>0 else 'Fm0'];self.le(rows,{self.idx('t',F0):1,self.idx('t',P):-1},0)
        if old_record is not None:
            oldP,oldQ=old_record;self.le(rows,{self.idx('t',oldQ):1,self.idx('t',P):-1},0)
        return rows,eqs,P,Qe
    def event_slot_rows(self,ev,s,prior_assigned=(),external_assigned=()):
        rows=self.slot_rows(ev,s)
        for old,sold in list(prior_assigned)+list(external_assigned):
            if sold<s:self.speed(rows,old,ev)
            elif s<sold:self.speed(rows,ev,old)
        return rows
    def update_common(self,comp,z,sp,sq,old_record,prior_assigned,relaxed=True,external_assigned=()):
        rows,eqs,P,Qe=self.update_noslot(comp,z,old_record,relaxed=relaxed)
        rows+=self.event_slot_rows(P,sp,prior_assigned,external_assigned);rows+=self.event_slot_rows(Qe,sq,prior_assigned,external_assigned)
        return rows,eqs,P,Qe
    def exact_visitor_eq(self,ev,z,v):return [({self.idx('L' if v==0 else 'R',ev):Q(1)},Q(z))]
    def survival_rows(self,comp,z,record):
        rows=[];P,Qe=record;H=self.H(comp);self.le(rows,{self.idx('t',P):1,self.idx('t',H):-1},0);self.le(rows,{self.idx('t',H):1,self.idx('t',Qe):-1},0)
        rhs=self.C*abs(Q(z)) if self.ratio=='ea' else Q(0)
        self.le(rows,{self.idx('t',Qe):1,self.idx('R',Qe):1,self.idx('L',Qe):-1,self.idx('t',P):-self.C},rhs);return rows
    def slot_pairs(self,comp,z):
        h=self.fpos[self.H(comp).name];f0=self.fpos['Fp0' if z>0 else 'Fm0'];n=len(self.seq)
        for sp in range(max(0,f0),min(n+1,h+2)):
            for sq in range(max(0,h),n+1):yield sp,sq

def inequalities(lp,rows=(),eqs=()):
    raw=[]
    for d,b in list(lp.base_rows)+list(rows):
        r,bb=canonical_le(d,b);raw.append((r,int(bb)))
    for d,b in list(lp.base_eqs)+list(eqs):
        r,bb=canonical_le(d,b);raw.append((r,int(bb)));r,bb=canonical_le({k:-v for k,v in d.items()},-b);raw.append((r,int(bb)))
    for j,(lo,hi) in enumerate(lp.bounds):
        r,bb=canonical_le({j:-1},-lo);raw.append((r,int(bb)));r,bb=canonical_le({j:1},hi);raw.append((r,int(bb)))
    best={}
    for r,b in raw:
        if r not in best or b<best[r]:best[r]=b
    return [(dict(r),Q(best[r])) for r in sorted(best)]

def norm_path(path):return tuple(tuple(x) for x in path)
def norm_context(ctx):return json.dumps(ctx,sort_keys=True,separators=(',',':'))

def cert_key(kind,context,path):return (kind,norm_context(context),norm_path(path))

def verify_certificate(ineq,nvars,rec):
    if rec.get('m')!=len(ineq):raise ValueError(f"m mismatch {rec.get('m')} != {len(ineq)}")
    if rec.get('n')!=nvars:raise ValueError(f"n mismatch {rec.get('n')} != {nvars}")
    h=system_hash(ineq)
    if rec.get('system_sha256')!=h:raise ValueError(f"system hash mismatch {rec.get('system_sha256')} != {h}")
    supp=rec.get('support');vals=rec.get('y')
    if not isinstance(supp,list) or not isinstance(vals,list) or len(supp)!=len(vals):raise ValueError('support/value mismatch')
    if len(set(supp))!=len(supp):raise ValueError('duplicate support index')
    y={}
    for i,pair in zip(supp,vals):
        if not isinstance(i,int) or not (0<=i<len(ineq)):raise ValueError('support index out of range')
        if not (isinstance(pair,list) and len(pair)==2 and isinstance(pair[0],int) and isinstance(pair[1],int) and pair[1]!=0):raise ValueError('bad rational multiplier')
        q=Q(pair[0],pair[1])
        if q<0:raise ValueError('negative multiplier')
        if q:y[i]=q
    for j in range(nvars):
        s=sum((q*Q(ineq[i][0].get(j,Q(0))) for i,q in y.items()),Q(0))
        if s!=0:raise ValueError(f'yTA nonzero at var {j}: {s}')
    dot=sum((q*Q(ineq[i][1]) for i,q in y.items()),Q(0))
    if dot>=0:raise ValueError(f'yTb not negative: {dot}')
    yb=rec.get('yb')
    if not (isinstance(yb,list) and len(yb)==2 and Q(yb[0],yb[1])==dot):raise ValueError('stored yb mismatch')
    return dot

class Pool:
    def __init__(self,proof):
        self.map={};self.used=set()
        for idx,rec in enumerate(proof.get('certificates',[])):
            try:k=cert_key(rec['kind'],rec['context'],rec['path'])
            except Exception as e:raise SystemExit(f'FAIL malformed certificate key at {idx}: {e}')
            if k in self.map:raise SystemExit(f'FAIL duplicate certificate key at {idx}')
            self.map[k]=(idx,rec)
    def test(self,lp,kind,rows,eqs,context,path):
        k=cert_key(kind,context,[list(a) for a in path]);item=self.map.get(k)
        if item is None:return False
        idx,rec=item
        try:verify_certificate(inequalities(lp,rows,eqs),len(lp.names),rec)
        except Exception as e:raise SystemExit(f'FAIL certificate {idx} kind={kind} path={path}: {e}')
        self.used.add(idx);return True
    def finish(self):
        extra=set(range(len(self.map)))-self.used
        if extra:raise SystemExit(f'FAIL extraneous/unconsumed certificates: count={len(extra)} first={min(extra)}')

class SearchVerifier:
    def __init__(self,lp,pool):self.lp=lp;self.pool=pool;self.terminals=0
    def test(self,kind,rows,eqs,context,path):return self.pool.test(self.lp,kind,rows,eqs,context,path)
    def enumerate_histories(self,z,rows0=(),eqs0=(),external=(),find_one=False,context=None):
        out=[];lp=self.lp;depth=lp.depth;context=context or {'phase':'one-side','z':int(z)}
        def dfs(comp,record,assigned,actions,rows,eqs):
            if comp>depth:
                self.terminals+=1;out.append(tuple(actions));return bool(find_one)
            if comp>1 and record is not None:
                rr=list(rows)+lp.survival_rows(comp,z,record)
                if not self.test('survival',rr,eqs,context,actions+[('S',comp)]):
                    if dfs(comp+1,record,assigned,actions+[('S',comp)],rr,eqs):return True
            base,ee,P,Qe=lp.update_noslot(comp,z,record,relaxed=True);r0=list(rows)+base;e0=list(eqs)+ee
            if self.test('updateprefix',r0,e0,context,actions+[('UP',comp)]):return False
            h=lp.fpos[lp.H(comp).name];f0=lp.fpos['Fp0' if z>0 else 'Fm0'];n=len(lp.seq)
            for sp in range(max(0,f0),min(n+1,h+2)):
                rp=r0+lp.event_slot_rows(P,sp,assigned,external)
                if self.test('pslot',rp,e0,context,actions+[('P',comp,sp)]):continue
                for vp in (0,1):
                    ep=e0+lp.exact_visitor_eq(P,z,vp)
                    if self.test('pvisitor',rp,ep,context,actions+[('PV',comp,sp,vp)]):continue
                    for sq in range(max(0,h),n+1):
                        rq=rp+lp.event_slot_rows(Qe,sq,assigned,external)
                        if self.test('qslot',rq,ep,context,actions+[('Q',comp,sp,vp,sq)]):continue
                        for vq in (0,1):
                            eq2=ep+lp.exact_visitor_eq(Qe,z,vq);act=('U',comp,sp,sq,vp,vq)
                            if self.test('exact',rq,eq2,context,actions+[act]):continue
                            if dfs(comp+1,(P,Qe),assigned+[(P,sp),(Qe,sq)],actions+[act],rq,eq2):return True
            return False
        dfs(1,None,[],[],list(rows0),list(eqs0));return out
    def replay(self,z,actions):
        lp=self.lp;rows=[];eqs=[];record=None;assigned=[]
        for a in actions:
            if a[0]=='S':rows+=lp.survival_rows(a[1],z,record)
            else:
                _,comp,sp,sq,vp,vq=a;r,e,P,Qe=lp.update_common(comp,z,sp,sq,record,assigned,relaxed=False)
                rows+=r;eqs+=e+lp.exact_visitor_eq(P,z,vp)+lp.exact_visitor_eq(Qe,z,vq);record=(P,Qe);assigned += [(P,sp),(Qe,sq)]
        return rows,eqs,assigned
    def solve_class(self):
        if self.test('base',[],[],{'phase':'base'},[]):return {'status':'CLOSED','reason':'base'}
        order=sorted((Q(-1),Q(1)),key=lambda z:sum(1 for _ in self.lp.slot_pairs(1,z)));witness={}
        for z in order:
            h=self.enumerate_histories(z,find_one=True,context={'phase':'one-side','z':int(z)})
            if not h:return {'status':'CLOSED','reason':'one-side','z':int(z)}
            witness[z]=h[0]
        for oz,iz in ((order[0],order[1]),(order[1],order[0])):
            r,e,ext=self.replay(oz,witness[oz]);ctx={'phase':'conditional-first','outer_z':int(oz),'outer_actions':[list(a) for a in witness[oz]],'inner_z':int(iz)}
            inn=self.enumerate_histories(iz,r,e,ext,True,ctx)
            if inn:return {'status':'UNRESOLVED','reason':'combined-survivor'}
        oz,iz=order;outer=self.enumerate_histories(oz,find_one=False,context={'phase':'outer-exhaustive','z':int(oz)})
        for h in outer:
            r,e,ext=self.replay(oz,h);ctx={'phase':'conditional-exhaustive','outer_z':int(oz),'outer_actions':[list(a) for a in h],'inner_z':int(iz)}
            if self.enumerate_histories(iz,r,e,ext,True,ctx):return {'status':'UNRESOLVED','reason':'combined-survivor'}
        return {'status':'CLOSED','reason':'combined-exhaustion'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('proof');a=ap.parse_args();p=Path(a.proof)
    raw=p.read_bytes();proof=json.loads(raw)
    ratio=proof.get('ratio')
    if ratio not in CASES:raise SystemExit('FAIL bad ratio')
    C,X=CASES[ratio]
    if proof.get('C')!=[C.numerator,C.denominator]:raise SystemExit('FAIL C mismatch')
    if proof.get('X')!=[[x.numerator,x.denominator] for x in X]:raise SystemExit('FAIL X mismatch')
    ci=proof.get('class_index')
    if not isinstance(ci,int):raise SystemExit('FAIL class index')
    seqs=list(first_hit_reps(X,C))
    if not (0<=ci<len(seqs)):raise SystemExit('FAIL class out of range')
    if proof.get('first_hit_order')!=[e.name for e in seqs[ci]]:raise SystemExit('FAIL first-hit order mismatch')
    if proof.get('result',{}).get('status')!='CLOSED':raise SystemExit(f"FAIL proof is not CLOSED: {proof.get('result')}")
    if proof.get('uncertified_numerical_infeasibilities')!=0:raise SystemExit('FAIL producer reports uncertified numerical infeasibilities')
    lp=ExactLP(seqs[ci],X,C,ratio.lower(),DEPTH);pool=Pool(proof);sv=SearchVerifier(lp,pool);res=sv.solve_class()
    if res!=proof.get('result'):raise SystemExit(f'FAIL independently reconstructed result {res} != stored {proof.get("result")}')
    if res.get('status')!='CLOSED':raise SystemExit(f'FAIL class not closed: {res}')
    pool.finish()
    print(json.dumps({'status':'PASS','ratio':ratio,'class_index':ci,'result':res,'certificates_verified':len(proof.get('certificates',[])),'terminal_histories_encountered':sv.terminals,'proof_sha256':sha256(raw).hexdigest()},indent=2,sort_keys=True))
    print('INDEPENDENT_CLASS_VERIFIER=PASS')
if __name__=='__main__':main()
