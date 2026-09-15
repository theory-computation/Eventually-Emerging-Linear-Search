#!/usr/bin/env python3
"""Exact-certifying search prototype mirroring v10_engine_push branch coverage.

Safety rule: numerical infeasibility never prunes by itself.  A branch closes only
when farkas_core returns a Fraction-exact certificate.  If support recovery fails,
the branch is expanded conservatively; any surviving terminal makes the class
unresolved rather than proving a false theorem.

This stage-2 version is intended for bounded class-range smoke/measurement before
full production and proof-format freezing.
"""
import argparse,json,time
from fractions import Fraction as Q
from pathlib import Path
from exact_model import ExactLP,first_hit_reps
from farkas_core import compressed_inequalities,primal_float_status,exact_farkas,certificate_record

CASES={
'EA':(Q(87,20),[Q(1),Q(7719,1000),Q(15969,1000),Q(3829,200),Q(6147,250),Q(32707,1000),Q(24283,500),Q(27197,500),Q(136059,1000)]),
'FI':(Q(219,50),[Q(1),Q(1241,200),Q(10693,1000),Q(541,40),Q(3103,200),Q(4091,200),Q(28219,1000),Q(6871,125),Q(7928,125)])}

def action_json(a):return list(a)

class LimitReached(Exception):pass
class Search:
 def __init__(self,lp,class_index,max_tests=None):
  self.lp=lp;self.ci=class_index;self.max_tests=max_tests;self.tests=0;self.certs=[];self.counts={};self.uncertified=0
 def test(self,kind,rows,eqs,context,path):
  if self.max_tests is not None and self.tests>=self.max_tests:raise LimitReached
  self.tests+=1;self.counts[kind+'_tests']=self.counts.get(kind+'_tests',0)+1
  I=compressed_inequalities(self.lp,rows,eqs);st=primal_float_status(I,len(self.lp.names))
  if st!=2:return False
  y=exact_farkas(I,len(self.lp.names))
  if y is None:
   self.uncertified+=1;self.counts[kind+'_infeasible_uncertified']=self.counts.get(kind+'_infeasible_uncertified',0)+1;return False
  rec=certificate_record(I,len(self.lp.names),y);rec.update({'kind':kind,'context':context,'path':[action_json(a) for a in path]})
  self.certs.append(rec);self.counts[kind+'_certified']=self.counts.get(kind+'_certified',0)+1;return True
 def enumerate_histories(self,z,rows0=(),eqs0=(),external=(),find_one=False,context=None):
  out=[];lp=self.lp;depth=lp.depth;context=context or {'phase':'one-side','z':int(z)}
  def dfs(comp,record,assigned,actions,rows,eqs):
   if comp>depth:
    out.append(tuple(actions));return bool(find_one)
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
       eq2=ep+lp.exact_visitor_eq(Qe,z,vq)
       act=('U',comp,sp,sq,vp,vq)
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
  order=sorted((Q(-1),Q(1)),key=lambda z:sum(1 for _ in self.lp.slot_pairs(1,z)))
  witness={}
  for z in order:
   h=self.enumerate_histories(z,find_one=True,context={'phase':'one-side','z':int(z)})
   if not h:return {'status':'CLOSED','reason':'one-side','z':int(z)}
   witness[z]=h[0]
  for oz,iz in ((order[0],order[1]),(order[1],order[0])):
   r,e,ext=self.replay(oz,witness[oz]);ctx={'phase':'conditional-first','outer_z':int(oz),'outer_actions':[action_json(a) for a in witness[oz]],'inner_z':int(iz)}
   inn=self.enumerate_histories(iz,r,e,ext,True,ctx)
   if inn:return {'status':'UNRESOLVED','reason':'combined-survivor'}
  oz,iz=order;outer=self.enumerate_histories(oz,find_one=False,context={'phase':'outer-exhaustive','z':int(oz)})
  for h in outer:
   r,e,ext=self.replay(oz,h);ctx={'phase':'conditional-exhaustive','outer_z':int(oz),'outer_actions':[action_json(a) for a in h],'inner_z':int(iz)}
   if self.enumerate_histories(iz,r,e,ext,True,ctx):return {'status':'UNRESOLVED','reason':'combined-survivor'}
  return {'status':'CLOSED','reason':'combined-exhaustion'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--ratio',choices=['EA','FI'],required=True);ap.add_argument('--class-index',type=int,required=True);ap.add_argument('--max-tests',type=int,default=None);ap.add_argument('--out',default=None);a=ap.parse_args()
 C,X=CASES[a.ratio];seqs=list(first_hit_reps(X,C));lp=ExactLP(seqs[a.class_index],X,C,a.ratio.lower(),7);S=Search(lp,a.class_index,a.max_tests);t=time.time()
 try:result=S.solve_class()
 except LimitReached:result={'status':'LIMIT','reason':'max-tests'}
 proof={'ratio':a.ratio,'C':[C.numerator,C.denominator],'X':[[x.numerator,x.denominator] for x in X],'class_index':a.class_index,'first_hit_order':[e.name for e in seqs[a.class_index]],'result':result,'tests':S.tests,'counts':S.counts,'uncertified_numerical_infeasibilities':S.uncertified,'certificates':S.certs,'wall_seconds':time.time()-t}
 out=Path(a.out) if a.out else Path(__file__).resolve().parent.parent/f'results/producer_{a.ratio}_class{a.class_index}.json';out.write_text(json.dumps(proof,indent=2,sort_keys=True));print(json.dumps({k:proof[k] for k in ('ratio','class_index','result','tests','counts','uncertified_numerical_infeasibilities','wall_seconds')},indent=2));print('CERTIFICATES=',len(S.certs));print('RESULT =',out)
if __name__=='__main__':main()
