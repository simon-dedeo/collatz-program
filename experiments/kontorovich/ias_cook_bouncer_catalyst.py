#!/usr/bin/env python3
"""Exact Cook-style catalyst-reset audit for bouncer cylinder links.

An edge family has affine input/output tails.  Linking its output family to a
following input family restricts the first tail to one congruence class of
index

    following_input_stride / gcd(output_stride, following_input_stride).

Index one is the natural clean-catalyst condition: every incoming tail passes
through.  This worker checks a bounded atlas and the generic 2-adic valuation
identity showing that every positive bouncer link has index divisible by
2^(154*h_next+23*m_after_next), hence at least 2^177.
"""
from __future__ import annotations

import argparse, hashlib, json, math
from pathlib import Path
from typing import Any, Sequence

SCHEMA="collatz-ias-cook-bouncer-catalyst-v1"
A=3**114; B=2**154; C=3**17; D=2**23
F=(A-B)//5; M=3**33*(C-D)

def canonical_json(x:Any)->bytes:return json.dumps(x,sort_keys=True,separators=(",",":")).encode()
def source_sha256()->str:return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
def v2(x:int)->int:
    if not x: raise ValueError("v2(0)")
    return (x&-x).bit_length()-1

def strides(m:int,h:int,nxt:int)->tuple[int,int]:
    if min(m,h,nxt)<1: raise ValueError("positive opcodes required")
    Cm=C**m; odd_modulus=math.lcm(F*Cm,Cm*M)
    qstep=odd_modulus*(1<<(23*nxt+1))
    input_stride=D**m*B**h*(qstep//Cm)
    output_stride=A**h*qstep
    assert v2(qstep)==23*nxt+1
    assert v2(input_stride)==23*m+154*h+23*nxt+1
    assert v2(output_stride)==23*nxt+1
    return input_stride,output_stride

def audit(bound:int)->dict[str,Any]:
    if bound<1: raise ValueError("bound must be positive")
    edge={(m,h,n):strides(m,h,n) for m in range(1,bound+1) for h in range(1,bound+1) for n in range(1,bound+1)}
    checked=clean=0; minimum=None; minimizer=None; valuation_hist={}
    for m in range(1,bound+1):
      for h in range(1,bound+1):
       for n in range(1,bound+1):
        out_stride=edge[m,h,n][1]
        for h2 in range(1,bound+1):
         for n2 in range(1,bound+1):
          in_stride=edge[n,h2,n2][0]
          index=in_stride//math.gcd(out_stride,in_stride)
          exponent=v2(index); expected=154*h2+23*n2
          if exponent!=expected: raise AssertionError("generic link-index valuation failed")
          checked+=1; clean+=index==1; valuation_hist[exponent]=valuation_hist.get(exponent,0)+1
          candidate=(index,m,h,n,h2,n2)
          if minimum is None or candidate<minimum:
              minimum=candidate; minimizer=(m,h,n,h2,n2)
    assert minimum is not None and minimizer is not None and clean==0
    min_index=minimum[0]
    return {
      "opcode_bound":bound,
      "edge_families":len(edge),
      "consecutive_links_checked":checked,
      "clean_tail_links":clean,
      "minimum_link_index":str(min_index),
      "minimum_link_index_bits":min_index.bit_length(),
      "minimum_link_index_v2":v2(min_index),
      "minimum_parameters":{"m":minimizer[0],"h":minimizer[1],"next_m":minimizer[2],"following_h":minimizer[3],"following_next_m":minimizer[4]},
      "v2_histogram":{str(k):v for k,v in sorted(valuation_hist.items())},
      "generic_identity":{
        "output_stride_v2":"23*shared_m+1",
        "following_input_stride_v2":"23*shared_m+154*following_h+23*following_next_m+1",
        "link_index_v2":"154*following_h+23*following_next_m",
        "uniform_lower_bound":"positive opcodes imply link_index divisible by 2^177",
        "N_block_precision_cost":"at least 177*(N-1) dyadic tail bits",
      },
      "interpretation":"the natural affine tail is refined at every bouncer link and is not a Cook-clean reusable catalyst",
      "scope":"generic stride-valuation identity plus exhaustive exact integer indices in the displayed opcode box; excludes this natural tail interface, not every possible nonlinear catalyst coordinate",
      "counterexample":None,
    }

def build(bound:int)->dict[str,Any]:
    data={"schema":SCHEMA,"worker_sha256":source_sha256(),"audit":audit(bound)}
    data["artifact_sha256"]=hashlib.sha256(canonical_json(data)).hexdigest();return data
def verify(path:Path)->dict[str,Any]:
    expected=json.loads(path.read_text());assert expected["schema"]==SCHEMA and expected["worker_sha256"]==source_sha256()
    payload=dict(expected); advertised=payload.pop("artifact_sha256");assert advertised==hashlib.sha256(canonical_json(payload)).hexdigest()
    assert expected==build(int(expected["audit"]["opcode_bound"]));assert expected["audit"]["counterexample"] is None
    return {"artifact_sha256":advertised,"links":expected["audit"]["consecutive_links_checked"],"clean":expected["audit"]["clean_tail_links"],"minimum_v2":expected["audit"]["minimum_link_index_v2"],"counterexample":None}
def main(argv:Sequence[str]|None=None)->None:
    p=argparse.ArgumentParser(description=__doc__);s=p.add_subparsers(dest="cmd",required=True);b=s.add_parser("build");b.add_argument("output",type=Path);b.add_argument("--bound",type=int,default=12);v=s.add_parser("verify");v.add_argument("artifact",type=Path);s.add_parser("selftest");a=p.parse_args(argv)
    if a.cmd=="selftest":
        tiny=audit(2);assert tiny["consecutive_links_checked"]==32 and tiny["minimum_link_index_v2"]==177;print("Cook catalyst selftest: PASS")
    elif a.cmd=="build":
        data=build(a.bound);a.output.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n");print(json.dumps(verify(a.output),indent=2,sort_keys=True))
    else: print(json.dumps(verify(a.artifact),indent=2,sort_keys=True))
if __name__=="__main__":main()
