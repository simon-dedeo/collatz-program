import json, urllib.request

key = open("/Users/simon/Desktop/DANIEL/API_KEY").read().strip()

prompt = r"""
I am proving an anti-concentration ("mixed-radix flattening") theorem, independent of Collatz.
OBJECT: length-k binary word, weight m, odd positions 0<=i_1<...<i_m<k. Cycle numerator
   B = sum_{r=1}^m 3^{m-r} 2^{i_r}   (mod prime p, p!|6).
Equivalently B = sum_{j on} 2^j 3^{N_j}, N_j = #{on positions > j}.
Online recursion B_{j+1}=B_j (bit 0) or 3B_j+2^j (bit 1), B_0=0.
GOAL: fix eta,delta>0; for p with |<2,3>|>=p^delta, k>=C log p, eta*k<=m<=(1-eta)k, positions uniform:
  max_a Pr(B=a mod p) <= p^{-c}+e^{-ck}.  Weaker L^2 form acceptable first.

NUMERICS (exact DP, done): flattening holds robustly for ALL primes up to 1e6; even the smallest
available |<2,3>| ~ p^{0.54} flattens to machine-uniform by k~4 log p. Truly tiny subgroups don't occur.

I have a clean Fourier framing I want you to pressure-test and improve. Under Bernoulli(1/2) bits,
with mu_j = law of B_j, the Fourier coefficients satisfy the EXACT recursion
  hat mu_{j+1}(xi) = (1/2)[ hat mu_j(xi) + e_p(xi 2^j) hat mu_j(3 xi) ].
So mult-by-3 couples xi to 3xi; along a <3>-orbit O of size t3=ord_p(3), the vector
v_j=(hat mu_j(3^i xi))_i evolves by v_{j+1}=M_j v_j, M_j=(1/2)(I+U_j), U_j = D_j P,
P cyclic shift, D_j=diag(e_p(3^i xi 2^j)). Each ||M_j||<=1, M_j=(1/2)(I+unitary).
L^2 flattening = contraction of prod M_j away from 1.

QUESTIONS (be rigorous, cite exact theorems, flag errors, do NOT rubber-stamp):
1. Is the matrix-contraction route enough for the L^2 form e^{-ck}+p^{-1-c} WITHOUT sum-product?
   Quantify contraction of prod_{j}(1/2)(I+U_j): the deficiency 1-||prod M_j|| in terms of how the
   phases e_p(3^i xi 2^j) vary as j ranges over a block (2^j runs through <2>). Give the cleanest
   lower bound on the spectral gap per block of length ~log p.
2. The affine group Aff(F_p) is solvable so naive expansion fails. What is the CORRECT theorem to
   invoke for "no simultaneous approximate stability under x->3x and x->x+2^j"? Bourgain's
   affine sum-product? Bourgain-Glibichuk-Konyagin exponential sum bound over multiplicative
   subgroups? Give the precise statement I should cite and its hypotheses (order of <2>,<3>).
3. Fixed-Hamming-weight transfer: I relaxed to Bernoulli(1/2). To return to exact weight m in
   [eta k,(1-eta)k], is it cleanest via (a) local CLT on the count with a tilt/exponential change
   of measure, (b) contour/coefficient extraction Pr(B=a,|w|=m)=[z^m] E[z^{|w|}e_p(...)], or
   (c) conditioning + Fourier in an extra variable? Give the sharpest route and the error it costs.
4. Is there a known published anti-concentration/flattening result for sum_r g^{a_r} h^{b_r}-type
   "mixed multiplicative" sums I should cite or that subsumes this?
Keep it tight and technical. Numbered answers.
"""

body = {
    "model": "gpt-5.6-sol",
    "input": prompt,
    "reasoning": {"effort": "high"},
}
req = urllib.request.Request(
    "https://api.openai.com/v1/responses",
    data=json.dumps(body).encode(),
    headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"},
)
try:
    resp = json.load(urllib.request.urlopen(req, timeout=900))
except urllib.error.HTTPError as e:
    print("HTTP", e.code, e.read().decode()[:2000]); raise
# extract text
out = []
for item in resp.get("output", []):
    if item.get("type") == "message":
        for c in item.get("content", []):
            if c.get("type") == "output_text":
                out.append(c["text"])
text = "\n".join(out) if out else json.dumps(resp)[:4000]
open("gpt_consult_reply.md", "w").write(text)
print("=== reply saved, length", len(text), "===")
print(text)
