## 0. Status

I do not know an unconditional proof of C1′ from the stated facts. The most credible route is a **restricted-pressure estimate**, implemented as a finite-state, computer-certifiable cone inequality. The proof below reduces C1′ to one explicit uniform pressure-gap lemma. That lemma is the genuine open step.

Write
\[
\omega_k(r):=
\frac{\max_{0\le i<3}c_k(r+i3^{k-1})
      -\min_{0\le i<3}c_k(r+i3^{k-1})}
     {\bar c_{k,r}},
\qquad
\nu_k(r):=\frac{\bar c_{k,r}}{\sum_s\bar c_{k,s}},
\]
where \(c_k\) is a threshold eigenvector, normalized arbitrarily.

The target is
\[
\forall t>0,\qquad \nu_k\{\omega_k>t\}\longrightarrow0.
\tag{C1'}
\]

---

# 1. Candidate mechanisms

## 1.1. Hilbert-metric contraction away from the exceptional spine

### Proposed mechanism

Fix a finite 3-adic neighborhood \(E_J\) of the backward \(\langle4\rangle\)-orbit of \(-1\). On the complement of \(E_J\), show that some fixed iterate of the policy-linearized KL operator maps the positive cone into a cone of uniformly bounded projective diameter. Birkhoff’s theorem would then give
\[
d_H(A^Lx,A^Ly)\le \tau\,d_H(x,y),
\qquad \tau<1,
\]
uniformly in \(k\), \(\lambda\) near \(2\), and in the minimizing policy.

Since normalized profiles are transported exactly through \(5\bmod9\), nontrivial oscillation must repeatedly encounter the branching residues \(2,8\bmod9\). Uniform contraction outside \(E_J\) would imply that a fiber with \(\omega_k(r)>t\) has an itinerary spending a positive fraction of scales in \(E_J\).

### Strengths

- Naturally controls **oscillation**, not merely mass.
- Compatible with the exact transport identity.
- Birkhoff contraction is highly formalizable once a positive block matrix is available.

### Main obstruction

The global operator is not uniformly positive, and the minimum makes it only piecewise linear. More importantly, projective contraction alone does not show that \(E_J\) has small \(\nu_k\)-mass. It gives a localization lemma, but a separate pressure or mass-leakage estimate is still needed.

### Assessment

Useful as the first half of a proof:
\[
\text{large oscillation}\Longrightarrow\text{many exceptional visits}.
\]
Probably insufficient by itself.

---

## 1.2. Restricted pressure of the \(-1\) subsystem

### Proposed mechanism

Code fibers by ternary addresses and mark transitions that remain in a small neighborhood of the exceptional backward orbit. Construct a weighted finite-state automaton dominating the eigenvector mass carried by itineraries with many exceptional visits.

The desired inequality is that the normalized restricted pressure is strictly negative:
\[
P_{\mathrm{exc}}(\lambda)-P_{\mathrm{global}}(\lambda)<0
\tag{1.1}
\]
uniformly for \(\lambda\in[\lambda_{K},2]\).

Equivalently, after blocking \(L\) ternary digits, one seeks a positive vector \(h\), a tilt \(z>1\), and \(\rho<1\) such that
\[
\sum_{e:q\to q'} w_e(\lambda)\,z^{b(e)}h(q')
   \le \rho\,h(q)
\tag{1.2}
\]
for every abstract state \(q\), every allowed minimizing policy, and every \(\lambda\in[\lambda_K,2]\). Here \(b(e)\) counts exceptional persistence and \(w_e\) is the normalized eigenvector-mass multiplier.

A Chernoff bound then gives exponential decay for paths with linearly many exceptional blocks.

### Numerical normalization

At \(\gamma\approx0.9033\),
\[
\lambda=2^\gamma,\qquad
\lambda^{\alpha-1}
=2^{\gamma(\alpha-1)}
\approx 1.442.
\]
Thus the point value along the advanced fixed-point spine can grow by about \(1.442\) per level.

This must **not** be compared directly to the threshold eigenvalue \(1\). Passing from one ternary level to the next creates three possible addresses. For mass among fibers, the bare one-spine multiplier is heuristically
\[
\frac{\lambda^{\alpha-1}}{3}\approx0.481,
\]
and at \(\lambda=2\) it is exactly
\[
\frac{2^{\alpha-1}}3=\frac{3/2}{3}=\frac12.
\]
Hence the isolated fixed spine is strongly subcritical in mass.

A crude correction for repeated transport excursions gives
\[
\frac{\lambda^{\alpha-1}}
     {3(1-\lambda^{-2})}
\approx
\frac{1.442}{3(1-0.286)}
\approx0.673.
\tag{1.3}
\]
This is only a heuristic: it omits returns through the \(R_2\) branch and correlations created by the minimizing policy. The observed decay ratio near \(0.81\) indicates that such return clouds significantly increase the effective restricted pressure, but there is still room for a strict gap.

Also, \(s(\lambda)\approx1\) is the column sum of the fixed-level annealed KL operator. It is not the ternary tower growth \(3\). Thus comparing \(1.442\) directly with \(s(\lambda)\) or with the eigenvalue \(1\) uses incompatible normalizations.

### Assessment

This is the most promising mechanism. It addresses the exact issue: pointwise amplification \(>1\) versus entropy dilution by transversal ternary branching.

---

## 1.3. Frostman estimate from exact transport

### Proposed mechanism

Try to prove a bound of the form
\[
\nu_k(B(x,3^{-j}))\le C\,3^{-\beta j}
\tag{1.4}
\]
uniformly for \(x\) on the backward \(\langle4\rangle\)-orbit of \(-1\), with \(\beta>0\). Since the high-oscillation set is expected to lie in a union of such balls with sub-full 3-adic covering growth, a Frostman covering argument would imply C1′.

The exact transport identity on \(5\bmod9\) is useful because it shows that transport steps preserve normalized profiles. Therefore oscillation must be generated or maintained by branch events.

### Difficulty

It is not true pointwise that every branch event costs a factor \(<1\): the \(R_8\) coefficient is \(\lambda^{\alpha-1}>1\). The cost appears only after accounting for:

1. one preferred continuation among three lifts;
2. loss through transport;
3. the frequency of coherent returns to the advanced branch.

Thus a valid Frostman estimate is essentially a pressure estimate in another language.

### Assessment

Potentially elegant after the pressure gap has been proved, but unlikely to establish the gap by itself.

---

## 1.4. Uniform integrability relative to Haar measure

Let \(H_k\) be uniform measure on the level-\((k-1)\) fibers and define
\[
f_k(r):=\frac{d\nu_k}{dH_k}(r)
       =3^{k-2}\nu_k(r).
\]

If one can prove either

\[
\sup_k \int f_k^p\,dH_k<\infty
\quad\text{for some }p>1,
\tag{1.5}
\]
or more generally uniform integrability of \(\{f_k\}\), then every Haar-thin family \(E_k\) satisfies \(\nu_k(E_k)\to0\). Indeed, (1.5) gives
\[
\nu_k(E_k)
\le
\|f_k\|_{L^p(H_k)}
H_k(E_k)^{1-1/p}.
\tag{1.6}
\]

The isolated-spine heuristic is favorable: since its density grows like roughly \(1.442^k\) while its Haar mass is \(3^{-k}\), its \(p\)-moment contribution decays provided
\[
1.442^p<3,
\]
which allows \(p\) up to about \(3\). Return clouds lower the admissible exponent but may still leave some \(p>1\).

### Difficulty

One must first prove that the high-oscillation set is uniformly Haar-thin and then establish an \(L^p\) pressure inequality. Both are nontrivial. Moreover, C1′ may hold even if every \(L^p\), \(p>1\), bound fails; uniform integrability is weaker than \(L^p\)-boundedness.

### Assessment

A good formulation of the pressure method, and possibly the cleanest final corollary, but a direct restricted-pressure estimate is more flexible.

---

# 2. Preferred proof mechanism: block restricted pressure

I recommend combining:

1. off-spine projective contraction to localize high oscillation;
2. a tilted finite-state pressure certificate to bound the mass of exceptional itineraries.

The following is a precise conditional proof scheme.

---

## Lemma 1. Policy linearization

For fixed \(k,\lambda\), and \(c>0\), choose for each branch row one lift at which the relevant minimum is attained. Let \(\sigma\) denote the resulting minimizing policy. Then there is a nonnegative matrix \(A_{k,\lambda,\sigma}\) such that
\[
F_\lambda(c)=A_{k,\lambda,\sigma}c.
\]

In particular, if \(c_k=F_{\lambda_k}(c_k)\), then for some policy \(\sigma_k\),
\[
A_{k,\lambda_k,\sigma_k}c_k=c_k.
\tag{2.1}
\]

### Checkability

This is immediate row by row. Each branch minimum has three possible choices, so every policy matrix is finite and explicit. No differentiability or uniqueness of the minimum is needed.

---

## Lemma 2. Symmetric fiber oscillation is labeling-independent

For a fiber profile \(x=(x_0,x_1,x_2)>0\), define
\[
\operatorname{osc}(x)
=
\frac{\max_i x_i-\min_i x_i}{(x_0+x_1+x_2)/3}.
\]
Then \(\operatorname{osc}\) is invariant under permutations of the lifts.

Moreover, exact transport through a \(5\bmod9\) state preserves \(\operatorname{osc}\).

### Consequence

The observed alternating swap of the two non-\((-1)\) lifts is irrelevant. The natural limiting object is the unordered profile
\[
\{a,1,2-a\}.
\]

---

## Lemma 3. Finite-block contraction away from the exceptional component

Fix \(t>0\). There exist:

- a finite 3-adic depth \(J=J(t)\);
- a block length \(L=L(t)\);
- a finite exceptional state set \(\mathcal E_J\), consisting of \(J\)-digit neighborhoods of the backward \(\langle4\rangle\)-orbit of \(-1\);
- constants \(0<\tau<1\) and \(C<\infty\);

such that the following holds uniformly for all sufficiently large \(k\), all
\[
\lambda\in[\lambda_{18},2],
\]
and every minimizing policy.

If a length-\(L\) block of the scale itinerary avoids \(\mathcal E_J\), then its induced map on normalized fiber profiles satisfies
\[
\operatorname{osc}(P_{\rm out}x)
\le
\tau\,\operatorname{osc}(x).
\tag{2.2}
\]

Branch blocks entering or leaving \(\mathcal E_J\) satisfy the rough bound
\[
\operatorname{osc}(P x)
\le C\max\{1,\operatorname{osc}(x)\}.
\tag{2.3}
\]

### Interpretation

Outside the exceptional component, normalized profiles forget their boundary data at a uniform exponential rate.

### How to certify it

For each residue class modulo \(3^{J+L}\) and each policy:

1. build the induced \(3\times3\) positive profile matrix for the block;
2. prove that all relevant cross-ratios are bounded;
3. use the Birkhoff coefficient
   \[
   \tau(A)\le
   \tanh\!\left(\frac{\operatorname{diam}_H(A)}4\right)<1;
   \]
4. maximize the resulting bound over the finite set of blocks and over \(\lambda\in[\lambda_{18},2]\) using interval arithmetic.

Zeros may require increasing \(L\) or using a product cone that tracks several neighboring fibers.

---

## Lemma 4. Oscillation-localization lemma

Assume Lemma 3. For every \(t>0\), there are constants
\[
\theta_t>0,\qquad C_t<\infty
\]
such that if \(\omega_k(r)>t\), then the scale itinerary of \(r\) contains at least
\[
\theta_t\left\lfloor\frac{k-J}{L}\right\rfloor-C_t
\tag{2.4}
\]
exceptional \(L\)-blocks.

Equivalently, if \(N_{\mathcal E}(r)\) counts exceptional blocks, then
\[
\{\omega_k>t\}
\subseteq
\left\{
r:
N_{\mathcal E}(r)
\ge \theta_t k-C_t
\right\}.
\tag{2.5}
\]

### Proof sketch

Partition the itinerary into \(L\)-blocks. Every nonexceptional block contracts oscillation by \(\tau\). Exceptional blocks can increase it by at most the finite factor \(C\). Therefore
\[
\omega_k(r)
\le
C_0\,\tau^{N_{\rm out}(r)}
C^{N_{\mathcal E}(r)}.
\tag{2.6}
\]
Since \(N_{\rm out}+N_{\mathcal E}\asymp k/L\), the condition \(\omega_k(r)>t\) forces a positive lower density of exceptional blocks, after adjusting constants for initial and terminal blocks.

A more robust formalization replaces (2.6) by a finite-state recurrence for an upper oscillation envelope.

---

## Lemma 5. Uniform restricted-pressure gap — the hard lemma

For the exceptional automaton from Lemma 3, there exist constants
\[
z>1,\qquad \rho<1,\qquad C<\infty
\]
such that, uniformly in \(k\),
\[
\sum_r \nu_k(r)\,z^{N_{\mathcal E}(r)}
\le C\,\rho^{\,k/L}z^{\vartheta k}
\tag{2.7}
\]
for some \(\vartheta<\theta_t\).

Equivalently, in the more directly usable form, there exist \(q_t<1\) and \(C_t<\infty\) such that
\[
\nu_k\left\{
r:N_{\mathcal E}(r)\ge \theta_t k-C_t
\right\}
\le C_tq_t^k.
\tag{2.8}
\]

### Finite certificate form

Construct a finite abstract state set \(Q\) recording:

1. the residue modulo \(3^J\);
2. whether the orbit is in the exceptional component;
3. a rational cone containing the normalized local profile;
4. sufficient policy information to dominate all three choices of every minimum.

For each \(L\)-digit transition \(e:q\to q'\), compute an upper normalized mass multiplier \(w_e(\lambda)\) and an exceptional count \(b(e)\). It suffices to find a positive rational vector \(h:Q\to\mathbb Q_{>0}\), \(z>1\), and \(R\) such that
\[
\sum_{e:q\to q'}
w_e(\lambda)z^{b(e)}h(q')
\le R\,h(q)
\tag{2.9}
\]
for every \(q\), every policy, and every
\[
\lambda\in[\lambda_{18},2],
\]
with
\[
Rz^{-\theta_t}<1.
\tag{2.10}
\]

Then Markov’s inequality gives
\[
\nu_k\{N_{\mathcal E}\ge\theta_t n\}
\le
C(Rz^{-\theta_t})^n.
\tag{2.11}
\]

### Essential normalization issue

The multipliers \(w_e\) must govern **fiber mass relative to total fiber mass**, not point values. A spine edge should therefore contain the ternary dilution factor. The bare advanced continuation has normalized multiplier approximately
\[
\lambda^{\alpha-1}/3,
\]
not \(\lambda^{\alpha-1}\).

### This is the hardest lemma

Everything else is a localization or abstract large-deviation argument. Lemma 5 asserts exactly that the exceptional subsystem has pressure strictly below the global mass pressure.

---

## Lemma 6. C1′ from localization and pressure

Assume Lemmas 4 and 5. Then for every \(t>0\),
\[
\nu_k\{\omega_k>t\}\longrightarrow0.
\]

### Proof

By Lemma 4,
\[
\{\omega_k>t\}
\subseteq
\{N_{\mathcal E}\ge\theta_tk-C_t\}.
\]
Lemma 5 gives
\[
\nu_k\{\omega_k>t\}
\le C_tq_t^k\longrightarrow0.
\]
This proves C1′.

---

## Lemma 7. Consequences for \(\delta_k\) and \(\lambda_k\)

For each fiber,
\[
u_r=\frac{\bar c_r-\min c}{\bar c_r}
\le \omega_k(r),
\qquad 0\le u_r\le1.
\]
If C1′ holds, then for any \(t>0\),
\[
\sum_r\nu_k(r)u_r
\le
t+\nu_k\{\omega_k>t\}.
\]
Taking \(k\to\infty\), then \(t\downarrow0\), gives
\[
\sum_r\nu_k(r)u_r\longrightarrow0,
\qquad
\delta_k\longrightarrow0.
\]
The oscillation law therefore implies
\[
\lambda_k\longrightarrow2.
\]
KL’s theorem then yields the predecessor-counting exponent \(1-\varepsilon\).

---

# 3. What exact finite computation is needed?

A realistic certificate search would use the following data.

## 3.1. Choose a core depth

Take \(J\) large enough to include verbatim the observed periodic addresses
\[
-1=(2)^\infty,\qquad
-1/4=(20)^\infty,\qquad
-1/16=(2100)^\infty,
\]
and all short return paths between their residue classes.

A first search might use \(J\in[10,16]\).

## 3.2. Block transitions

Choose \(L\), perhaps \(4\le L\le12\), and enumerate all transitions modulo \(3^{J+L}\) induced by:

- transport \(m\mapsto4m\);
- \(R_2(m)=(4m-2)/3\);
- \(R_8(m)=(2m-1)/3\);
- each possible minimizing lift.

The exact transport identity should be imposed symbolically rather than estimated.

## 3.3. Cone discretization

Track profiles modulo scaling in a permutation-invariant cone, for example by the ordered coordinates
\[
0<x_{\min}\le x_{\mathrm{mid}}\le x_{\max},
\qquad
x_{\min}+x_{\mathrm{mid}}+x_{\max}=3.
\]
Use rational polyhedral cells for the ratios
\[
x_{\min}/x_{\mathrm{mid}},
\qquad
x_{\max}/x_{\mathrm{mid}}.
\]

The observed exceptional profile
\[
\{0.6925,1,1.3075\}
\]
provides a useful location for refined cells, but the proof must cover the full invariant cone.

## 3.4. Pressure certificate

Search by linear programming for:

- a positive state potential \(h\);
- a tilt \(z>1\);
- an upper pressure \(R\);

satisfying (2.9). All powers of \(\lambda\) can be bounded by outward-rounded interval arithmetic on \([\lambda_{18},2]\). Since
\[
\lambda^{-2},\quad
\lambda^{\alpha-2},\quad
\lambda^{\alpha-1}
\]
are monotone on this interval, many bounds reduce to checking endpoints.

The final output can consist entirely of:

1. a finite list of rational inequalities;
2. certified intervals for the three weights;
3. a rational \(h\), \(z\), and \(R\);
4. the strict rational inequality \(Rz^{-\theta_t}<1\).

That is suitable for later Lean verification.

---

# 4. What could make C1′ false?

The main danger is not the single fixed point \(-1\). Its entropy-normalized multiplier is only about \(0.48\). The danger is an increasingly complicated **return cloud** around the backward \(\langle4\rangle\)-orbit.

## 4.1. Structural failure mode: critical exceptional renewal system

C1′ could fail if there are arbitrarily long exceptional return loops whose combined weighted multiplicity exactly compensates for ternary dilution. In pressure language,
\[
P_{\mathrm{exc}}=P_{\mathrm{global}},
\tag{4.1}
\]
even though every fixed finite truncation appears subcritical.

This could occur through:

- many \(R_2\)- and transport-mediated returns to the \(R_8\) spine;
- a sequence of larger and larger 3-adic neighborhoods with pressure gaps tending to zero;
- policy correlations that preferentially choose minima feeding the exceptional component;
- a null-recurrent or critical renewal structure, with no finite invariant exceptional state but with positive limiting mass in growing neighborhoods.

Then the high-oscillation mass might decay only up to a large crossover scale and subsequently stall.

## 4.2. Expected signature if the system is critical but C1′ still true

One may have
\[
\nu_k\{\omega_k>t\}\sim k^{-\beta}
\]
rather than exponential decay. Consecutive ratios would then satisfy
\[
\frac{M_{k+1}}{M_k}=1-\frac{\beta}{k}+o(k^{-1}),
\]
and hence drift toward \(1\). This is compatible with the observed drift \(0.789,0.805,0.808\), so the current data do not establish a uniform exponential gap.

In this scenario Lemma 5 is too strong, although C1′ could remain true through a weaker renewal theorem.

## 4.3. Expected signature if C1′ is false

For some \(t>0\), one would see
\[
\nu_k\{\omega_k>t\}\to M_t>0
\]
along a subsequence or in the full limit. Consequences should include:

1. \(\nu_k\)-mass in optimally chosen growing neighborhoods of the exceptional orbit stabilizes at a positive value;
2. the weighted defect
   \[
   \sum_r\nu_k(r)u_r
   \]
   stops decaying;
3. \(\delta_k\) approaches a positive limit or has positive limsup;
4. \(\lambda_k\) appears to converge to a value strictly below \(2\);
5. finite-state restricted-pressure upper bounds approach \(1\) as \(J,L\to\infty\).

## 4.4. Best finite-\(k\) discriminants

The following computations would distinguish a genuine gap from a stall better than raw consecutive mass ratios.

### A. Restricted spectral radii versus truncation depth

For increasing \(J,L\), compute the best certified normalized pressure bound
\[
q_{J,L}.
\]
Evidence for C1′:
\[
\sup_{J\ge J_0}\inf_Lq_{J,L}<1.
\]
Evidence for criticality:
\[
q_{J,L}\uparrow1
\]
as the exceptional neighborhood is enlarged.

### B. Renewal-loop generating function

Enumerate first-return loops to the \(-1\) component and compute their normalized total weights \(a_n\). Test whether
\[
\sum_{n\ge1}a_n<1,
\quad =1,
\quad\text{or}>1.
\]
These correspond respectively to subcritical, critical, and supercritical exceptional pressure.

### C. \(L^p\) moments

Compute
\[
M_p(k)=\int f_k^p\,dH_k.
\]
If \(M_p(k)\) remains bounded for some fixed \(p>1\), then concentration on Haar-thin exceptional sets is impossible. If all tested \(p>1\) show growing moments with effective critical exponent tending to \(1\), a null-recurrent concentration mechanism becomes plausible.

### D. Mass in nested exceptional neighborhoods

For a fixed geometric definition \(E_J\), compute
\[
\limsup_{k\to\infty}\nu_k(E_J)
\]
and then study \(J\to\infty\). The desired order of limits is
\[
\lim_{J\to\infty}\limsup_{k\to\infty}\nu_k(E_J)=0.
\]
Failure would be visible as a persistent plateau.

---

# 5. Recommended immediate objective

The most useful next theorem to target is not C1′ in full generality, but the following finite-certificate statement:

> **Restricted block-pressure theorem.** There exist explicit \(J,L\), a finite cone partition, \(z>1\), a positive rational potential \(h\), and \(\rho<1\), valid uniformly for \(\lambda\in[\lambda_{18},2]\) and every minimizing policy, such that the tilted block inequality (2.9) holds.

If such a certificate exists, the remaining argument—policy linearization, oscillation localization, Chernoff bound, C1′, \(\delta_k\to0\), and \(\lambda_k\to2\)—is comparatively standard and formalizable.

If repeated searches show that the optimal certified pressure converges to \(1\), the next model should be a countable-state renewal operator around the backward orbit of \(-1\), with the decisive question becoming whether its first-return series is strictly subcritical or exactly critical.