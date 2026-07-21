Let
\[
A=\lambda^{\alpha-1}>1,\qquad B=\lambda^{\alpha-2}<1,\qquad t=\lambda^{-2}.
\]
Then the pure equation is
\[
\Pi(q)=A\min_{3y=2q}\Pi(y).
\]

## Q1. Constraints on the \(-1\) fiber

### 1. Exact characterization of all pure-branch solutions

For \(q\neq0\), let \(\nu(q)\) be its exact denominator exponent and write
\[
\Pi(q)=A^{-\nu(q)}H(q).
\]
Every nonzero \(q\) has three children of depth \(\nu(q)+1\), so
\[
H(q)=\min_{3y=2q}H(y). \tag{1}
\]
Thus, along every edge,
\[
H(y)\ge H(q),
\]
and at least one child of each vertex has equality.

At the root, the children are \(0,1/3,2/3\). Since \(H(0)=\Pi(0)=1\),
\[
1=A\min\left(1,A^{-1}H(1/3),A^{-1}H(2/3)\right),
\]
hence
\[
\boxed{\min\{H(1/3),H(2/3)\}=1}
\]
or equivalently
\[
\boxed{\min\{\Pi(1/3),\Pi(2/3)\}=A^{-1}
=\lambda^{1-\alpha}.} \tag{2}
\]

This is the only root-fiber constraint imposed by the pure system.

Indeed, choose any \(C\ge1\), set
\[
H(1/3)=1,\qquad H(2/3)=C,
\]
and extend \(H\) by making it constant on each of the two descendant subtrees. Then (1) holds everywhere. Therefore every profile
\[
\boxed{(1,a,b),\qquad a=A^{-1},\quad b\ge A^{-1}}
\]
up to interchange of the last two entries, occurs in a positive solution of (P).

The corresponding co-spine constant is
\[
C=Ab,
\]
and the only pure-system restriction is
\[
\boxed{C\ge1.}
\]

So there is no pure-branch mechanism forcing
\[
b=2-a,\qquad C=2A-1.
\]

### 2. No local mean pinning

The condition
\[
b=2-a
\]
is exactly
\[
\frac{1+a+b}{3}=1,
\]
i.e. the assertion that \(c(-1)\) equals the arithmetic mean of its three lifts. But the pure operator uses a minimum, not a mean. Its equation fixes the smallest lift and is completely insensitive to the sum of the other two.

Consequently, mean pinning would require an additional global identity, invariant measure, symmetry, or selection principle. It is not encoded in (P).

### 3. What global mass balance actually says

Let
\[
S_k=\sum_{m\equiv2\pmod3}c(m),
\qquad
M_{k-1}=\sum_{r\equiv2\pmod3}\mu(r).
\]
Multiplication by \(4\) permutes the level-\(k\) states. Moreover, each of the two branch maps, restricted respectively to \(m\equiv2\pmod9\) and \(m\equiv8\pmod9\), maps bijectively onto the level-\((k-1)\) states. Summing the fixed-point equations therefore gives
\[
\boxed{(1-t)S_k=(A+B)M_{k-1}.} \tag{3}
\]

Since each \(\mu(r)\) is the minimum of a three-element fiber,
\[
M_{k-1}\le \frac{S_k}{3}.
\]
Equation (3) gives only the global weighted relation
\[
\frac{M_{k-1}}{S_k}=\frac{1-t}{A+B}. \tag{4}
\]
It does not give a separate relation for the \(-1\) fiber, nor does it distinguish its two nonminimal lifts.

The annealed column sum is
\[
s(\lambda)=t+\frac{A+B}{3}.
\]
At \(\lambda=2\),
\[
t=\frac14,\quad A=\frac32,\quad B=\frac34,\quad s(2)=1.
\]
Then (3) would force \(M_{k-1}=S_k/3\), hence equality in the minimum-versus-mean inequality for every fiber carrying positive mass. That requires all three entries of every fiber to be equal. Thus the finite global equation at exactly \(\lambda=2\) is singular relative to the proposed local pure-branch profile; the annealed identity does not imply the local profile \((1,2/3,4/3)\). The limits \(k\to\infty\), localization near \(-1\), and \(\lambda\to2\) need not commute.

### 4. Backward-orbit feedback

The \(2\)-branch near \(-1/4\) does feed values near \(-1\) back into the global system with coefficient \(B\). Therefore it can select a particular \(C\) in the full problem. But that feedback lies outside the closed pure subsystem (P). It is a global boundary condition, not a hidden consequence of local min-harmonicity.

The same point can be seen directly from the perturbed chain recursion. Suppose \(x_n\) is at local depth \(n\), and \(x_{n+1}\) is a minimizing child. The advanced equation gives
\[
c(x_{n+1})
=A^{-1}\bigl(c(x_n)-t\,c(4x_n)\bigr).
\]
With
\[
H_n=A^n\frac{c(x_n)}{c(-1)},
\]
this becomes
\[
\boxed{H_{n+1}=H_n-tA^n\frac{c(4x_n)}{c(-1)}.} \tag{5}
\]
Equivalently,
\[
H_n
=
H_N+t\sum_{r=n}^{N-1}A^r\frac{c(4x_r)}{c(-1)}. \tag{6}
\]

Thus a chain constant is determined by:

1. its terminal value at the deep boundary of the window, and
2. the accumulated transport forcing along the chain.

This gives a concrete mechanism for parity or labeling wobble: if the terminal chain alternates under the offset-doubling permutation, then \(C_k\) can have persistent even/odd corrections even when the transport tail itself decays geometrically.

At the root, (5) gives precisely
\[
Aa_k=1-t\frac{c(-4)}{c(-1)},
\]
or
\[
\boxed{a_k=A^{-1}-\lambda^{-1-\alpha}\frac{c(-4)}{c(-1)},}
\]
your identity (I). There is no corresponding one-step identity for \(b_k\); its value is given by a deep-chain formula of the form (6).

If the normalized transport terms in (6) decay like \(\rho^r\), \(\rho<1\), their omitted tail is \(O(\rho^N)\). But the terminal value \(H_N\) need not converge, so this alone does not prove convergence of \(C_k\).

### 5. Vanishing-transport selection is not universal

A vanishing perturbation can select a particular min-harmonic solution, but the selected solution generally depends on:

- the perturbing operator,
- the boundary condition at depth \(k\),
- the relative rates at which different couplings vanish,
- and the critical/argmin-chain structure.

There is no general selection theorem saying that additive positive transport selects the arithmetic-mean normalization. In fact, one can modify the deep boundary while keeping the same local limiting operator (P) and obtain any prescribed \(C\ge1\).

Therefore the observed near-relation \(b_k\approx2-a_k\) may reflect a global approximate balance, but it is not a local theorem and is not robust under arbitrary vanishing perturbations.

At \(\lambda=2\), the candidate
\[
a=\frac23,\qquad b=\frac43,\qquad C=Ab=2
\]
is admissible, but so is every
\[
b\ge\frac23,\qquad C\ge1.
\]
Nothing in (P) distinguishes \(C=2\).

---

## Q2. Can the multiplier \(2.0\)–\(2.2\) be derived from (P)?

Not from (P) alone.

Equation (1) only requires that every vertex have at least one child with the same \(H\)-value and that the other children have no smaller value. It imposes no statistics on how often the other children are much larger.

Two extreme constructions show this.

### Flat construction

Set all three children of every nonroot node equal to the parent in \(H\)-coordinates. Then every nonroot fiber has zero oscillation. The number of high-oscillation fibers is eventually zero.

### Fully oscillatory construction

Fix \(K>1\). At every node of \(H\)-value \(h\), give one child value \(h\) and the other two value \(Kh\), and continue recursively. Then every fiber has oscillation
\[
\frac{\max-\min}{\operatorname{mean}}
=
\frac{Kh-h}{(h+2Kh)/3}
=
\frac{3(K-1)}{1+2K}.
\]
For sufficiently large \(K\), this exceeds \(0.2\). Hence all \(3^n\) depth-\(n\) fibers can be highly oscillatory, giving dimension \(1\).

Intermediate marked-subtree constructions produce growth rates between these extremes, including rates near \(2.1^n\). Thus:

\[
\boxed{\text{The local equation permits multiplier }3\text{ and gives no bound }<3.}
\]

The observed multiplier must therefore come from the statistics of globally selected chain constants or from an additional regularity principle.

A rigorous route to dimension \(<1\) would require an extra estimate such as one of the following.

1. **Branching bound.** If every high-oscillation node has at most \(B<3\) high-oscillation children, modulo an immigration term \(I_n\), then
   \[
   N_{n+1}\le BN_n+I_n.
   \]
   If \(I_n=O(r^n)\), then
   \[
   \limsup N_n^{1/n}\le \max(B,r),
   \qquad
   \dim\le \log_3\max(B,r)<1.
   \]

2. **Moment/energy contraction.** Find a nonnegative oscillation energy \(E_n\) satisfying
   \[
   E_{n+1}\le \theta E_n,\qquad \theta<3,
   \]
   together with a lower energy cost for each fiber whose oscillation exceeds \(0.2\). Markov's inequality then bounds the number of high fibers by \(O(\theta^n)\).

3. **Stationary probabilistic law for chain constants.** If global boundary data induces a stationary multitype branching process, the multiplier is the Perron root of its offspring matrix. In a one-type approximation it would be \(3p\), where \(p\) is the probability that a child fiber remains above the oscillation threshold. But \(p\) is not determined by (P); it is inherited from the global eigenvector/transport dynamics.

The value \(2.0\)–\(2.2\) is therefore a property of the selected ensemble, not of min-harmonicity itself.

---

## Q3. Standard terminology and selection theory

Several related frameworks apply.

### For the pure equation

After logarithms, for example \(u=\log_A\Pi\),
\[
u(q)=1+\min_{3y=2q}u(y).
\]
This is commonly described as:

- an additive **Bellman equation** or dynamic-programming equation;
- a **min-plus/tropical eigenproblem**;
- an additive eigenfunction problem for a deterministic **Shapley operator**;
- a min-plus harmonic or idempotent harmonic function on a rooted tree;
- in nonlinear Perron–Frobenius language, an eigenproblem for an order-preserving homogeneous map.

The \(H\)-equation
\[
H(q)=\min_{3y=2q}H(y)
\]
is particularly simple: \(H\) is monotone along descendant edges and has at least one constant descendant ray from every vertex. Its free data can be viewed as boundary-at-infinity or chain data.

### For perturbative selection

Related theories include:

- vanishing-discount selection for Bellman equations;
- vanishing-viscosity selection in Hamilton–Jacobi/weak KAM theory;
- tropical or max-plus spectral projection onto critical classes;
- zero-temperature limits and calibrated subactions in ergodic optimization;
- singular perturbations of nonlinear Perron–Frobenius eigenvectors.

However, your transport perturbation is not automatically a standard zero-temperature regularization. The coefficient \(t=\lambda^{-2}\) does not itself tend to zero; only its normalized local influence appears to decay with depth. The problem is also on an effectively infinite tree with boundary data moving outward as \(k\to\infty\). Standard finite-state selection theorems do not directly supply a unique limit.

A selection lemma capable of pinning \(C\) would need, at minimum:

1. compactness of normalized eigenvectors on local balls;
2. a precise effective perturbation parameter;
3. control of the boundary term in (6);
4. uniqueness of the selected critical class or a specified balancing rule among critical chains.

The self-loop root and infinitely many marginal descendant chains produce many critical directions, so uniqueness is exactly what is missing.

## Conclusions

- Your statement that
  \[
  \min\{\Pi(1/3),\Pi(2/3)\}=\lambda^{1-\alpha}
  \]
  is exact and is the only pure local root-fiber constraint.
- There is no hidden pure-branch identity forcing \(b=2-a\).
- Global mass balance constrains only an aggregate sum of fiber minima, not the \(-1\) fiber mean.
- Backward-orbit and transport feedback can select \(C\), but the selected value depends on global boundary data and accumulated forcing.
- The observed oscillation multiplier cannot be derived from (P) alone; (P) permits every-fiber oscillation and dimension \(1\).
- At \(\lambda=2\), \(C=2\) is admissible but not selected by the pure system. A proof of \(C=2\) would have to come from an additional global selection theorem, and the present equations do not provide one.