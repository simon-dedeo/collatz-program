## Conclusion

The exact finite-level equations can be written down, but the proposed local limit does **not** determine \(a\). After transport is discarded, the renormalization is just the permutation
\[
j\longmapsto 2j\pmod 3,
\]
which fixes \(0\) and swaps \(1,2\). Consequently every profile
\[
(1,a,2-a),\qquad 0<a<2,
\]
is a labelled period-two solution. The two-step map is the identity on this family, so there is no local contraction or unique stable value of \(a\). In particular, neither \(\lambda=1.87\) nor \(\lambda=2\) predicts \(a=0.6925\).

The empirical value \(0.6925\) must therefore be selected by the transport forcing and the global environment of the backward \(\langle4\rangle\)-orbit, not by the transport-free local fixed-point equations. For the same reason, the observed mass-decay ratios \(0.79\)–\(0.81\) cannot be obtained from the stated local linearization alone.

---

# 1. Exact finite-level closure

Fix \(k\), put
\[
N=3^k,\qquad H=3^{k-1},
\]
and write
\[
t=\lambda^{-2},\qquad
A=\lambda^{\alpha-2},\qquad
B=\lambda^{\alpha-1}.
\]
For a level-\((k-1)\) state \(z\), define
\[
\mathcal M_k(z):=\min_{\ell\in\{0,1,2\}}c(z+\ell H).
\]

We assume that the threshold extremal vector satisfies the equality
\[
c=F_\lambda(c).
\]
If only \(c\leq F_\lambda(c)\) is known, all equalities below become inequalities.

## Lemma 1.1 — Exact equation on the \(-1\) fiber

For \(j\in\mathbf Z/3\mathbf Z\), let
\[
X_j:=c(-1+jH),\qquad Y_j:=c(-4+jH).
\]
Then
\[
\boxed{
X_j=tY_j+B\,\mathcal M_k\!\left(-1+2j\,\frac H3\right).
}
\]

### Proof sketch

Every \(-1+jH\) is \(8\bmod 9\), and
\[
4(-1+jH)\equiv -4+jH\pmod{3H},
\]
because \(4jH\equiv jH\pmod{3H}\). Moreover,
\[
R_8(-1+jH)
 =\frac{2(-1+jH)-1}{3}
 =-1+2j\frac H3.
\]
Substitution into the KL equation gives the formula. ∎

The three branch bases are
\[
-1,\qquad -1+2H/3,\qquad -1+H/3,
\]
so they are respectively the child labels \(0,2,1\) above \(-1\bmod H/3\).

---

## Lemma 1.2 — Exact transport tower

For \(q\geq0\) and \(j\in\mathbf Z/3\mathbf Z\), define
\[
C_{q,j}:=c(-4^q+jH).
\]
Then transport preserves \(j\):
\[
4(-4^q+jH)\equiv -4^{q+1}+jH\pmod{3H}.
\]

The residue types cycle as
\[
-4^q\bmod9:
\qquad
8,\ 5,\ 2,\ 8,\ 5,\ 2,\ldots
\]
according as \(q\equiv0,1,2\pmod3\).

### Proof sketch

The first assertion follows from
\[
4jH-jH=3jH\equiv0\pmod{3H}.
\]
The residue cycle follows from \(4^3\equiv1\bmod9\). ∎

---

## Lemma 1.3 — Three equations around the \(8\to5\to2\to8\) cycle

If \(q\equiv0\pmod3\), define
\[
\rho_q:=\frac{-2\cdot4^q-1}{3}.
\]
If \(q\equiv2\pmod3\), define
\[
\sigma_q:=\frac{-4^{q+1}-2}{3}.
\]
These are integers. The exact equations are:

\[
\boxed{
C_{q,j}
=tC_{q+1,j}
+B\,\mathcal M_k\!\left(\rho_q+2j\frac H3\right),
\qquad q\equiv0\pmod3,
}
\]

\[
\boxed{
C_{q,j}=tC_{q+1,j},
\qquad q\equiv1\pmod3,
}
\]

\[
\boxed{
C_{q,j}
=tC_{q+1,j}
+A\,\mathcal M_k\!\left(\sigma_q+4j\frac H3\right),
\qquad q\equiv2\pmod3.
}
\]

### Proof sketch

For \(q\equiv0\), the state is \(8\bmod9\), and
\[
R_8(-4^q+jH)
=\frac{-2\cdot4^q-1}{3}+2j\frac H3.
\]
For \(q\equiv1\), the state is \(5\bmod9\), so there is no branch term. For \(q\equiv2\), use
\[
R_2(-4^q+jH)
=\frac{-4^{q+1}-2}{3}+4j\frac H3.
\]
∎

---

## Corollary 1.4 — One full transport cycle

For \(q\equiv0\pmod3\),
\[
\boxed{
C_{q,j}
=t^3C_{q+3,j}
+t^2A\,\mathcal M_k\!\left(\sigma_{q+2}+4j\frac H3\right)
+B\,\mathcal M_k\!\left(\rho_q+2j\frac H3\right).
}
\]

For \(q=0\), this gives the exact three-step equation based at the \(-1\) fiber:
\[
X_j
=t^3C_{3,j}
+t^2A\,\mathcal M_k\!\left(-86+4j\frac H3\right)
+B\,\mathcal M_k\!\left(-1+2j\frac H3\right),
\]
since \(\sigma_2=(-4^3-2)/3=-22\), not \(-86\); thus more explicitly,
\[
\boxed{
X_j
=t^3c(-64+jH)
+t^2A\,\mathcal M_k\!\left(-22+4j\frac H3\right)
+B\,\mathcal M_k\!\left(-1+2j\frac H3\right).
}
\]

---

## Lemma 1.5 — Minimal exact closed subsystem

Let \(\Omega_k\subseteq S_k\) be the least subset satisfying:

1. \(-1+jH\in\Omega_k\) for \(j=0,1,2\);
2. if \(x\in\Omega_k\), then \(4x\bmod3^k\in\Omega_k\);
3. if \(x\equiv8\bmod9\), then all three lifts of \(R_8(x)\) belong to \(\Omega_k\);
4. if \(x\equiv2\bmod9\), then all three lifts of \(R_2(x)\) belong to \(\Omega_k\).

Then the KL equations restricted to \(\Omega_k\) form the minimal coordinate-closed finite system containing the \(-1\) fiber.

### Remark

The orbit tower \(\{-4^q+jH\}\) alone is not closed: each \(2\)- or \(8\)-state introduces a new minimum and hence three additional values. Thus there is no exact three-variable or finite-width “\(-1,-4,-16\)” closure independent of the branch side-fibers. The closure is finite only because \(S_k\) is finite.

This is the correct exact self-referential system.

---

# 2. Label action and the transport-free local limit

There is also an important level issue: a level-\(k\) eigenvector and a level-\((k-1)\) eigenvector are distinct objects. Passing from the exact finite-level system to a profile recurrence between levels requires an additional convergence/renormalization hypothesis.

Assume, in the most favorable form, that the branch minima over the three child fibers asymptotically reproduce the preceding normalized profile. Let
\[
p^{(k)}=(p^{(k)}_0,p^{(k)}_1,p^{(k)}_2)
\]
denote the mean-normalized profile of the \(-1\) fiber.

## Lemma 2.1 — Branch label permutation

Under \(R_8\), the level-\(k\) lift label \(j\) references child label
\[
\pi(j)=2j\pmod3.
\]
Hence
\[
\pi(0)=0,\qquad \pi(1)=2,\qquad \pi(2)=1.
\]

In matrix form,
\[
P=
\begin{pmatrix}
1&0&0\\
0&0&1\\
0&1&0
\end{pmatrix},
\qquad
P^2=I.
\]

This is an exact arithmetic fact, independent of any limiting assumption. ∎

---

## Lemma 2.2 — Transport-free projective renormalization

If transport is negligible relative to the advanced branch and if the branch minima identify with the preceding local profile, then projectively
\[
p^{(k)}=Pp^{(k-1)}.
\]

The factor \(B=\lambda^{\alpha-1}\) disappears under normalization. Thus the transport-free normalized map contains no dependence on \(\lambda\).

### Consequence

The labelled one-step fixed points satisfy
\[
p_1=p_2.
\]
But every positive profile is a two-step fixed point:
\[
p^{(k+2)}=P^2p^{(k)}=p^{(k)}.
\]

---

## Proposition 2.3 — Complete family with the empirical normalization

Pin the spine coordinate at \(1\) and impose mean \(1\):
\[
p_0=1,\qquad p_0+p_1+p_2=3.
\]
Then every positive two-cycle has the form
\[
\boxed{
p=(1,a,2-a),\qquad 0<a<2,
}
\]
with the next level
\[
\boxed{
Pp=(1,2-a,a).
}
\]

Thus \(a\) is arbitrary in the transport-free local system.

If one chooses the smaller off-spine entry as \(a\), then \(0<a\leq1\). The empirical value
\[
a=0.6925
\]
is compatible with the family but is not selected by it.

---

## Lift-labeling interpretation

In canonical base-\(3\) lift labels, the swap is genuine:
\[
1\leftrightarrow2
\]
at every renormalization step. Therefore the labelled vector has period two unless \(a=1\).

However, the unordered profile
\[
\{1,a,2-a\}
\]
is stationary. Equivalently, if one relabels the two off-spine children by applying \(P\) at alternating levels, the apparent period two disappears.

Hence:

- as a labelled dynamical system: genuine period two;
- as an unlabeled fiber shape: a labeling artifact.

---

# 3. Why \(\lambda\) does not determine \(a\)

The coefficient ratio of transport to the advanced branch is
\[
\varepsilon(\lambda)
=\frac{t}{B}
=\lambda^{-2-(\alpha-1)}
=\boxed{\lambda^{-1-\alpha}}.
\]

Numerically,
\[
\varepsilon(1.87)\approx 0.198,
\]
while, using \(2^\alpha=3\),
\[
\varepsilon(2)=2^{-1-\alpha}
=\frac1{2\cdot 2^\alpha}
=\boxed{\frac16}.
\]

These are small but nonzero coefficients. More importantly, the actual forcing is
\[
\varepsilon(\lambda)\,
\frac{c(-4+jH)}
{\text{relevant branch minimum}},
\]
not merely \(\varepsilon(\lambda)\). Its asymptotic value depends on the entire transport/branch closure.

The empirical spike growth says that this forcing becomes negligible along the spine. Once it is discarded, however, the parameter that could select \(a\) has also been discarded.

Therefore:

\[
\boxed{
a(1.87)\text{ is undetermined},\qquad
a(2)\text{ is undetermined}.
}
\]

There is no closed formula \(a=a(\lambda,\alpha)\) from the stated local limit. In particular, the local equations do not derive \(a=0.6925\).

---

# 4. Existence and stability of the limiting family

## Lemma 4.1 — Existence

For every \(a\in(0,2)\),
\[
p(a)=(1,a,2-a)
\]
is positive, mean-normalized, and satisfies
\[
P^2p(a)=p(a).
\]
Moreover,
\[
Pp(a)=p(2-a).
\]

This is immediate by direct calculation. ∎

---

## Lemma 4.2 — Linearization

The transport-free renormalization is linear:
\[
D\mathcal R=P.
\]
Its eigenvectors and eigenvalues are
\[
(1,0,0),\quad \lambda=1,
\]
\[
(0,1,1),\quad \lambda=1,
\]
\[
(0,1,-1),\quad \lambda=-1.
\]

The parameter \(a\) varies in the antisymmetric direction
\[
\frac{d}{da}p(a)=(0,1,-1).
\]
Thus one renormalization step changes the sign of this perturbation, and two steps preserve it exactly.

---

## Lemma 4.3 — No local asymptotic stability

No member \(p(a)\) is asymptotically stable under the transport-free two-step map.

### Proof sketch

Since \(P^2=I\), the derivative of the two-step map is the identity. In particular, the antisymmetric multiplier is
\[
(-1)^2=1.
\]
Hence perturbations in \(a\) neither decay nor grow. ∎

---

## Lemma 4.4 — Hilbert-projective formulation

For positive \(x,y\in\mathbf R_{>0}^3\), let
\[
d_H(x,y)
=
\log\frac{\max_i x_i/y_i}{\min_i x_i/y_i}.
\]
Because \(P\) is a coordinate permutation,
\[
d_H(Px,Py)=d_H(x,y).
\]
Thus \(P\) is an isometry, not a strict contraction, in Hilbert’s projective metric.

Consequently, a Birkhoff/Hilbert contraction argument cannot prove uniqueness or attraction for the transport-free map. Any contraction must come from the omitted transport and transversal branch coupling.

---

# 5. Transversal decay and mass profiles

The same degeneracy prevents the requested decay law from following from the local linearization.

## Lemma 5.1 — No transversal decay exponent from the local map

The only nontrivial profile multiplier is \(-1\), of modulus \(1\). Therefore the local map predicts neither exponential decay nor a power-law decay of oscillation away from the spine.

In particular, it does not produce a per-level contraction factor near \(0.8\).

---

## Lemma 5.2 — Right-profile data do not determine \(\nu_k\)-mass

The oscillation profile is determined by the right eigenvector \(c_k\). The mass
\[
\nu_k(r)=\frac{\bar c_r}{\sum_s\bar c_s}
\]
depends on normalization over all fibers, hence on the global distribution of fiber means. A local three-coordinate profile near \(-1\) does not determine:

1. how many fibers at distance \(3^{-j}\) inherit a given oscillation;
2. their means \(\bar c_r\);
3. their contribution to the denominator \(\sum_s\bar c_s\).

Thus even a complete local formula for the right profile would not, by itself, determine the \(\nu_k\)-mass tail.

---

## Forced linearized form

Retaining the omitted environment schematically gives an antisymmetric recurrence
\[
d_{k+1}=-d_k+f_k,
\]
where \(d_k\) measures the difference of the two off-spine coordinates and \(f_k\) is the transport/transversal forcing. Hence
\[
d_{k+2}-d_k=-f_k+f_{k+1}.
\]

If \(f_k\to0\), this implies convergence to a boundary-dependent two-cycle, not convergence to a universal value. The limiting amplitude is determined by the accumulated forcing:
\[
d_{2n}
=
d_0+\sum_{r=0}^{n-1}\bigl(-f_{2r}+f_{2r+1}\bigr).
\]
This explicitly exhibits why \(a\) is global-data dependent.

To derive the observed mass ratio \(0.79\)–\(0.81\), one would need at least:

- a transfer operator on the full backward-\(\langle4\rangle\) neighborhood tree;
- its transversal spectral radius;
- the growth rate of the number of affected fibers;
- the corresponding fiber-mean weights entering \(\nu_k\).

None of these quantities is encoded in the permutation \(P\).

---

# Final assessment of Conjecture C2

The exact finite-level closure and the label swap are rigorous. However, the stronger proposed conclusions do not follow:

1. **Exact closure:** given by Lemmas 1.1–1.5; it necessarily includes branch-generated side towers.
2. **Limiting profile:** the transport-free map is \(P\), yielding the family
   \[
   (1,a,2-a)\leftrightarrow(1,2-a,a).
   \]
3. **Value of \(a\):** not determined by \(\lambda,\alpha\); \(a=0.6925\) is selected by global forcing, if it has a universal limit at all.
4. **Stability:** neutral, not asymptotically stable; the two-step derivative is the identity.
5. **Mass decay:** not derivable from this local linearization; the measured \(0.79\)–\(0.81\) ratios require a global transversal transfer operator.

A viable strengthened C2 would therefore need to retain the first nonvanishing transport forcing and specify a convergent renormalized environment around the complete backward \(\langle4\rangle\)-orbit of \(-1\).