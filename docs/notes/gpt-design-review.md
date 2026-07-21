### 1. Spine-face domination is not currently established

Factoring by the pinned \(-1\) lift removes the artificial period-2 relabeling, but it does **not** by itself force a minimizing policy to pay exceptional charge.

The missing assertion is pathwise:

> Every block that preserves a nonzero spine-face oscillation must traverse a depth-memory edge marked as charged.

Lemma 5 only prices the charges that a path actually incurs. Its stationary/Haar density \(\pi(E_J)\) does not imply that an adversarial minimizing path incurs them. Since the aligned \(\{0,3\}\) class is reachable from every state, an admissible zero-charge cycle in the oscillation-carrying spine-face automaton would let the adversary preserve oscillation indefinitely while evading the tilt.

Thus the spine-face fix succeeds only if the augmented finite automaton verifies one of the equivalent properties:

* no zero-charge cycle carries nonzero spine-face oscillation; or
* every length-\(n\) oscillation-persistent path has
  \[
  E(\gamma)\ge \theta n-O(1)
  \]
  with \(\theta>\log R/\log z\).

Without such an edgewise/pathwise certificate, the adversary wins. Haar-measure charging is insufficient.

---

### 2. The 8-branch is marginal on the spine face

The raw coefficient \(\lambda^{\alpha-1}>1\) does not determine the normalized projective action. After mean normalization and quotienting by the \(\langle\times2\rangle\) relabeling, the reported transversal spectrum \(\{0,1\}\) means:

* one transversal direction is killed;
* one direction is preserved with multiplier \(1\).

Hence the normalized 8-branch is **marginal/isometric along the surviving spine-face direction**, not strictly contractive. Depending on the chosen norm, a single nonnormal representative may have bounded transient amplification, but there is no uniform \(\tau<1\).

Therefore claim (i), as stated uniformly “off the exceptional set,” is false near the spine face unless the block is guaranteed to use an additional genuinely mixing 2/5-branch. The factor \(q_2<1\) helps only when that branch is forced; the minimizing policy may otherwise remain in the eigenvalue-1 direction.

So yes: autonomous Birkhoff decay fails on the near-spine face. Decay there must come from pathwise charge, not from strict contraction.

---

### 3. Correct non-circular localization statement

The argument can still close, but not from contraction alone. It needs a stratified contraction-or-charge lemma:

1. Away from the spine-face cone, every \(L_w\)-block contracts a suitable oscillation carrier by \(\tau<1\).
2. On the spine face, neutral blocks are allowed, but every neutral oscillation-carrying block is charged.
3. Entry/exit and finite transient amplification are absorbed by a bounded state potential.

Equivalently, there must be no cycle with both:

* nonnegative oscillation growth; and
* insufficient average charge.

Merely asserting that “persistent oscillation must spend positive density near the exceptional set” is exactly the missing statement. Deriving that assertion from concentration of the exceptional set, or from C1′ itself, would be circular.

A non-circular proof is a finite weighted-cycle/joint-spectral-radius certificate on the augmented low-window × depth-memory × spine-face automaton.

---

### 4. Clean finite-checkable sufficient lemma

Let \(\mathcal S\) be the augmented \(J=3\) state space. For every admissible length-\(L_w=6\) block \(\gamma:s\to s'\) and every admissible minimizing policy \(\sigma\), let:

* \(T_{\gamma,\sigma}\) be the homogenized profile map;
* \(e(\gamma)\in\mathbb N\) be its actual depth-memory charge;
* \(z>1\) be the Lemma 5 tilt;
* \(R_6\) be the normalized six-step tilted row bound:
  \[
  \sum_{\gamma:s\to *} w(\gamma)z^{e(\gamma)}h(s_\gamma)
  \le R_6 h(s).
  \]

A sufficient lemma is:

> **Charged spine-face Lyapunov lemma.**  
> There exist positive rational state potentials \(g(s)\), a finite polyhedral homogeneous oscillation carrier \(\Phi_s\), and a rational \(\rho>0\) such that
> \[
> \boxed{
> g(s')\,\Phi_{s'}\!\left(T_{\gamma,\sigma}x\right)
> \le
> \rho\,z^{e(\gamma)}\,g(s)\,\Phi_s(x)
> }
> \tag{CL}
> \]
> for every augmented state \(s\), every admissible six-step block \(\gamma\), every admissible minimizing policy \(\sigma\), and every extreme ray \(x\) of the corresponding profile-policy cone, with
> \[
> \boxed{R_6\rho<1.}
> \tag{SG}
> \]
> Moreover, \(\Phi\) must detect normalized oscillation:
> \[
> \operatorname{osc}(x)>t
> \quad\Longrightarrow\quad
> \Phi_s(x)\ge c_t\,\operatorname{mean}(x)
> \]
> for some \(c_t>0\), while the initial carrier/mean ratio is uniformly bounded.

Because \(T_{\gamma,\sigma}\) and \(\Phi_s\) are piecewise-linear homogeneous, (CL) is checked exactly on finitely many policy cones and extreme rays. Homogenization must include any affine source terms; otherwise a difference-only seminorm may miss creation of oscillation.

Iterating (CL), persistence for \(n\) blocks forces enough actual charge:
\[
c_t\lesssim \rho^n z^{E(\gamma)}.
\]
Lemma 5 then gives
\[
\nu_k\{\operatorname{osc}>t\}
\ll_t (R_6\rho)^n\to0.
\]

This inequality simultaneously certifies:

* strict contraction off the spine;
* only bounded/marginal behavior on the spine;
* pathwise charging of every marginal persistence mechanism.

If (CL) fails because of a zero-charge eigenvalue-1 cycle, the proposed localization architecture does not close.