1. **Charge rule / \(C=1\).**
   - For the standard positive orthant, yes: if vectors are columns and \(A\ge0\) has no zero rows, then for \(x,y>0\),
     \[
     \min_i\frac{x_i}{y_i}\le \frac{(Ax)_j}{(Ay)_j}\le \max_i\frac{x_i}{y_i},
     \]
     so \(d_H(Ax,Ay)\le d_H(x,y)\). Thus \(C=1\) is sound. For row-vector action the required condition is no zero **columns**.
   - Caveats: this only covers interior points. On faces, require common support and that \(A\) maps the relevant relative interior into a common face. For the \(C_K\) product cone, positivity/no-zero-rows alone does not establish cone invariance or nonexpansion in that cone’s own metric.
   - The Chernoff rule is correctly oriented:
     \[
     Z_n\{Q\ge\theta n\}\le z^{-\theta n}\|T(z)^n\|,
     \]
     so \(R(z)<z^\theta\), equivalently \(R^{64}<z^{60}\), gives exponential decay. Charges must be additive and encoded exactly once in the same tilted operator. Reducibility can add a polynomial prefactor, harmless under the strict inequality. \(R_{\rm unc}<1\) alone needs bounded connector norms and the number of covered excursions bounded.

2. **Localization.**
   - In cocycle time it is valid: if every certified covered map has coefficient \(\le\tau\), all others \(\le1\), and the initial projective diameter is uniformly \(D<\infty\), then
     \[
     d_H(v_n,w_n)\le D\,\tau^{N_{\rm cov}}.
     \]
     Hence \(d_H>t\) implies
     \[
     N_{\rm cov}\le \frac{\log(D/t)}{-\log\tau}=O_t(1).
     \]
     Also require that the stated “oscillation” is quantitatively controlled by \(d_H\).
   - If contraction is attached to six-step **time intervals**, select disjoint intervals. A residue-class/greedy argument loses at most a factor \(6\), so \(O_t(1)\) disjoint covered blocks still implies only \(O_t(1)\) covered starting positions. Then uncovered density exceeds \(15/16\) for sufficiently large \(n\).
   - The shift/shift/\(\times2\) mixture is harmless only if each interval is an actual chronological cocycle block and the automaton tracks all carry/lookahead information. Disjoint six-digit cylinders of the original \(u\) are not automatically preserved by repeated \(\times2\); dependency cones can overlap or grow. Thus formulate localization in time, not in static digit space. If six digits are only state memory rather than six time maps, a separate bounded-overlap lemma is needed. Count only phases for which the \(\tau\) certificate was actually proved.

3. **Discharging H1.**
   - The strongest finite-state route is a rigorous vector-valued PF/cone certificate at the larger memory, likely \((3,9)\): retain the four sibling masses and cross-\(q\) fibers, derive the ratio inequalities from the eigenvector equations, and certify an invariant polyhedral cone by exact LP or interval arithmetic. A primitive/Doeblin block or bounded-distortion Ruelle-operator argument can then make the bound uniform in depth. Measurements at \(k=15,16\) alone do not prove this.
   - A two-sided natural extension helps encode carry and sibling correlations, but does not by itself remove H1. The infinite natural extension preserves normalization exactly. A finite lift preserves column sums only when each unresolved boundary extension is assigned a normalized kernel \(\kappa\); using the true \(\kappa\) is essentially the missing conditional-tail estimate, while choosing an arbitrary normalized kernel changes the model.
   - So the practical replacement is not “two-sided window alone,” but a finite two-sided/vector-state automaton plus a certified boundary conditional cone. This can preserve exact column normalization and should also address H2; merely cloning compatible extensions would inflate column sums, while uniform splitting would silently assume the desired independence.