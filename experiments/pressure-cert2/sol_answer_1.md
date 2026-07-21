- **Q1 — charge definition.**
  - The only charge justified by Lemma 5 is
    \[
    e(\gamma)=\sum_{i\in\gamma}\mathbf 1\{q_{i+1}\in E_3\},
    \qquad E_3=\{5,20,26\},
    \]
    with the target-state convention used in Lemma 5. For a six-move block, sum over its six low-window edges, including any \(T,B2,B8\) edges represented by that block.
  - Depth memory may augment the state to record top-window alignment, but it cannot redefine \(e\).
  - A top-window charge would require a separate pathwise comparison. For \(z>1\), a sufficient form is
    \[
    e_{\rm top}(\gamma)\le e_{\rm low}(\gamma)+H(s_0)-H(s_n)+C,
    \]
    where the coboundary is absorbed into \(g(s)\). No such comparison follows from Lemma 5 or the stated orbit-filling fact.

- **Q2 — decoupling.**
  - No stated mechanism forces aligned-class time to generate \(E_3\)-visits at density \(\ge0.513\). Orbit filling only says the \(\langle4\rangle\)-orbit eventually visits every low residue; it gives neither that density nor a coupling to the top digits.
  - However, independence for every finite horizon does **not by itself prove** an infinite zero-charge cycle. One must find a directed cycle/SCC in the finite augmented automaton satisfying simultaneously:
    1. the top depth-memory state remains on the oscillation-carrying aligned face;
    2. every low-edge target avoids \(E_3\);
    3. the cycle map is nonzero on the marginal face.
  - Thus the proposed certification has no valid coupling argument as stated. I expect the product-automaton search to produce the falsifying cycle, but its existence must be confirmed by that finite search rather than inferred solely from coordinate independence.

- **Q3 — expected eigenvalue.**
  - If the cycle stays exactly in the aligned face and implements the stated renormalized profile map, the predicted eigenvalue is **exactly \(1\)**, not \(>1\).
  - Around an \(n\)-block zero-charge cycle, state weights cancel, and CL implies
    \[
    \mu\le \rho^n.
    \]
    Hence \(\mu=1\) forces \(\rho\ge1\), giving zero Lyapunov gap and, under the intended SG budget, failure to close. It does **not** imply \(\lambda_\infty<2\).
  - A value \(>1\) requires a genuinely expanding cycle product—e.g. coupling outside the exact aligned restriction—not merely the marginal co-spine mode. Distinguish them by computing the exact rational cycle-product matrix on the transversal quotient and its characteristic polynomial/spectral radius, not by floating-point LP tolerances.

- **Q4 — cone and rays.**
  - Use the closed cone
    \[
    \overline C_K=\{v\ge0:v_i\le K v_j\ \forall i,j\}.
    \]
    For \(K>1\), its six extreme rays are the permutations of
    \[
    (K,1,1),\qquad (K,K,1).
    \]
  - The profile cone is \(\overline C_K^5\): tail plus four branch-source vectors. Importantly, the extreme rays of a direct-product cone are **not** Cartesian products of five rays; each has one active component on an extreme ray and the other four zero. Zero components are legitimate closure limits.
  - If each factor is separately normalized, Cartesian products of section vertices appear, but one must then add the five independent nonnegative scale variables. Otherwise relative source magnitudes are incorrectly fixed.
  - Policy extrema have every diagonal entry of each \(D_t\) at either \(3/(2K+1)\) or \(1\). Because \(D_tb^{(t)}\) is bilinear, the rigorous finite check should refine by policy vertices and by the linear cells of the polyhedral carriers; “all product vertices” alone is not generally sufficient.
  - CL must apply \(\Phi_{s'}\) to the **output profile** \(T_{g,s}X\) and \(\Phi_s\) to the **input profile** \(X\). If \(T\) outputs only the single fiber \(y\), then \(\Phi_s\) must be defined compatibly on that same profile type; otherwise the inequality is ill-typed.

**Expectation at \((J,L_w)=(3,6)\): FALSIFICATION**, most likely by an exact marginal \(\mu=1\) zero-charge cycle, because no supplied theorem couples the dangerous top face to the low-window charge.