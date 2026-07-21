## Bottom line

The \(J=3,L_w=6\) computation kills the **present CL certificate at that resolution**, but it does **not yet prove a no-go theorem for every \(J,L_w\)**. The structural facts you list establish accessibility of the marginal face, not recurrence inside the zero-charge neutral subgraph at every resolution.

The correct immediate move is:

1. formulate and run the exact **neutral-cycle/holonomy test** for larger \(J,L_w\);
2. if neutral zero-charge cycles persist, abandon charge-on-\(E_J\) CL entirely;
3. give the actual nonlinear min-operator one sharply time-boxed attempt via a synchronizing/strict-selection lemma;
4. otherwise pivot to cycles.

---

# 1. Is marginality intrinsic at all \(J\)?

## What is proved

At \(J=3,L_w=6\), yes: the certificate is impossible for a structural reason, not because of poor constants.

Let \(\widehat A_e\) denote the mean-normalized face operator. On the zero-charge cycle \(\gamma\), the co-spine ray
\[
\mathbb R_+(2,-1,-1)
\]
is invariant and
\[
\widehat A_\gamma v=v.
\]
Any Lyapunov functional that genuinely controls oscillation must be positive on \(v\). Iterating the CL inequality around \(\gamma\) therefore gives
\[
1\le \rho^{|\gamma|},
\qquad\text{hence}\qquad \rho\ge 1.
\]
Since the cycle has zero charge, \(R_6\) cannot compensate, and the target \(R_6\rho<1\) is impossible.

The one-line obstruction is:

> A nonzero oscillation ray contained in a recurrent zero-charge class makes the normalized joint spectral radius at least \(1\), while the pressure certificate requires it to be strictly below \(1\).

That is a complete no-go theorem for this instance and for any equivalent norm/Lyapunov reweighting that still detects that oscillation mode.

## What is not proved

The following three statements do **not** imply a neutral zero-charge cycle at every \(J,L_w\):

- \(E_J\) is sparse;
- the \(\langle4\rangle\)-orbit fills \(Q_J\);
- alignment and charge are independent coordinates.

The missing implication is recurrence. Accessibility of an aligned state at every ball does not imply that one can return to the same aligned orientation while avoiding \(E_J\).

A sparse set can still be a directed feedback set. The simplest logical counterexample is one directed cycle on \(Q_J\): a single charged vertex is sparse but intersects every cycle.

There is also a holonomy issue. Even when the zero-charge complement contains cycles, their permutation product may move the distinguished co-spine coordinate rather than stabilize it. “Alignment is reachable everywhere” does not imply “the cycle holonomy lies in the stabilizer of the co-spine ray.”

## Exact criterion to test

For each \((J,L_w)\), construct the lifted neutral graph whose states contain:

- the ball/residue state;
- aligned-face orientation;
- any policy/permutation data needed to determine the face operator.

Retain only zero-charge transitions. For every directed cycle \(\gamma\), compute the normalized product
\[
\widehat A_\gamma.
\]

The obstruction exists precisely when there is a cycle and a nonconstant face vector \(v\) such that
\[
\widehat A_\gamma v=v
\]
—or more generally when the constrained joint spectral radius of the zero-charge subsystem is at least \(1\).

In the purely permutation-controlled case, this reduces to a group-labeled SCC calculation: does the cycle-label semigroup intersect the stabilizer of a co-spine ray?

## How a finite larger \(J\) could beat the obstruction

There are three genuine mechanisms.

1. **Charge becomes a feedback set.**  
   Every zero-charge path has bounded length because every directed cycle meets \(E_J\). Then charge occurs with uniformly positive pathwise density.

2. **Nontrivial neutral holonomy.**  
   Zero-charge cycles remain, but every cycle product moves/mixes the co-spine direction and has normalized oscillation multiplier \(<1\).

3. **The nonlinear minimum destroys the face.**  
   The linearized policy graph admits a marginal cycle, but along the actual Bellman/min dynamics that policy is not minimizing on the corresponding nonconstant states. This does not rescue the present linear CL class; it is a different proof route.

Thus my decisive answer to Question 1 is:

> The \(J=3\) CL route is dead. A class-wide no-go is highly plausible, but it is not yet proved by sparsity, orbit-filling, and coordinate independence alone. The missing theorem is the existence, for every \(J,L_w\), of a zero-charge cycle whose holonomy stabilizes a nonzero oscillation ray.

This is finite and exactly checkable. I would run that test before investing in any new CL constants. If it persists through several structurally distinct \(J\), the right goal is then to prove the cycle family symbolically.

---

# 2. If the obstruction is intrinsic, what route remains?

## (a) Use the actual nonlinear min-operator

This is the strongest remaining route.

Pricing “oscillation persistence” is circular if the frequency of the charged event is inferred from the desired oscillation-decay statement. It is **not** circular if one proves a deterministic forcing statement from the exogenous arithmetic dynamics.

The right target is a synchronizing-word or strict-selection lemma:

> There exists a finite arithmetic word \(W\) and \(\eta>0\) such that, whenever \(W\) occurs, the actual min-composition satisfies
> \[
> \operatorname{osc}(T_Wx)
> \le (1-\eta)\operatorname{osc}(x)
> \]
> for every normalized nonconstant state \(x\).

Then the frequency or recurrence of \(W\) is proved from the residue/\(4\)-adic dynamics, independently of oscillation. That is non-circular.

A slightly more qualitative version would suffice:

1. identify the equality set for the min-operator;
2. prove that its maximal forward-invariant subset is the diagonal;
3. prove that forcing words recur independently of the current oscillation state.

The key technical question is therefore not “does low oscillation occur with positive density?” It is:

> Is there a residue word that forces the min to leave every nonconstant neutral face?

If yes, this can recover exponential decay when the word has positive frequency. If the word merely recurs with unbounded gaps, it can still give convergence without a geometric rate.

The \(J=3\) marginal linear policy does not rule this out: a policy can be linearly neutral yet fail to remain the actual minimizer after one or more iterations.

### Kill criterion for route (a)

Route (a) is dead if there is an exact nonconstant state and an arithmetic recurrent word/cycle on which:

- the same neutral lifts remain actual minimizers at every step, and
- normalized oscillation remains exactly constant.

That would be a nonlinear calibrated neutral orbit, not merely a linearized one.

This is the most important next computation.

---

## (b) Subexponential or renewal decay

This is logically sufficient, but it needs more than a Cesàro average.

Suppose there are effective renewal times \(\tau_1,\tau_2,\dots\) such that each renewal gives a fixed contraction:
\[
D_{\tau_{n+1}}\le (1-\eta)D_{\tau_n},
\qquad D=\operatorname{osc}/\operatorname{mean}.
\]
Then
\[
D_k\le D_0(1-\eta)^{N(k)},
\]
where \(N(k)\) is the number of renewals up to time \(k\).

To conclude \(\mathbb E_{\nu_k}D_k\to0\), positive-density renewals are unnecessary. It is enough that

\[
N(k)\longrightarrow\infty
\quad\text{in probability},
\]
together with a uniform bound or uniform integrability for \(D_k\). Dominated convergence then gives the desired decay. Thus arbitrarily sparse but recurrent strict-selection events can suffice.

For quantitative rates:

- exponential tails for renewal gaps give geometric decay;
- polynomial gap tails give polynomial decay;
- mere recurrence gives qualitative \(o(1)\).

What does **not** suffice is only
\[
\frac1k\sum_{j<k}\mathbb E D_j\to0,
\]
unless the final argument needs merely Cesàro convergence. That does not by itself imply \(\mathbb E D_k\to0\).

So route (b) is viable only if one can isolate an independently recurrent contracting event. It is not a substitute for finding such an event; it merely weakens the required frequency estimate.

Also, in finite-state forcing systems, recurrence often automatically has exponential tails. Genuine polynomial behavior usually indicates either:

- growing state spaces;
- near-neutral continuous states;
- contraction strength tending to zero;
- or a nonuniform family in \(J\).

The observed ratio drifting upward from \(0.81\) is compatible with polynomial decay, but it does not distinguish polynomial decay from a long crossover.

---

## (c) Arithmetic versus transfer operators

I would not conclude that \(\lambda_\infty=2\) is inaccessible to **all** transfer-operator methods. The failed object is narrower:

> linearized, autonomous face contraction certified by a charge supported only on the low-window exceptional set.

A nonlinear min-plus/Bellman operator with residue forcing is still a transfer-operator argument, but it can use strict selection that the face linearization erases.

That said, if a nonlinear calibrated neutral orbit exists, then the proof must use arithmetic to show that the relevant orbit has zero or vanishing statistical weight, or otherwise exploit cancellation/selection outside projective contraction. At that point the arithmetic is not optional.

---

# 3. Honest triage

| Direction | Tractability | Payoff | Verdict |
|---|---:|---:|---|
| Push nonlinear route (a) | \(6/10\) | \(10/10\) | Worth one focused attempt |
| Push renewal/subexponential route (b) | \(3.5/10\) | \(7/10\) | Backup only after identifying renewals |
| Pivot to cycles/finite places | \(8/10\) | \(8.5/10\) | Best main program |

## Recommendation

### 1. Time-box route (a)

Do exactly two things:

1. search for an exact **nonlinear calibrated neutral cycle**;
2. failing that, search for a finite **universally strict forcing word**.

These are clean yes/no outcomes.

- If a calibrated neutral cycle exists, the nonlinear contraction route is dead in essentially the same way as CL.
- If a strict forcing word exists, \(\lambda_\infty=2\) becomes credible again, and route (b) can handle weak recurrence if positive density is hard.

Do not spend time designing another weighted CL norm before these tests. The \(J=3\) obstruction is norm-independent.

### 2. Do not lead with route (b)

A generic “perhaps polynomial” program is too unconstrained. It becomes concrete only after you have:

- a renewal event;
- a definite contraction at each renewal;
- and an arithmetic recurrence estimate.

Without those, “Cesàro/renewal” is a slogan rather than a proof strategy.

### 3. Make cycles the main lane

The monodromy/sporadic-prime direction currently has:

- a clearer source of genuinely new results;
- finite-place structure untouched by archimedean exclusion arguments;
- more discrete and falsifiable intermediate targets;
- less dependence on proving a delicate global statistical contraction at the spectral boundary.

So my honest strategic judgment is:

> Do one short nonlinear-min kill test for \(\lambda_\infty=2\), but do not make it the main open-ended effort. Unless that test produces a forcing lemma quickly, pivot the main program to cycles and finite places.

The charged-Lyapunov route as presently formulated is dead at \(J=3\). It may or may not be dead as an abstract all-\(J\) class, but no further constant optimization is justified until the neutral-cycle criterion has been checked at larger resolutions.