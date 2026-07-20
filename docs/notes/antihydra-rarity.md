# Antihydra rarity: exact cylinder–seed transfer and the first rigorous population-level theorems behind the $(1/\varphi)^n$ heuristic

*2026-07-20. Companion scripts and machine verification: `experiments/antihydra-rarity/` (`verify_bijection.py`, `verify_automaton.py`, `verify_transfer.py`, `verify_phi.py`; output tables `theta_table.csv`, `qk_table.csv`). Context: `docs/CRYPTIDS.md` §1 (Antihydra spec), `docs/SMELL.md` errata item 3 (withdrawn "lottery ticket"; this note is the salvage of SMELL #2-transfer (ii)).*

**Summary of results.** Let $H(n)=\lfloor 3n/2\rfloor$ be the Antihydra base map and let $b$ be its counter ($+2$ on even, $-1$ on odd, $b_0=0$; the machine halts when $b$ hits $-1$). We prove:

1. **Lemma 1.3 (cylinder–residue bijection, Terras analogue).** For every $k\ge 1$ the first $k$ parities of the $H$-orbit define a *bijection* $\mathbb{Z}/2^k \to \{0,1\}^k$. Consequently every statistic of the first $k$ parity bits has an *exact* seed count. (Verified exhaustively for $k\le 20$.)
2. **Theorem 3.1 (window rarity).** The number of seeds $n\le x$ whose counter stays within a window $[0,C]$ above the halting boundary for the first $\lfloor\log_2 x\rfloor$ steps is at most $2K_C\,x^{\theta(C)}$ with $\theta(C)=\log_2\rho(C)<1$, where $\rho(C)$ is the Perron root of an explicit $(C{+}1)$-state automaton.
3. **Theorem 4.2 (structure of $\theta$).** $\rho(1)=0$, $\rho(2)=1$, $\rho(3)^3=2$, $\rho(4)^3=3$, $\rho(5)^3=2+\sqrt3$, $\rho(6)^3=(5+\sqrt{13})/2$; $\rho$ is strictly increasing for $C \ge 2$, and $$\lim_{C\to\infty}\theta(C) \;=\; \log_2 3-\tfrac23 \;=\; H(\tfrac13)\;\approx\; 0.9183 \;<\;1 .$$ **The working conjecture $\theta(C)\to 1$ ("full-shift recovery") is false**: the window forces odd-parity frequency $2/3$, an entropy cost that never vanishes. Rarity is therefore *uniform in $C$*: boundary-hugging seeds below $x$ never exceed $\approx x^{0.9183}$, no matter how wide the fixed window.
4. **Proposition 4.4 (no $\varphi$ coincidence).** No window automaton has Perron root $\varphi$; in particular the $C=1$ automaton is *not* the golden-mean shift ($L_1$ is empty). The suspected coincidence fails, and we can say exactly where $\varphi$ *does* live:
5. **Theorem 6.1 (the $\varphi$-law at population level).** The fraction of residues mod $2^k$ that halt within $k$ steps increases to $1/\varphi=\varphi-1=0.6180\ldots$, and within any non-halted cylinder at counter height $b$ the halting fraction of refinements tends to $\varphi^{-(b+1)}$ — the community's heuristic constant, now an exact counting theorem over seeds. Separately, exactly $F_{k+2}$ (Fibonacci) seeds mod $2^k$ have golden-mean-shift ("no 11") parity prefixes — the same subshift as in Mahler's Z-number bound.
6. **Theorem 5.1 / Corollary 5.2 (late-halt rarity).** With $c=\tfrac53-\log_2 3\approx 0.0817$: at most $41\,x^{1-c\delta}$ seeds $n\le x$ halt at a step between $\delta\log_2 x$ and $\log_2 x$; more generally any *late return* of the counter to within $C$ of the boundary is polynomially rare.

Everything is proved from scratch below; every numbered claim was verified numerically (§8). Nothing here says anything about seed $8$ itself; §7 states the honest corollary.

---

## 0. Setting and conventions

**The map.** For $n\in\mathbb{Z}_{\ge 0}$ let
$$H(n) \;=\; n+\Big\lfloor \frac n2\Big\rfloor \;=\; \Big\lfloor \frac{3n}2\Big\rfloor,\qquad\text{so } H(n)=\tfrac{3n}{2}\ (n\text{ even}),\quad H(n)=\tfrac{3n-1}{2}\ (n\text{ odd}).$$
Write $e_j(n) = H^j(n)\bmod 2 \in\{0,1\}$ for the **parity itinerary** ($e=0$ even, $e=1$ odd). The identity we use throughout:
$$2\,H(a) \;=\; 3a-(a\bmod 2)\qquad (a\in\mathbb{Z}_{\ge0}), \tag{0.1}$$
checked on both parities. ($H$ extends to $\mathbb Z$ with the same identity; we stay on $\mathbb Z_{\ge0}$.)

**The counter.** For a word $w=(e_0,\dots,e_{k-1})\in\{0,1\}^k$ define the counter path
$$b_0=0,\qquad b_{j+1}=b_j+2-3e_j \quad(\text{i.e. } +2 \text{ on } e_j=0,\ -1\text{ on }e_j=1),$$
and for a seed $n$ write $b_j(n)$ for the path of its itinerary. Explicitly $b_j = 2j-3\,O_j$ where $O_j=\#\{i<j: e_i=1\}$. The Antihydra machine (seed $8$) halts iff some $b_j=-1$, i.e. iff an odd term is met while $b=0$; equivalently iff some prefix has $O_j>2(j-O_j)$ (the wiki's "$O>2E$"). Since the counter's only negative step is $-1$, the first exit below $0$ is exactly the value $-1$: **"$b_j\ge 0$ for all $j\le k$" $\iff$ "not halted within $k$ steps."**

**The window convention (and its defense).** Fix an integer $C\ge 1$ and say a word (or seed) is **$C$-windowed for $k$ steps** if
$$b_j\in[0,C]\qquad\text{for all } 1\le j\le k. \tag{0.2}$$
Reasons this is the right object, and where the off-by-ones live:

- The lower endpoint $0$ is forced: $b=-1$ is the absorbing halt, so $[0,\cdot]$ = "still alive". Including $-1$ would count dead words whose continuations are machine-meaningless.
- The upper endpoint $C$ means "within distance $C+1$ of the absorbing value $-1$". Any additive re-indexing of the window just relabels $C$; no statement below depends on it.
- The constraint is imposed at **every** step through $j=k$, endpoint included. This is what makes the language factorial (prefix-closed) and automaton-recognizable, and it is what "boundary-hugging" means: never halting, never escaping upward. (Imposing it only at time $k$ would give a different — larger — set; the proof of Theorem 4.2(c) bounds even that set.)
- The horizon $k=\lfloor \log_2 x\rfloor$ for seeds $n\le x$ is forced by Lemma 1.3: $n \bmod 2^k$ pins exactly $k$ parity bits, no more. Cylinder counting cannot see deeper than $\log_2 x$ steps; §7 flags this honestly.

The degenerate small windows are computed, not assumed: $C=1$ gives the empty language (from $b=0$, the step $+2$ overshoots $1$ and the step $-1$ halts), and $C=2$ gives exactly one word per length, the cycle $(0\,1\,1)^\infty$ with counter $0\to2\to1\to0\to\cdots$. Rarity starts being interesting at $C=3$.

---

## 1. Lemma 1: the cylinder–residue bijection

**Lemma 1.1 (shift identity).** *For all integers $n\ge 0$, $t\ge 0$, $k\ge 1$ and $0\le i\le k$:*
$$H^i(n+2^k t)\;=\;H^i(n)+3^i\,2^{k-i}\,t. \tag{1.1}$$

*Proof.* Induction on $i$. For $i=0$ this is trivial. Assume (1.1) for some $i<k$ and set $m=H^i(n)$, $m'=m+3^i 2^{k-i}t$. Since $k-i\ge 1$, the shift $3^i2^{k-i}t$ is even, so $m'\equiv m \pmod 2$; call the common parity $e$. By (0.1),
$$2H(m') = 3m'-e = (3m-e)+3^{i+1}2^{k-i}t = 2H(m)+3^{i+1}2^{k-i}t,$$
hence $H^{i+1}(n+2^kt)=H(m')=H(m)+3^{i+1}2^{k-(i+1)}t$. $\blacksquare$

**Corollary 1.2.** *(a) For $i<k$, the parity $e_i(n)$ depends only on $n \bmod 2^k$ (the shift in (1.1) is even).*
*(b) The two lifts of a residue produce opposite next parities:* $e_k(n+2^k) = 1-e_k(n)$ *(at $i=k$ the shift is $3^k$, odd).*

By (a) the **itinerary map**
$$\Phi_k:\ \mathbb{Z}/2^k\mathbb{Z}\ \longrightarrow\ \{0,1\}^k,\qquad \Phi_k(n) = (e_0(n),\dots,e_{k-1}(n))$$
is well defined.

**Lemma 1.3 (cylinder–residue bijection; Terras analogue for $H$).** *For every $k\ge1$, $\Phi_k$ is a bijection.*

*Proof.* Induction on $k$. For $k=1$, $\Phi_1(n)=n\bmod 2$ is the identity $\mathbb Z/2\to\{0,1\}$.

Assume $\Phi_k$ is a bijection. Every residue mod $2^{k+1}$ is uniquely $\bar n + \varepsilon 2^k$ with $\bar n\in[0,2^k)$ and $\varepsilon\in\{0,1\}$, and by Corollary 1.2(a),
$$\Phi_{k+1}(\bar n+\varepsilon 2^k) \;=\; \big(\Phi_k(\bar n),\; e_k(\bar n+\varepsilon 2^k)\big).$$
By Corollary 1.2(b) the two choices of $\varepsilon$ give the two distinct extensions of the length-$k$ word $\Phi_k(\bar n)$. So $\Phi_{k+1}$ maps the two lifts of each residue $\bar n$ bijectively onto the two extensions of $\Phi_k(\bar n)$; since $\Phi_k$ is a bijection on the base level, $\Phi_{k+1}$ is a bijection. $\blacksquare$

**Remark 1.4 (the $3^{-1}\bmod 2^k$ view).** Injectivity alone has a one-line proof from invertibility of $3$: if $n\equiv n'\pmod 2$ (so equal $e_0$) and $H(n)\equiv H(n')\pmod{2^{k-1}}$, then by (0.1) $3(n-n')=2(H(n)-H(n'))\equiv 0 \pmod{2^k}$, and $3$ is a unit mod $2^k$, so $n\equiv n'\pmod{2^k}$; induct. This is the exact analogue of Terras' 1976 lemma for the Collatz map $T$, with the same mechanism: one parity-indexed affine branch, slope a unit in $\mathbb Z_2$.

**Remark 1.5 (consistency with the SMELL errata; what bijectivity does and does not permit).** Lemma 1.3 says every length-$k$ parity word — including the all-odd word $1^k$, realized by the residue $n\equiv 1$ (note $H(1)=1$) — occurs for **exactly one** residue class mod $2^k$. Hence the unconditioned window maxima of SMELL #3 are trivially $m_k=k$, exactly as the errata states, and *no* theorem below constrains any individual itinerary. What bijectivity **does** provide is the opposite service: it converts any word-count into an **exact seed-count**. Throughout, we count *seeds whose itinerary prefix satisfies a constraint*; we never bound itineraries.

**Numerical verification (script `verify_bijection.py`, all green).**
- (A1) For each $k=1,\dots,20$: the $2^k$ words $\{\Phi_k(n)\}_{n<2^k}$, computed by iterating $H$ on actual integers, are pairwise distinct (hence a bijection). At $k=20$: $1\,048\,576$ distinct words out of $1\,048\,576$.
- (A2) First-$k$ parities of $n$ and of $n\bmod 2^k$ agree for random $n<2^{40}$ and lifts $n+t2^k$, $t\le 3$ ($k\in\{5,12,20\}$).
- (A3) $e_k(n+2^k)=1-e_k(n)$ for all $n<2^k$, $k\le 14$.

---

## 2. The window language, its automaton, and the exact transfer

**Definition 2.1.** For $C\ge1$, $k\ge1$:
$$L_C(k) \;=\; \{\,w\in\{0,1\}^k \;:\; b_j(w)\in[0,C]\ \text{for } 1\le j\le k\,\}.$$

**Definition 2.2 (window automaton $A_C$).** Directed graph on states $\{0,1,\dots,C\}$ (the counter value), with edges
$$s \xrightarrow{\;e=0\;} s+2 \ \ (\text{if } s+2\le C), \qquad s \xrightarrow{\;e=1\;} s-1 \ \ (\text{if } s\ge 1);$$
transitions that would leave $[0,C]$ are absent (dead). We write $A_C$ also for its $(C{+}1)\times(C{+}1)$ 0/1 adjacency matrix, $\rho(C)$ for its spectral radius, and $\theta(C)=\log_2\rho(C)$.

By construction, $L_C(k)$ is exactly the set of length-$k$ edge-label sequences of paths starting at state $0$, so
$$|L_C(k)| \;=\; \sum_{s=0}^{C}\big(A_C^{\,k}\big)_{0,s}. \tag{2.1}$$

**Lemma 2.3 (graph structure).** *For $C\ge2$, $A_C$ is irreducible (strongly connected), and every cycle has length divisible by $3$ (period $3$).*

*Proof.* Down-edges give a path $s\to s-1\to\cdots\to 0$ from every state. From $0$: $0\to2$, $2\to1$ ($C\ge2$), and from any $s\ge0$ reached we reach $s+2\le C$ by an up-edge; so from $\{0,1,2\}$ we reach every state by up-steps. Hence strong connectivity. A cycle with $u$ up-steps and $d$ down-steps returns to its start, so $2u=d$ and its length is $u+d=3u$; cycles of length exactly $3$ exist ($s\to s+2\to s+1\to s$), so the period is exactly $3$. $\blacksquare$

(For $C=1$: from state $0$ both moves are dead, so $A_1$ is nilpotent, $\rho(1)=0$ and $L_1(k)=\emptyset$ for $k\ge1$. For $C=2$ the graph is the single $3$-cycle $0\to2\to1\to0$: $|L_2(k)|=1$, $\rho(2)=1$.)

**Lemma 2.4 (Perron upper bound with explicit constant).** *Let $C\ge2$. By Perron–Frobenius for irreducible nonnegative matrices there is a strictly positive right eigenvector $v$, $A_Cv=\rho(C)v$. Then for all $k\ge1$*
$$|L_C(k)| \;\le\; K_C\,\rho(C)^k,\qquad K_C \;=\; v_0\sum_{s=0}^{C}\frac1{v_s}$$
*(a scale-invariant constant).*

*Proof.* From $A_C^k v=\rho^k v$ read off the row $0$: $\sum_s (A_C^k)_{0,s}v_s=\rho^k v_0$. All terms are nonnegative, so $(A_C^k)_{0,s}\le \rho^k v_0/v_s$ for each $s$; sum over $s$ and use (2.1). $\blacksquare$

**Proposition 2.5 (exact transfer: seeds = words).** *For all $C,k\ge1$:*
$$\#\{\,0\le n<2^k \;:\; b_j(n)\in[0,C],\ 1\le j\le k\,\} \;=\; |L_C(k)|.$$

*Proof.* The event on the left depends only on $(e_0(n),\dots,e_{k-1}(n))=\Phi_k(n)$, which by Corollary 1.2(a) depends only on $n\bmod 2^k$; by Lemma 1.3, $\Phi_k$ is a bijection onto $\{0,1\}^k$, so the seeds satisfying the window condition are in bijection with the words in $L_C(k)$. $\blacksquare$

This equality is *exact*, not asymptotic — the model where "parity bits are fair coins" is, at the level of $k$-step prefixes of seeds mod $2^k$, not a heuristic but a theorem (uniform distribution of $\Phi_k$). All randomness talk below is shorthand for these exact uniform counts.

**Numerical verification (script `verify_transfer.py`).** At $k=20$, direct iteration of $H$ on all $2^{20}$ seeds versus the word DP:

| $C$ | seeds with $k=20$-step window | $|L_C(20)|$ |
|----|----|----|
| 1 | 0 | 0 |
| 2 | 1 | 1 |
| 3 | 64 | 64 |
| 4 | 1458 | 1458 |
| 6 | 13386 | 13386 |
| 10 | 100754 | 100754 |
| 40 | 407624 | 407624 |

Equal in every case (also across $k\in\{4,8,12,16,22\}$ at $C=6$), and Lemma 2.4's bound $K_C\rho^k$ was checked for $k\le60$, $C\in\{2,3,4,6,10,20\}$ in exact integer arithmetic.

---

## 3. The rarity theorem

**Theorem 3.1 (window rarity of seeds).** *Let $C\ge2$, $x\ge2$, $k=\lfloor\log_2 x\rfloor$. Then*
$$\#\{\,1\le n\le x \;:\; b_j(n)\in[0,C]\ \text{for } 1\le j\le k\,\}\;\le\; 2\,K_C\;x^{\theta(C)},$$
*with $\theta(C)=\log_2\rho(C)<1$ and $K_C$ as in Lemma 2.4. (For $C=1$ the count is $0$.)*

*Proof.* Since $x<2^{k+1}$, every $n\le x$ lies in $[0,2^{k+1})$, where each residue class mod $2^k$ has exactly two representatives. The window event for $k$ steps depends only on $n\bmod 2^k$ (Corollary 1.2(a)), so by Proposition 2.5 the count is at most $2|L_C(k)|\le 2K_C\rho(C)^k$ (Lemma 2.4). Finally $\rho(C)^k=2^{k\theta(C)}\le x^{\theta(C)}$ because $k\le\log_2x$ and $\theta(C)\ge0$ for $C\ge2$. That $\theta(C)<1$ — indeed $\theta(C)<H(1/3)\approx0.9183$ uniformly — is Theorem 4.2(c) below. $\blacksquare$

Interpretation: among all seeds up to $x$, those whose counter hugs the halting boundary (never halts, never escapes above $C$) throughout the observable horizon $\log_2 x$ form a set of size $O(x^{\theta(C)})$ — a power saving. By contrast a positive proportion ($\to 1-1/\varphi\approx0.382$, Theorem 6.1) survive with an *unbounded* counter, and proportion $\to1/\varphi$ halt. Boundary-hugging is the exponentially atypical behavior, exactly what the drift heuristic gestures at.

---

## 4. Structure of $\theta(C)$: exact values, strict monotonicity, and the true limit

Write $H(p)=-p\log_2p-(1-p)\log_2(1-p)$ for binary entropy; note $H(\tfrac13)=\log_23-\tfrac23=0.9182958\ldots$

**Lemma 4.1 (binomial toolkit).** *For integers $k\ge1$, $0\le j\le k$, real $\alpha\in[\tfrac12,1)$, and $m\ge1$:*
1. $\binom kj \le 2^{kH(j/k)}$;
2. $\displaystyle\sum_{i\ge\alpha k}\binom ki \le 2^{kH(\alpha)}$;
3. $\binom{3m}m \ge \dfrac{2^{3mH(1/3)}}{3m+1}$.

*Proof.* (1) With $p=j/k$: $1=(p+(1-p))^k\ge\binom kj p^j(1-p)^{k-j}$, and $p^{-j}(1-p)^{-(k-j)}=2^{kH(p)}$ (for $j\in\{0,k\}$ it is trivial).
(2) Tilt with $\lambda=\alpha/(1-\alpha)\ge1$: $\sum_{i\ge\alpha k}\binom ki\le\sum_{i=0}^k\binom ki\lambda^{\,i-\alpha k}=\lambda^{-\alpha k}(1+\lambda)^k$, and $\log_2[\lambda^{-\alpha}(1+\lambda)]=-\alpha\log_2\frac{\alpha}{1-\alpha}+\log_2\frac1{1-\alpha}=H(\alpha)$.
(3) The $3m{+}1$ numbers $t_i=\binom{3m}i(\tfrac13)^i(\tfrac23)^{3m-i}$ sum to $1$, and $t_{i+1}/t_i=\frac{3m-i}{2(i+1)}$, which is $\ge 1$ iff $i\le m-1$; so $t_m=\max_i t_i\ge\frac1{3m+1}$, i.e. $\binom{3m}m\ge\frac{3^m(3/2)^{2m}}{3m+1}=\frac{2^{3mH(1/3)}}{3m+1}$. $\blacksquare$

**Theorem 4.2 (structure of the Perron roots).**
*(a) (Exact small values.) $\rho(1)=0$, $\rho(2)=1$, and*
$$\rho(3)=2^{1/3},\quad \rho(4)=3^{1/3},\quad \rho(5)=(2+\sqrt3)^{1/3},\quad \rho(6)=\Big(\tfrac{5+\sqrt{13}}2\Big)^{1/3}.$$
*(b) (Strict monotonicity.) $\rho(C)<\rho(C+1)$ for every $C\ge2$ (and $\rho(1)<\rho(2)$).*
*(c) (Uniform bound and limit.) For every $C$, $\rho(C)<3\cdot2^{-2/3}=2^{H(1/3)}=1.8898\ldots$, and $\rho(C)\to3\cdot2^{-2/3}$ as $C\to\infty$. Equivalently*
$$\theta(C)\uparrow \log_23-\tfrac23 = H(\tfrac13)\approx0.918296\qquad(C\to\infty).$$

*Proof of (a).* $\rho(1)=0$ and $\rho(2)=1$ were computed in §2. Since every cycle of $A_C$ has length divisible by $3$ (Lemma 2.3), the characteristic polynomial of $A_C$ is a polynomial in $x^3$ times a power of $x$. Direct computation of $\det(xI-A_C)$ (machine-verified in exact integer arithmetic, script `verify_automaton.py`) gives, with $y=x^3$:
$$C{=}3:\ x\,(y-2),\quad C{=}4:\ x^2(y-3),\quad C{=}5:\ y^2-4y+1,\quad C{=}6:\ x\,(y^2-5y+3),$$
whose largest roots in $y$ are $2,\,3,\,2+\sqrt3,\,(5+\sqrt{13})/2$ respectively. (Continuing: $C{=}7$: $x^2(y^2-6y+6)$; $C{=}8$: $y^3-7y^2+10y-1$; and at $C{=}12$ the largest $y$-factor is $y^2-6y+1$, so $\rho(12)=(3+2\sqrt2)^{1/3}=(1+\sqrt2)^{2/3}$ — the silver ratio makes a cameo, the golden one never does; see Proposition 4.4.)

*Proof of (b).* Restricting $A_{C+1}$ to the states $\{0,\dots,C\}$ deletes exactly the up-edge $C-1\to C+1$ (up-edges $s\to s+2$ with $s+2\le C$ and all down-edges survive), so the principal submatrix of $A_{C+1}$ on $\{0,\dots,C\}$ **is** $A_C$. Let $\rho'=\rho(C+1)$ with right Perron vector $v>0$ (Lemma 2.3 gives irreducibility for $C+1\ge3$). For every $s\le C$,
$$(A_C\,v_{|})_s \;\le\; (A_{C+1}v)_s \;=\; \rho'\,v_s,$$
with **strict** inequality at $s=C-1$, where the deleted edge carried $v_{C+1}>0$. Let $u>0$ be a left Perron vector of $A_C$ (irreducible for $C\ge2$). Pairing:
$$\rho(C)\,\langle u,v_{|}\rangle \;=\; \langle uA_C,\,v_{|}\rangle \;=\; \langle u,\,A_Cv_{|}\rangle \;<\; \rho'\,\langle u,v_{|}\rangle,$$
the strict inequality because $u_{C-1}>0$ multiplies a strictly smaller coordinate. Since $\langle u,v_{|}\rangle>0$, $\rho(C)<\rho'$. ($\rho(1)=0<1=\rho(2)$ directly.) $\blacksquare$

*Proof of (c), upper bound.* Fix $C\ge2$ and let $v>0$ be the Perron vector, $s^*=\arg\max_s v_s$. Then
$$\rho^k v_{s^*}=(A_C^kv)_{s^*}=\sum_t (A_C^k)_{s^*,t}\,v_t\le \Big(\sum_t (A_C^k)_{s^*,t}\Big)v_{s^*}\le \|A_C^k\|_\infty\, v_{s^*},$$
so $\rho(C)^k\le\|A_C^k\|_\infty=\max_s\#\{\text{length-}k\text{ paths from }s\}$. A path from $s$ with $n_1$ down-steps ends at $b_k=s+2k-3n_1\in[0,C]$, hence $n_1\ge(2k+s-C)/3\ge(2k-C)/3=\alpha k$ with $\alpha=\tfrac23-\tfrac C{3k}$. For $k\ge2C$ we have $\alpha\ge\tfrac12$, so by Lemma 4.1(2) the number of paths from $s$ is at most $\sum_{i\ge\alpha k}\binom ki\le2^{kH(\alpha)}$. By concavity of $H$ (tangent line at $\tfrac13$, slope $H'(\tfrac13)=\log_22=1$) and symmetry,
$$H(\alpha)=H(1-\alpha)=H\!\Big(\tfrac13+\tfrac C{3k}\Big)\le H(\tfrac13)+\tfrac C{3k}.$$
Therefore $\rho(C)^k\le 2^{kH(1/3)}\,2^{C/3}$ for all $k\ge 2C$; taking $k\to\infty$ gives $\rho(C)\le2^{H(1/3)}$. Strictness for each finite $C$: by (b), $\rho(C)<\rho(C+1)\le2^{H(1/3)}$.

*Proof of (c), lower bound.* Given $C\ge6$, let $m=\lfloor(C-2)/4\rfloor\ge1$, so $4m+2\le C$, and set $h=2m+1\le C$. Consider closed walks at state $h$ of length $3m$ using $m$ up-steps and $2m$ down-steps in **any** order: every partial sum lies in $[h-2m,\,h+2m]=[1,\,4m+1]\subseteq[0,C]$ and the endpoint is $h$, so all $\binom{3m}m$ orderings are legal paths in $A_C$:
$$(A_C^{3m})_{h,h}\;\ge\;\binom{3m}m.$$
On the other hand, the diagonal bound $(A_C^{3m})_{h,h}\,v_h\le(A_C^{3m}v)_h=\rho^{3m}v_h$ gives $(A_C^{3m})_{h,h}\le\rho(C)^{3m}$. Combining with Lemma 4.1(3):
$$\rho(C)\;\ge\;\binom{3m}m^{1/(3m)}\;\ge\;2^{H(1/3)}\,(3m+1)^{-1/(3m)}\ \xrightarrow[C\to\infty]{}\ 2^{H(1/3)}. \qquad\blacksquare$$

**Remark 4.3 (correction of the working conjecture: no full-shift recovery).** The expected statement "$\theta(C)\to1$ as the window widens" is **false**. The reason is structural, not an off-by-one: membership in $L_C(k)$ constrains the counter *at time $k$ itself*, pinning the odd-parity count to $n_1\in[\frac{2k-C}3,\frac{2k}3]$ — frequency $\tfrac23+O(C/k)$, not the entropy-maximizing $\tfrac12$. The entropy ceiling $H(\tfrac13)$ is therefore built into *any* bounded window, uniformly in $C$. This strengthens the rarity theorem: boundary-hugging seeds below $x$ number $\lesssim x^{0.9183}$ **for every fixed window width whatsoever** (with the constant $2K_C\le2^{O(C)}$ absorbing the width). Full entropy is recovered only by deleting the upper constraint entirely ($C=\infty$, i.e. "alive at every step"), where the count is $\Theta(2^k)$: a positive proportion of seeds survives with unbounded counter (Theorem 6.1).

**Numerical table (script `verify_automaton.py`; full table `experiments/antihydra-rarity/theta_table.csv`).**

| $C$ | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 12 | 16 | 24 | 32 | 40 | $\infty$ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $\rho(C)$ | 0 | 1 | 1.2599 | 1.4422 | 1.5511 | 1.6265 | 1.7173 | 1.7996 | 1.8346 | 1.8630 | 1.8741 | 1.8795 | 1.88988 |
| $\theta(C)$ | $-\infty$ | 0 | 0.3333 | 0.5283 | 0.6333 | 0.7018 | 0.7801 | 0.8477 | 0.8755 | 0.8976 | 0.9062 | 0.9103 | 0.918296 |

Strict monotonicity holds along the whole table; all values sit below $3\cdot2^{-2/3}$; the block lower bound $\rho(4m+2)\ge\binom{3m}m^{1/3m}$ was checked at $m=2,5,9,20$.

**Proposition 4.4 (no golden-ratio coincidence — the $C=1$ guess resolved).** *For every $C\ge1$, $\rho(C)\ne\varphi=(1+\sqrt5)/2$. In particular the $C=1$ window automaton is not the golden-mean shift: $L_1(k)=\emptyset$ for $k\ge1$ (§2), whereas the golden-mean shift has $F_{k+2}$ words of length $k$.*

*Proof.* $\varphi^2=\varphi+1$ gives $\varphi^3=2\varphi+1=2+\sqrt5$. By Theorem 4.2(a), $\rho(5)^3=2+\sqrt3<2+\sqrt5<\tfrac{5+\sqrt{13}}2=\rho(6)^3$ (the last inequality is $2\sqrt5<1+\sqrt{13}$, i.e. $20<14+2\sqrt{13}$, true). By strict monotonicity (Theorem 4.2(b)), $\rho(C)\le\rho(5)<\varphi$ for $C\le5$ and $\rho(C)\ge\rho(6)>\varphi$ for $C\ge6$. $\blacksquare$

(Numerically the near-miss is $\rho(6)=1.6265$ vs $\varphi=1.6180$, i.e. $\theta(6)=0.7018$ vs $\log_2\varphi=0.6942$ — close enough to explain the guess, but provably not equal; exact non-divisibility of all characteristic polynomials by $x^2-x-1$ was additionally machine-checked for $C\le12$.) Where the golden ratio *does* genuinely appear in Antihydra seed statistics is §6.

---

## 5. Late returns to the boundary, and late halting, are polynomially rare

The window theorem constrains seeds that hug the boundary *at every step*. The halting predicate itself only needs the counter to *touch* $-1$ once — so the directly halting-relevant statement is about **returns**. Set
$$c \;=\; 1-H(\tfrac13)\;=\;\tfrac53-\log_23\;=\;0.0817042\ldots$$

**Theorem 5.1 (late visits to a boundary window).** *Let $C\ge0$ and let $1\le t_0\le k$ with $t_0\ge2C$. Then*
$$\#\{\,0\le n<2^k \;:\; b_j(n)\le C \ \text{for some } j\in[t_0,k]\,\}\;\le\; 19\cdot2^{C/3}\cdot 2^{\,k-c\,t_0}.$$
*(No lower constraint is imposed: the count includes seeds already halted — a superset.)*

*Proof.* Fix $j$. A word of length $k$ has $b_j\le C$ iff its length-$j$ prefix has $n_1(j)\ge(2j-C)/3=\alpha j$ with $\alpha=\tfrac23-\tfrac C{3j}$; the remaining $k-j$ letters are free. For $j\ge t_0\ge 2C$ we have $\alpha\ge\tfrac12$, so by Lemma 4.1(2) and the tangent bound $H(\alpha)\le H(\tfrac13)+\tfrac C{3j}$ (as in Theorem 4.2(c)),
$$\#\{w: b_j(w)\le C\}\;\le\;2^{jH(\alpha)}\,2^{k-j}\;\le\;2^{C/3}\,2^{k-cj}.$$
By Lemma 1.3 the same bound counts seeds mod $2^k$. Union over $j=t_0,\dots,k$ and sum the geometric series: $\sum_{j\ge t_0}2^{-cj}\le 2^{-ct_0}/(1-2^{-c})$, and $1/(1-2^{-c})=1/(1-3\cdot2^{-5/3})=18.16\ldots<19$. $\blacksquare$

**Corollary 5.2 (late halting is polynomially rare at population level).** *For $x\ge2$, $\delta\in(0,1]$, $k=\lfloor\log_2x\rfloor$:*
$$\#\{\,1\le n\le x \;:\; \text{the run from seed } n \text{ halts at a step } T\in[\delta k,\;k]\,\}\;\le\;41\; x^{\,1-c\,\delta}.$$

*Proof.* Halting at step $T$ means $b_T=-1$, i.e. $n_1(T)=(2T+1)/3$ (so $T\equiv1\bmod3$, else impossible). The number of length-$k$ words with $b_T=-1$ is $\binom T{(2T+1)/3}2^{k-T}$; since $(2T+1)/(3T)\ge\tfrac23\ge\tfrac12$ and $H$ decreases on $[\tfrac12,1]$, Lemma 4.1(1) gives $\binom T{(2T+1)/3}\le2^{TH(1/3)}$, so the count is $\le 2^{k-cT}$. Summing over $T\ge t_0=\lceil\delta k\rceil$: $\le19\cdot2^{k-c\delta k}$ words, hence (Lemma 1.3, two lifts per residue in $[0,2^{k+1})\supseteq[1,x]$) at most $38\cdot2^{k}2^{-c\delta k}$ seeds. Finally $2^k\le x$ and $2^{-c\delta k}\le2^{-c\delta(\log_2x-1)}=2^{c\delta}x^{-c\delta}\le2^{c}x^{-c\delta}\le1.06\,x^{-c\delta}$; and $38\cdot1.06<41$. $\blacksquare$

**Corollary 5.3 (many returns).** *If $\delta k\ge2C$, then*
$$\#\{\,0\le n<2^k \;:\; b_j(n)\le C \text{ for at least } \delta k \text{ indices } j\in[1,k]\,\}\;\le\;19\cdot2^{C/3}\cdot2^{(1-c\delta)k},$$
*because $\ge\delta k$ distinct visit times in $[1,k]$ force at least one visit time $j\ge\delta k$ (fewer than $\delta k$ indices precede it), and Theorem 5.1 applies with $t_0=\lceil\delta k\rceil$.* $\blacksquare$

With $x=2^k$ this is exactly the advertised form: seeds whose counter returns to within $C$ of the halting boundary at least $\delta\log_2x$ times in the first $\log_2x$ steps number at most $x^{1-c\delta+o(1)}$.

**Interpretation.** $c=1-H(\tfrac13)$ is the entropy deficit of the $2{:}1$ odd-parity bias that reaching the boundary requires. Corollary 5.2 is the population-level shadow of the heuristic "halting late requires odd-density $\approx2/3$, a linear discrepancy": among seeds $\le x$, all but a $x^{-c\delta}$-fraction settle their fate (halt or escape the boundary region for good) within the first $\delta\log_2 x$ steps of the observable window. The exponent is small ($c\approx0.08$) but *explicit and unconditional*.

---

## 6. The golden ratio as a population-level theorem

Everything so far bounds windowed seeds from above. We now compute exactly what fraction of seeds halts, and recover $\varphi$ — as a first-passage constant, not a window entropy. Notation: $\varphi=(1+\sqrt5)/2$, so $1/\varphi=\varphi-1=0.61803\ldots$ and $\varphi+\varphi^{-2}=2$.

**Definition.** $f_\ell = \#\{w\in\{0,1\}^\ell:\ b_j(w)\ge0 \text{ for } j<\ell,\ b_\ell(w)=-1\}$ (first passage to $-1$ at step $\ell$), and
$$q_k \;=\; 2^{-k}\,\#\{\,0\le n<2^k:\ \text{the run from seed } n \text{ halts within } k \text{ steps}\,\}.$$

**Theorem 6.1 (the $1/\varphi$ law for seeds).**
*(i) $q_k=\sum_{\ell\le k}f_\ell\,2^{-\ell}$; in particular $(q_k)$ is nondecreasing.*
*(ii) $\displaystyle\lim_{k\to\infty}q_k \;=\; \frac1\varphi \;=\; \frac{\sqrt5-1}2.$*
*(iii) (Conditional law = the community heuristic, exactly.) Let $w$ be any non-halted length-$m$ parity word with counter value $b=b_m(w)\ge0$, and let $R_w\subset\mathbb Z/2^m$ be its residue class (Lemma 1.3). Then the fraction of the $2^j$ refinements of $R_w$ mod $2^{m+j}$ that halt within $m+j$ steps is nondecreasing in $j$ with limit exactly $\varphi^{-(b+1)}$.*
*(iv) (Densities.) The set of seeds that ever halt has lower asymptotic density $\ge\varphi-1\approx0.618$; equivalently the set of never-halting seeds has upper density $\le2-\varphi\approx0.382$.*

*Proof.* **(i)** By Lemma 1.3, seeds halting within $k$ steps correspond to words of length $k$ whose counter hits $-1$; classifying by the first hitting time $\ell$, each first-passage word of length $\ell$ has exactly $2^{k-\ell}$ free continuations, so $2^kq_k=\sum_{\ell\le k}f_\ell2^{k-\ell}$.

**(ii)** *Step 1 (skip-free decomposition).* Since the counter's only downward step is $-1$, a walk from height $2$ that reaches $-1$ passes through $1$ and $0$ at well-defined first times; splitting there decomposes it uniquely into three consecutive segments, each (after translating the height down) a first-passage-to-$-1$ word; conversely any concatenation of three first-passage words, started at height $2$, stays $\ge0$ until its final step. A first-passage word either is "$1$" ($\ell=1$) or starts with "$0$" (height $2$) followed by such a triple. Hence
$$f_\ell=[\ell{=}1]+\sum_{i+j+m=\ell-1} f_if_jf_m\qquad(\ell\ge1). \tag{6.1}$$
*Step 2 (the cubic).* Let $q=\lim q_k\le1$ (monotone bounded). Multiplying (6.1) by $2^{-\ell}$ and summing over $\ell\le L$: with $F_L=\sum_{\ell\le L}f_\ell2^{-\ell}=q_L$,
$$q_L=\tfrac12+\tfrac12\sum_{i+j+m\le L-1}(f_i2^{-i})(f_j2^{-j})(f_m2^{-m}),$$
and the triple sum is squeezed between $q_{\lfloor(L-1)/3\rfloor}^3$ and $q_{L}^{3}$. All terms are nonnegative, so letting $L\to\infty$ (monotone convergence of the partial triple sums to the product of the limits) yields
$$q=\tfrac12+\tfrac12\,q^3,\qquad\text{i.e. } (q-1)(q^2+q-1)=0. \tag{6.2}$$
*Step 3 ($q<1$: an effective survivor count).* Set $N=27$ and consider the $2^{k-N}$ seeds (residues mod $2^k$, $k>N$) whose first $N$ parities are $0^N$; their counter reaches $b_N=2N=54$. For such a seed to die by step $k$ there must be a relative time $j'\ge1$ with $n_1(j')>\tfrac{2N+2j'}3$, where $n_1(j')$ counts ones among the next $j'$ letters. For $j'\le2N$ this exceeds $j'$ — impossible. For $j'>2N$, the offending prefix count is, by Lemma 4.1(2) with $\alpha=\frac{2N+2j'}{3j'}\ge\tfrac23$ (so $H(\alpha)\le H(\tfrac13)$), at most a $2^{-cj'}$-fraction of that level. Hence the dying fraction within this class is at most
$$\sum_{j'>2N}2^{-cj'}\;\le\;\frac{2^{-55c}}{1-2^{-c}}\;=\;0.807\ldots<1 ,$$
($c=0.08170\ldots$), uniformly in $k$. So for every $k$, at least $0.19\cdot2^{k-27}>2^{-30}\cdot2^k$ seeds survive $k$ steps, whence $q\le1-2^{-30}<1$.
*Step 4.* The roots of (6.2) are $1$ and $\frac{-1\pm\sqrt5}2$; the only root in $[0,1)$ is $\frac{\sqrt5-1}2=1/\varphi$. $\blacksquare$ *(for (i),(ii))*

**(iii)** By the same skip-freeness, a first passage from height $b$ to $-1$ decomposes uniquely into $b+1$ consecutive first-passages-down-one; so the count $f^{(b)}_\ell$ of such words has $\sum_{\ell\le L}f^{(b)}_\ell2^{-\ell}$ squeezed between the $(b{+}1)$-fold products of partial sums of $f_\ell2^{-\ell}$, and the same monotone-limit argument gives $\lim_j q^{(b)}_j=q^{b+1}=\varphi^{-(b+1)}$, where $q^{(b)}_j$ is the fraction of length-$j$ words from height $b$ that hit $-1$ within $j$ steps. Now condition on the cylinder $w$: by Lemma 1.3 applied at level $m+j$, the refinements of $R_w$ are in bijection with the $2^j$ continuation words, and the halting ones (within $m+j$ steps) are exactly those whose continuation hits $-1$ from height $b$ within $j$ steps. **(iv)** For each $k$, the set of seeds halting within $k$ steps is a union of residue classes mod $2^k$, hence periodic with exact density $q_k$; a set containing, for every $k$, a periodic subset of density $q_k$ has lower density $\ge\sup_kq_k=1/\varphi$. Complementing gives the second phrasing. $\blacksquare$

**Remark 6.2 (what (iv) does not claim).** Whether the halting-seed density *exists* (equals $1/\varphi$ exactly) is open: it would require showing that seeds surviving $k$ steps do not later halt en masse — precisely the kind of infinite-horizon control that is the hard core of the problem. The finite-$k$ statements (i)–(iii) are exact and unconditional.

**Proposition 6.3 (the golden-mean shift enters exactly — Fibonacci seed counts).** *Let $F_1=F_2=1,F_{j+2}=F_{j+1}+F_j$. The number of seeds $n\in[0,2^k)$ whose first $k$ parities contain no factor $11$ (no two consecutive odd iterates — the golden-mean subshift) is exactly $F_{k+2}$. Moreover every such seed whose parity prefix moreover begins with $0$ satisfies $b_j\ge1$ for $1\le j\le k$: it provably does not halt within $k$ steps; there are $F_{k+1}$ of these.*

*Proof.* Count of no-$11$ binary words of length $k$ is $F_{k+2}$ (transfer matrix $[[1,1],[1,0]]$, standard induction); Lemma 1.3 converts words to seeds. For the certificate: induction on $j$ — if $e_{j-1}=0$ then $b_j=b_{j-1}+2\ge2$; if $e_{j-1}=1$ then $j\ge2$ (the word starts with $0$) and $e_{j-2}=0$ (no $11$), so $b_j=b_{j-2}+2-1\ge b_{j-2}+1\ge1$. $\blacksquare$

So $x^{\log_2\varphi}\approx x^{0.694}$ seeds below $x$ carry a *golden-mean certificate* of $\log_2x$-step survival — the same subshift, with the same Fibonacci count, that Mahler used to bound Z-numbers by $x^{\log_2\varphi}$ (up to a log factor; there: pointwise confinement of $\{\xi(3/2)^n\}$ forces no-$11$ for the conjugate map $\lceil3n/2\rceil$; here: no-$11$ forces counter growth for $\lfloor3n/2\rfloor$). **The precise relation between the two golden ratios:** Mahler's $\varphi$ is the growth rate of a *forbidden-factor subshift*; the Antihydra heuristic's $\varphi$ is the *first-passage constant* of Theorem 6.1, i.e. the root of $q=\frac{1+q^3}2$ — same number, provably different mechanisms, and by Proposition 4.4 the window automata realize neither.

---

## 7. Corollary: what this does — and does not — say about Antihydra

**Corollary 7.1 (the honest cryptid statement).** *Fix any window width $C\ge2$ and any $\delta\in(0,1]$. Among the seeds $1\le n\le x$ of the Antihydra map (same rule, same counter, variable seed):*
1. *at most $2K_C\,x^{\theta(C)}$ hug the halting boundary (counter in $[0,C]$) throughout the first $\lfloor\log_2x\rfloor$ steps, with $\theta(C)<\log_23-\tfrac23\approx0.9183<1$ — a power saving uniform in $C$ (Theorems 3.1, 4.2);*
2. *at most $41\,x^{1-c\delta}$ halt at any step in $[\delta\log_2x,\ \log_2x]$, $c=\tfrac53-\log_23$ (Corollary 5.2);*
3. *the fraction that halts within $\log_2x$ steps converges to $1/\varphi$, and within every surviving cylinder at counter height $b$ the halting fraction of refinements converges to $\varphi^{-(b+1)}$ (Theorem 6.1) — the community's $(1/\varphi)^{b+1}$ heuristic is exact at population level.*

**What this does NOT say.** Nothing above constrains the orbit of the single seed $8$. The Antihydra question is about one point of the system; our theorems say that the behavior conjectured for that point — never halting, counter escaping upward, no long boundary-hugging — is shared by all but a power-savings-small exceptional set of seeds, *within the horizon $\log_2x$*. Three limitations are structural and worth stating plainly:

- **Single-seed silence.** Population rarity can never, by itself, decide seed $8$: exceptional sets of size $x^{0.9}$ are uncountably plentiful in itinerary space, and Lemma 1.3 (bijectivity) guarantees that *every* finite boundary-hugging pattern is realized by some seed. Deciding seed $8$ requires controlling the equidistribution of one specific $\lfloor(3/2)\cdot\rfloor$-orbit's parities — the Mahler/Z-number wall (cf. `docs/SMELL.md` #2).
- **Horizon $\log_2x$.** All statements pin exactly $\lfloor\log_2x\rfloor$ parity bits, the information content of a seed $\le x$; cylinder counting is provably unable to see one step further (again by bijectivity: beyond $k$ bits, all continuations occur equally often). Statements about halting at superlogarithmic times have *no* population-level content obtainable this way.
- **Heuristic calibration, not derandomization.** Theorem 6.1 proves the fair-coin model is exact for prefix statistics *averaged over seeds*. The open problem is whether the specific orbit of $8$ behaves like a typical seed — this note quantifies precisely what "typical" means, and how thin the alternative is, but does not touch the specific orbit.

**Relation to the withdrawn claim (SMELL errata #3).** That claim tried to bound window maxima over *all* residues, which bijectivity makes trivial ($m_k=k$). The present note inverts the quantifier: it *uses* bijectivity as the counting tool and bounds *how many* residues realize each windowed behavior. There is no tension; Lemma 1.3 is simultaneously the reason the old claim was vacuous and the engine of the new theorems.

---

## 8. Numerical verification (all scripts in `experiments/antihydra-rarity/`)

| Script | Verifies | Result |
|---|---|---|
| `verify_bijection.py` | Lemma 1.3 exhaustively for $k\le20$ ($2^{20}$ residues); Corollary 1.2(a) on random $n<2^{40}$; Corollary 1.2(b) for $k\le14$ | all pass |
| `verify_automaton.py` | $\theta(C)$ for $C=1..40$ (→ `theta_table.csv`); strict monotonicity; $\rho(C)<3\cdot2^{-2/3}$; exact char. polys $C\le8$ (sympy, exact); $x^2-x-1$ divides no char. poly $C\le12$; $|L_C(k)|\le K_C\rho^k$ for $k\le60$ (exact integers); block lower bound at $m=2,5,9,20$ | all pass |
| `verify_transfer.py` | Proposition 2.5: seed counts (direct $H$-iteration, all $2^{20}$ seeds) $=$ word counts, $C\in\{1,2,3,4,6,10,40\}$, plus $k\in\{4,8,12,16,22\}$ at $C=6$; Theorem 3.1 bound | exact equality; bounds hold |
| `verify_phi.py` | Theorem 6.1: $q_k$ in exact rational arithmetic, $k\le700$ (→ `qk_table.csv`): $q_{700}=0.618033988750$ vs $1/\varphi=0.618033988750$; conditional limits at $b=1,2,3$ match $\varphi^{-(b+1)}$ to $9$ digits; recurrence (6.1) for $\ell\le40$ against direct DP; Proposition 6.3 Fibonacci counts at $k=5,10,15,20$ (e.g. $17711=F_{22}$ at $k=20$); Theorem 5.1/Corollary 5.2 tail bounds at $k=60$ | all pass |

Key numbers: $q_{100}=0.6180240$, $q_{700}$ agrees with $1/\varphi$ to $12$ digits; $\theta(40)=0.9103$ vs limit $0.918296$; $\min_{C\le40}|\rho(C)-\varphi|=0.0084$ (attained at $C=6$, provably nonzero).

---

## 9. Loose ends (flagged, not papered over)

1. **Density of halting seeds.** We prove lower density $\ge1/\varphi$ and give the exact finite-level law; existence of the density (Remark 6.2) is open and appears to require genuinely new control of survivors' futures.
2. **Sharpness of Theorem 5.1's exponent.** The union bound costs nothing at leading order for a *single* late visit, but Corollary 5.3 (many returns) is presumably far from sharp — an occupation-time large-deviation rate (via the tilted automaton spectrum) would improve $1-c\delta$; not pursued.
3. **Closed form for $\rho(C)$.** The $y=x^3$ characteristic polynomials ($y-2$, $y-3$, $y^2-4y+1$, $y^2-5y+3$, $y^2-6y+6$, $y^3-7y^2+10y-1,\dots$) beg for a product/continuant formula (they resemble strip-transfer continuants); we did not find one in closed form, only the exact limit $27/4$ of $\rho(C)^3$.
4. **Perron–Frobenius citations.** Existence of strictly positive left/right eigenvectors for irreducible nonnegative matrices is quoted as standard (Seneta, *Non-negative Matrices*, Thm 1.5); everything else spectral is proved inline (Lemmas 2.4, diagonal/row bounds in Theorem 4.2).
5. **Seed $8$.** Untouched, necessarily (§7).
