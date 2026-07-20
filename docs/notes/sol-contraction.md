Let  
\[
\operatorname{rng}(x):=\max_jx_j-\min_jx_j,\qquad
\bar x:=\frac13\sum_jx_j,\qquad
\Omega(x):=\frac{\operatorname{rng}(x)}{\bar x}
\]
for a positive three-vector \(x=(x_0,x_1,x_2)\). Thus \(\Omega\) is the mean-normalized fiber oscillation.

Write
\[
p=\lambda^{-2},\qquad q_2=\lambda^{\alpha-2},\qquad
q_8=\lambda^{\alpha-1}.
\]
For \(1<\lambda\le 2\),
\[
0<p<1,\qquad 0<q_2<1,\qquad q_8>1.
\]

## Lemma 1: Exact index arithmetic at a \(2\)-branch

Assume \(k\ge 3\), put \(Q=3^{k-1}\), \(Q'=3^{k-2}\), and let
\[
m_j=r+jQ,\qquad j\in\mathbf Z/3\mathbf Z,
\]
where \(r\equiv2\pmod9\).

1. **Transport.** If \(4r=r_4+hQ\), then
   \[
   4m_j\equiv r_4+(h+4j)Q\equiv r_4+(h+j)Q\pmod{3^k}.
   \]
   Thus transport sends the fiber over \(r\) to the fiber over \(4r\), with lift labels preserved up to one fixed cyclic shift \(j\mapsto h+j\).

2. **Retarded branch.** Let
   \[
   z=\frac{4r-2}{3}.
   \]
   Then
   \[
   R_2(m_j)=\frac{4(r+jQ)-2}{3}=z+4jQ'.
   \]
   If \(z=z_0+h'Q'\), then modulo \(Q=3Q'\),
   \[
   R_2(m_j)\equiv z_0+(h'+4j)Q'
   \equiv z_0+(h'+j)Q'.
   \]
   Hence the three branch targets are exactly the three level-\((k-1)\) lifts of \(z_0\bmod Q'\), again with indices aligned up to a fixed cyclic shift.

For comparison, at an \(8\)-branch,
\[
R_8(r+jQ)=\frac{2r-1}{3}+2jQ',
\]
so the induced permutation is \(j\mapsto h'+2j\), which swaps the two nonzero lift indices.

*Proof.* Direct modular arithmetic, using \(4\equiv1\pmod3\). ∎

---

## Lemma 2: Exact two-input form of the \(2\)-branch equation

After harmless cyclic relabeling, define
\[
t_j:=c(4m_j)
\]
and let \(Y_{j,\ell}\), \(\ell\in\mathbf Z/3\mathbf Z\), be the three level-\(k\) lifts of the branch target \(R_2(m_j)\). Put
\[
b_j:=\min_\ell Y_{j,\ell}.
\]
Then the fiber vector \(x_j:=c(m_j)\) satisfies
\[
x=p\,t+q_2\,b
\]
coordinatewise, and consequently
\[
\bar x=p\bar t+q_2\bar b.
\]

Thus a \(2\)-branch is a positive affine mixer of the transported fiber \(t\) and the three-vector \(b\) of branch minima.

∎

---

## Lemma 3: Sharp normalized oscillation inequality

For arbitrary positive three-vectors \(t,b\),
\[
\operatorname{rng}(pt+q_2b)
 \le p\,\operatorname{rng}(t)+q_2\,\operatorname{rng}(b).
\]
Therefore
\[
\boxed{\;
\Omega(x)\le A\,\Omega(t)+B\,\Omega(b)
\;}
\]
with
\[
\boxed{\;
A=\frac{p\bar t}{p\bar t+q_2\bar b},\qquad
B=\frac{q_2\bar b}{p\bar t+q_2\bar b}.
\;}
\]
Equivalently, if
\[
\rho_2:=\frac{q_2\bar b}{p\bar t}
      =\lambda^\alpha\frac{\bar b}{\bar t},
\]
then
\[
A=\frac1{1+\rho_2},\qquad B=\frac{\rho_2}{1+\rho_2}.
\]

These constants are sharp: equality holds whenever the maxima and minima of \(t\) and \(b\) occur at the same indices.

*Proof.* For every \(i,j\),
\[
x_i-x_j=p(t_i-t_j)+q_2(b_i-b_j)
 \le p\,\operatorname{rng}(t)+q_2\,\operatorname{rng}(b).
\]
Take the maximum over \(i,j\), divide by \(\bar x\), and use
\(\operatorname{rng}(t)=\bar t\,\Omega(t)\), etc. ∎

### Corollary 3.1: Genuine nonexpansion relative to the complete inputs

Since
\[
A+B=1,
\]
one has
\[
\boxed{\;
\Omega(x)\le \max\{\Omega(t),\Omega(b)\}.
\;}
\]
In particular, a \(2\)-branch cannot produce oscillation larger than both the transported oscillation and the oscillation already present among the three branch minima.

Moreover,
\[
\Omega(x)>\Omega(t)\quad\Longrightarrow\quad
\Omega(b)>\Omega(x)>\Omega(t).
\]
Thus every strict increase across a \(2\)-branch is imported through the \(R_2\)-minimum channel.

---

## Lemma 4: What min-Lipschitzness does—and does not—control

For the \(3\times3\) block \(Y=(Y_{j,\ell})\), define
\[
b_j=\min_\ell Y_{j,\ell}.
\]
Then
\[
|b_i-b_j|\le \max_\ell |Y_{i,\ell}-Y_{j,\ell}|,
\]
and hence
\[
\operatorname{rng}(b)
\le D(Y):=\max_\ell\operatorname{rng}_{j}(Y_{j,\ell}).
\]

*Proof.* The standard inequality
\[
|\min_\ell u_\ell-\min_\ell v_\ell|
 \le\max_\ell|u_\ell-v_\ell|
\]
applied to rows \(i,j\). ∎

This is a **cross-fiber** bound. It cannot be replaced by a bound involving only the internal oscillations
\[
\Omega(Y_{j,\bullet})
\]
of the three referenced fibers. Indeed, the three referenced fibers may each be constant while their constants differ.

### Denominator obstruction

Let
\[
\mu_j=\frac13\sum_\ell Y_{j,\ell},\qquad
\bar\mu=\frac13\sum_j\mu_j.
\]
Since \(b_j\le\mu_j\),
\[
\bar b\le\bar\mu.
\]
Using \(D(Y)/\bar\mu\) as the normalized branch-block oscillation gives
\[
\Omega(x)
 \le A\,\Omega(t)+B_*\,\frac{D(Y)}{\bar\mu},
\]
where
\[
B_*=\frac{q_2\bar\mu}{p\bar t+q_2\bar b}.
\]
Now
\[
A+B_*
 =1+\frac{q_2(\bar\mu-\bar b)}
          {p\bar t+q_2\bar b}
 \ge1.
\]
Equality holds precisely when \(\bar\mu=\bar b\), equivalently when every referenced fiber is constant in its lift variable. Thus the downward bias of the minimum worsens, rather than improves, a contraction estimate normalized by the referenced fiber means.

More generally, if the branch oscillation is normalized by a reference scale \(M\), then the coefficient sum is at most \(1\) exactly when \(M\le\bar b\). Natural choices based on fiber means usually satisfy \(M\ge\bar b\), so the desired inequality can fail.

---

## Lemma 5: Strict normalized increase through a \(2\)-branch is possible

The literal assertion “normalized oscillation cannot strictly increase through a \(2\)-branch” is false.

Take \(\lambda=2\). Then
\[
p=\frac14,\qquad q_2=2^{\alpha-2}=\frac34.
\]
Choose
\[
t=(1,1,1)
\]
and three constant referenced fibers
\[
Y_{0,\bullet}=(1,1,1),\quad
Y_{1,\bullet}=(1,1,1),\quad
Y_{2,\bullet}=(2,2,2).
\]
Thus every referenced fiber has internal oscillation zero, but
\[
b=(1,1,2).
\]
The \(2\)-branch output is
\[
x=\frac14t+\frac34b=(1,1,7/4).
\]
Therefore
\[
\Omega(t)=0,\qquad
\Omega(Y_{j,\bullet})=0\quad\text{for every }j,
\]
while
\[
\Omega(x)
 =\frac{7/4-1}{(1+1+7/4)/3}
 =\frac{3/4}{5/4}
 =\frac35.
\]

On the other hand,
\[
\Omega(b)=\frac{2-1}{4/3}=\frac34,
\]
and the sharp inequality gives equality:
\[
\Omega(x)=\frac15\Omega(t)+\frac45\Omega(b)=\frac35.
\]

Thus:

* oscillation can strictly increase relative to the transported fiber;
* it can do so even when every individual min-referenced fiber is internally flat;
* the increase is imported from variation **between** the three branch target fibers.

This local example refutes any universal no-increase theorem derived solely from the \(2\)-branch eigen-equation. Whether such an increase occurs in a particular certified global eigenvector is a separate numerical question.

---

# Correct surviving form of “oscillation is created only at the \(8\)-branch”

The literal normalized statement is false. A correct formulation separates nonexpansive mixing from superunit branch gain.

## Lemma 6: No affine branch creates oscillation absent from both incoming vectors

At either branch type \(e\in\{2,8\}\), write
\[
x=p\,t+q_e\,b.
\]
Then
\[
\Omega(x)\le
\frac{p\bar t}{\bar x}\Omega(t)
+\frac{q_e\bar b}{\bar x}\Omega(b),
\qquad
\frac{p\bar t}{\bar x}+\frac{q_e\bar b}{\bar x}=1.
\]
Hence if \(t\) and \(b\) are both constant, then \(x\) is constant. More generally,
\[
\Omega(x)\le\max\{\Omega(t),\Omega(b)\}.
\]

This applies equally to \(2\)- and \(8\)-branches. The difference is not normalized convexity.

## Lemma 7: Any increase at a \(2\)-branch is branch-imported

If
\[
\Omega(\operatorname{fiber}(r))
 >
\Omega(\operatorname{fiber}(4r))
\]
for \(r\equiv2\pmod9\), then the three-vector of \(R_2\)-minima has still larger oscillation:
\[
\Omega(b)>
\Omega(\operatorname{fiber}(r)).
\]
Thus a \(2\)-branch can relocate cross-fiber oscillation into a fiber, but cannot amplify it beyond the complete branch input.

## Lemma 8: Only the \(8\)-branch has superunit absolute branch gain

For absolute ranges,
\[
\operatorname{rng}(x)
 \le p\,\operatorname{rng}(t)+q_e\,\operatorname{rng}(b).
\]
At a \(2\)-branch,
\[
q_2=\lambda^{\alpha-2}<1,
\]
so the branch contribution to absolute range is attenuated:
\[
q_2\operatorname{rng}(b)<\operatorname{rng}(b).
\]
At an \(8\)-branch,
\[
q_8=\lambda^{\alpha-1}>1,
\]
so the branch channel is the unique channel capable of superunit one-step amplification of absolute range:
\[
q_8\operatorname{rng}(b)>\operatorname{rng}(b).
\]

This gives the defensible version of C3:

> **Corrected C3.** A \(2\)-branch is a normalized nonexpansive mixer and its branch channel has subunit absolute gain. Any normalized oscillation increase at a \(2\)-branch must be imported from cross-fiber variation among its \(R_2\)-minimum targets. The \(8\)-branch is the only branch with superunit absolute branch gain, and hence the only branch capable of dynamically amplifying branch-fed oscillation rather than merely transporting or redistributing it.

This formulation is compatible with the observed \(-1\) spike: the fixed \(R_8\)-feedback at \(-1\) repeatedly encounters the gain \(q_8=\lambda^{\alpha-1}>1\), whereas \(R_2\)-fed oscillation is multiplied by the subunit factor \(q_2\).