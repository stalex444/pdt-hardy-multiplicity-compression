# The Exact Two-Step Hardy Ladder Optimum for Repeated Schmidt Levels

Stephanie Alexander · PDT

For the ideal two-step Hardy ladder, the exact winning probability for a state with positive Schmidt amplitudes proportional to $(b,c,a,\ldots,a)$, where $a$ occurs $m\ge2$ times, is

$$
\boxed{
P_{\max} =
\frac{\max\{E(b,c),\ E(b,a)+E(c,a)\}}{b^2+c^2+ma^2},
\qquad
E(x,y)=\left(\frac{xy^5-yx^5}{x^5+y^5}\right)^2.}
$$

Here the listed multiplicity counts the designated background coordinates. Either exceptional amplitude may also equal $a$. The experiment has three binary settings per observer and five forbidden events. The first strategy pairs $b$ with $c$. The second uses separate copies of $a$ to form two independent pairs. The maximum ranges over all terminal ranks. An optimal strategy uses at most four coordinates.

## The Hardy ladder series

This is the fifth work in Stephanie Alexander’s Hardy ladder series. The four earlier entries are registered with Palomar.

| Earlier entry | Connection to this work | Palomar record |
|---|---|---|
| The two-qubit Hardy ladder | Gives the winning probability as a function of the Schmidt ratio, proves uniqueness of the optimal ratio for each positive ladder length, and identifies the two-step plastic-constant value used here. | [PALOMAR-2026-10-30-000005](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000005) |
| The Two-Step Hardy Ladder in Higher Dimensions | Proves the sharp four-level matching bound. The present proof imports that bound after compressing to four coordinates. | [PALOMAR-2026-11-21-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-21-000002) |
| The Quartic Gate and the Two-Step Hardy Optimum | Studies preparation of the optimal two-qubit spectrum. Balanced inputs approach it under repeated uses of the gate, and a change in the input populations attains it in one use. | [PALOMAR-2026-11-23-000030](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000030) |
| Real Measurements and Sharp Pairing in the Five-Level Hardy Ladder | Gives a reduction to real measurements and proves sharp pairing for spectra proportional to $(s,2,3,4,5)$ with $0<s\le2$. The present result covers a different family, $(b,c,a,\ldots,a)$, in every dimension with at least two background copies. | [PALOMAR-2026-11-23-000034](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-23-000034) |

## Why the multiplicity disappears from the numerator

Let $D=\operatorname{diag}(d_1,\ldots,d_k,1,\ldots,1)$ with $m$ trailing ones and $d_i>0$. Write an arbitrary orthonormal terminal frame in two row blocks, $X=(Z;Y)$, and let $P=ZZ^*$. For any nonnegative integers $p,q$ define

$$
F_{p,q}(D,X)=\|(I-\Pi_{D^q X})D^p X\|_F^2
=\operatorname{Re}\operatorname{tr}(A_{2p}-A_{p+q}A_{2q}^{-1}A_{p+q}),
\quad A_j=X^*D^j X .
$$

The projection is onto the column space. Positivity of $D$ makes $A_{2q}$ invertible. The two-step Hardy score uses $(p,q)=(1,5)$. The earlier five-zero reduction identifies its maximum over the first endpoint with the winning probability up to normalization. For each first endpoint the other party can take the entire orthogonal complement of its fifth-power image. [Four-level predecessor, including the five-zero reduction](https://github.com/stalex444/pdt-hardy-ladder-higher-dimensions/blob/c9946d77c639d89bee866ae19a47f3f5bc0fcb7f/PROOF.md)

Write $L_j=\operatorname{diag}(d_i^j)-I_k$. Then $A_j=I+Z^*L_jZ$. With $L=L_{2q}$, $S=I+Z^*LZ$, and $Q=I+PL$, the identity $QZ=ZS$ and the rectangular determinant identity $\det Q=\det S$ give

$$
ZS^{-1}Z^*=Q^{-1}P=:K.
$$

To see how this removes the terminal rank from the trace, set $B=L_{p+q}-L_{2q}$ and $C=L_{2p}-2L_{p+q}+L_{2q}$. Subtract $A_{2q}$ on both sides of the quadratic term, expand, and cycle the trace. This yields the exceptional-coordinate formula

$$
F_{p,q}=\operatorname{Re}\operatorname{tr}(CP-BKBP).
$$

Every quantity on the right is determined by $P$ and the $k$ exceptional amplitudes. Also $P$ and $I-P$ are positive semidefinite. For the second assertion, $I-P=(I-P)^*(I-P)+(YZ^*)^*(YZ^*)$ by the orthonormality of $X$. Thus a single replacement frame on $2k$ coordinates is

$$
X' = \begin{pmatrix}P^{1/2}\\ (I-P)^{1/2}\end{pmatrix}.
$$

Its columns are orthonormal and its exceptional block has Gram matrix $P$. It preserves the exact score simultaneously for **every** positive exceptional spectrum and **every** exponent pair. Its rank is $k$, irrespective of the original terminal rank. At $m\ge k$, appending zero rows to a smaller frame proves the reverse inclusion. The entire set of unnormalized terminal scores stabilizes at $k$ background copies. For $m<k$ the construction still represents each original score on $2k$ coordinates.

For background amplitude $a>0$, divide all amplitudes by $a$ first. Scaling back multiplies the unnormalized score by $a^{2p}$, since the projected column space is unchanged and the target gains a factor $a^p$. Physical Hardy probabilities always use the norm of the **original** state.

## Sharp optimality when only two amplitudes are exceptional

Set $k=2$. The reduction sends every terminal frame to a two-plane on $(b/a,c/a,1,1)$. The registered four-level fixed-spectrum theorem bounds its two-step score by the best disjoint matching. Two of the three matchings agree because the last coordinates coincide. The witnesses can be written explicitly. On a pair $(x,y)$ use a line spanned by $(\sqrt{y^5},\sqrt{x^5})/\sqrt{x^5+y^5}$. The real vector formed by reversing the sign of the second coordinate is orthogonal to the fifth-power image. Their squared Hardy amplitude is $E(x,y)$. Disjoint pairs give orthogonal witnesses and their scores add. These constructions attain both branches of the formula. [Registered four-level theorem](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-21-000002)

For $m>2$ the probability is strictly below the plastic ceiling $p_*=(8\rho^2+\rho-11)/25$, where $\rho^3=\rho+1$ and $\rho>1$. The best four-level raw score is at most $p_*(b^2+c^2+2a^2)$ by the registered four-level bound. The original norm exceeds this four-level norm by $(m-2)a^2$. This gives the explicit margin $p_*-P_{\max}\ge p_*(m-2)a^2/(b^2+c^2+ma^2)$.

### A five-level example that the earlier deletion estimate misses

For $(1,1,1,2,3)$ the coordinate-deletion estimate gives $1073/6050$, or about 17.736%, above the plastic ceiling of approximately 17.455%. The exact maximum is $1521/12100$, or about **12.570%**, attained by pairing 2 with 3. For $(2,2,2,1,3)$ the other branch wins. Pairing 1 and 3 with different copies of 2 gives the exact probability $4292/33275$, or about **12.899%**. The independent check reproduces the pairs, rational values and deletion bounds.

## Scope and related work

For a single pair of Schmidt amplitudes $x,y$, Boschi et al., Eq. (18), give the two-qubit ladder probability. Cereceda, Eqs. (18)–(19), derives the optimizing settings at fixed Schmidt ratio. At two steps their normalized probability is exactly $E(x,y)/(x^2+y^2)$. In an earlier higher-dimensional construction, Ghirardi and Marinatto select two unequal Schmidt amplitudes to witness Hardy nonlocality and compute the success of those measurements in Eq. (26). Here the upper bound over all complex terminal frames proves which pairing wins for each spectrum $(b,c,a,\ldots,a)$. [Boschi et al. (1997)](https://doi.org/10.1103/PhysRevLett.79.2755) · [Cereceda (2002)](https://doi.org/10.1088/0305-4470/35/43/309) · [Ghirardi and Marinatto (2005)](https://doi.org/10.1103/PhysRevA.72.014105)

Liang, Spekkens and Wiseman, §IV.E, reported a numerical upper bound of 0.17456 and asked whether a partially entangled two-qubit state could already give the strongest contradiction. For the same three-setting binary ladder, Chen, Mal, Tabia and Liang report 0.17455 and 0.17459 as numerical lower and upper bounds in Table I(a), Boschi row. Both comparisons allow the state to vary. The theorem here gives the attained maximum for each prescribed spectrum in the two-exception family, including its dependence on the number of background copies. [Liang, Spekkens and Wiseman (2011)](https://doi.org/10.1016/j.physrep.2011.05.001) · [Chen et al. (2024)](https://doi.org/10.1103/PhysRevA.109.042206)

The square-root frame above has the geometry of Halmos's two-subspace theorem. In the generic part of that theorem, the projection is represented by positive contractions $C,S$ with $C^2+S^2=I$. The additional step here identifies the exceptional Gram matrix $P$ as sufficient to compute every weighted residual in the theorem. One frame then preserves the entire family of scores, and the registered four-level matching theorem supplies the exact two-exception optimum. The preceding four-level work also gives a written plastic-ceiling bound in arbitrary dimension for three distinct amplitudes when one is simple. The general five-distinct-amplitude pairing conjecture remains open. [Halmos (1969), Theorem 2](https://doi.org/10.1090/S0002-9947-1969-0251519-5) · [Registered four-level theorem](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-21-000002)

## Verification

The challenge statements use the three actual compressed powers, an unrestricted complex terminal frame, and an independent definition of the two competing probabilities. The sharp theorem is an attained maximum. It imports the four-level Gram bound at its registered commit. The four comparator targets passed both the Lean and Nanoda kernels locally. The only reported axioms are propext, Classical.choice, and Quot.sound. An independent seeded replay made 2,250 projection-score comparisons with largest absolute discrepancy below $2\times 10^{-13}$ on the verification machine. The experiment-to-terminal reduction and rescaling by an arbitrary positive background amplitude are explained above. The general exponent theorem concerns projection residuals. Its experimental interpretation here is the two-step case.

Run the following commands from this directory with the pinned Lean toolchain. The last command is an independent numerical and rational replay requiring NumPy.

```sh
lake exe cache get
lake build
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --inadvisably-no-sandbox
python3 check_compression.py
```
