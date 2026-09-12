## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_thm_1.lean`

## Lean statement
```lean
theorem ext_thm_1 {X : Type*} [PseudoMetricSpace X] [Nonempty X]
    (T₁ T₂ : X → Set X) (lam ε : ℝ)
    (hlam₁ : 0 ≤ lam) (hlam₂ : lam < 1) (hε : 0 < ε)
    (hnonempty₁ : ∀ x : X, (T₁ x).Nonempty)
    (hnonempty₂ : ∀ x : X, (T₂ x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T₁ x) (T₁ y) ≤ ENNReal.ofReal lam * edist x y ∧
      Metric.hausdorffEDist (T₂ x) (T₂ y) ≤ ENNReal.ofReal lam * edist x y) :
    (approximateFixedPoints T₁ ε).Nonempty ∧ (approximateFixedPoints T₂ ε).Nonempty ∧
    Metric.hausdorffEDist (approximateFixedPoints T₁ ε) (approximateFixedPoints T₂ ε) ≤
      ENNReal.ofReal (ε / (1 - lam)) + (1 - ENNReal.ofReal lam)⁻¹ *
        ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)
```

## Statement explanation
Let $X$ be a nonempty pseudo-metric space. For a set-valued map $T : X \to \mathcal P(X)$ and a real tolerance $\varepsilon$, define the approximate fixed point set by

```math
\mathrm{AFix}(T,\varepsilon)
=\left\{x\in X:\ 0\le \varepsilon \ \text{and}\ \mathrm{infEDist}(x,T(x))\le \mathrm{ofReal}\varepsilon\right\}.
```

Here $\mathrm{infEDist}(x,T(x))$ is the extended infimum distance from the point $x$ to the set $T(x)$, and $\mathrm{ofReal}$ embeds a real number into the extended nonnegative real numbers $`\mathbb R_{\ge 0}\cup\{\infty\}`$.

The theorem considers two set-valued maps $T_1,T_2:X\to\mathcal P(X)$, a real contraction factor $\lambda$, and a positive real tolerance $\varepsilon$. Its hypotheses are:

- $0\le \lambda$ and $\lambda\lt 1$, so $\lambda\in[0,1)$;
- $0\lt \varepsilon$;
- for every $x\in X$, both $T_1(x)$ and $T_2(x)$ are nonempty;
- for every $x,y\in X$, both maps are Hausdorff-Lipschitz with the same constant $\lambda$:

$$
d_H(T_1(x),T_1(y))\le \mathrm{ofReal}\lambda \cdot d(x,y),
\qquad
d_H(T_2(x),T_2(y))\le \mathrm{ofReal}\lambda \cdot d(x,y).
$$

Here $d_H$ denotes the extended Hausdorff distance between sets, valued in $`\mathbb R_{\ge0}\cup\{\infty\}`$, and$d(x,y)=\mathrm{edist}(x,y)$ is the extended point distance.

The conclusion says three things. First, the approximate fixed point set of $T_1$ at tolerance $\varepsilon$ is nonempty. Second, the approximate fixed point set of $T_2$ at tolerance $\varepsilon$ is nonempty. Third, the extended Hausdorff distance between these two approximate fixed point sets is bounded by

```math
\mathrm{ofReal}\!\left(\frac{\varepsilon}{1-\lambda}\right)
+\left(1-\mathrm{ofReal}\lambda\right)^{-1}
\sup_{x\in X} d_H(T_1(x),T_2(x)).
```

Thus the theorem is a quantitative stability statement: two nonempty-valued Hausdorff contractions with the same contraction factor have nonempty approximate fixed point sets, and the distance between those sets is controlled by the uniform Hausdorff distance between the two maps plus the tolerance term $\varepsilon/(1-\lambda)$. If the supremum is infinite, then the right-hand side is infinite and the estimate becomes trivial; otherwise it is a genuine finite bound.

## Lean proof
```lean
by
  have happrox₁ : (approximateFixedPoints T₁ ε).Nonempty :=
    approximateFixedPoints_nonempty_of_hausdorff_contractive T₁ lam ε hlam₁ hlam₂ hε
      hnonempty₁ (fun x y => (hlip x y).1)
  have happrox₂ : (approximateFixedPoints T₂ ε).Nonempty :=
    approximateFixedPoints_nonempty_of_hausdorff_contractive T₂ lam ε hlam₁ hlam₂ hε
      hnonempty₂ (fun x y => (hlip x y).2)
  refine ⟨happrox₁, happrox₂, ?_⟩
  let D : ENNReal := ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)
  by_cases hDtop : D = ⊤
  · have hsubtop : 1 - ENNReal.ofReal lam ≠ ⊤ := ENNReal.sub_ne_top (by simp)
    rw [show (⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)) = D by rfl, hDtop,
      ENNReal.mul_top (ENNReal.inv_ne_zero.2 hsubtop)]
    exact le_top
  · have hDle : ∀ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x) ≤ D := fun x =>
      le_iSup (fun z : X => Metric.hausdorffEDist (T₁ z) (T₂ z)) x
    apply Metric.hausdorffEDist_le_of_infEDist
    · intro x hx
      exact approximateFixedPoint_infEDist_le T₁ T₂ lam ε hlam₁ hlam₂ hε hnonempty₁
        hnonempty₂ (fun x y => (hlip x y).2) D hDtop hDle hx
    · intro x hx
      exact approximateFixedPoint_infEDist_le T₂ T₁ lam ε hlam₁ hlam₂ hε hnonempty₂
        hnonempty₁ (fun x y => (hlip x y).1) D hDtop
        (fun y => by simpa only [Metric.hausdorffEDist_comm] using hDle y) hx
```

## Proof explanation
The proof first establishes the two nonemptiness claims. It uses the cited result `approximateFixedPoints_nonempty_of_hausdorff_contractive`, which says that if $T:X\to\mathcal P(X)$ has nonempty values, $\lambda\in[0,1)$, $\varepsilon\gt 0$, and

$$
d_H(T(x),T(y))\le \mathrm{ofReal}\lambda \cdot d(x,y)
$$

for all $x,y\in X$, then $\mathrm{AFix}(T,\varepsilon)$ is nonempty. The proof applies this result once to $T_1$, using the first conjunct of the hypothesis that both maps are $\lambda$-Lipschitz in Hausdorff distance, and once to $T_2$, using the second conjunct. This gives the facts

$$
(\mathrm{AFix}(T_1,\varepsilon)).\mathrm{Nonempty}
\quad\text{and}\quad
(\mathrm{AFix}(T_2,\varepsilon)).\mathrm{Nonempty}.
$$

The `refine` command then splits the conjunction conclusion into these two already-proved nonemptiness statements and the remaining Hausdorff-distance inequality.

For the remaining inequality, the proof sets

$$
D=\sup_{x\in X} d_H(T_1(x),T_2(x))
$$

as a local abbreviation in $`\mathbb R_{\ge0}\cup\{\infty\}`$. It then splits into two cases according to whether$D=\infty$.

In the case $D=\infty$, the right-hand side of the desired inequality becomes

```math
\mathrm{ofReal}\!\left(\frac{\varepsilon}{1-\lambda}\right)
+\left(1-\mathrm{ofReal}\lambda\right)^{-1}\cdot \infty.
```

The proof first shows that $1-\mathrm{ofReal}\lambda\ne\infty$. This uses `ENNReal.sub_ne_top`, applied to the fact that $1\ne\infty$; subtracting any extended nonnegative real from $1$ cannot produce $\infty$. Hence the inverse $\left(1-\mathrm{ofReal}\lambda\right)^{-1}$ is nonzero, by `ENNReal.inv_ne_zero`. The rewrite rule `ENNReal.mul_top` then turns a nonzero factor times $\infty$ into $\infty$. Therefore the entire right-hand side is $\infty$, and the inequality is closed by `le_top`, since every extended nonnegative real is at most $\infty$.

In the finite case $D\ne\infty$, the proof records that each pointwise distance is bounded by the supremum:

$$
d_H(T_1(x),T_2(x))\le D
$$

for every $x\in X$. This is the content of `le_iSup`: every value of the indexed family is at most its supremum.

The proof then applies `Metric.hausdorffEDist_le_of_infEDist`. In the current goal, this result is used in the following form: to prove

$$
d_H(\mathrm{AFix}(T_1,\varepsilon),\mathrm{AFix}(T_2,\varepsilon))\le C,
$$

where $C$ is the displayed right-hand side, it is enough to prove the two one-sided point-to-set estimates

$$
\forall x\in \mathrm{AFix}(T_1,\varepsilon),\quad
\mathrm{infEDist}(x,\mathrm{AFix}(T_2,\varepsilon))\le C,
$$

and

$$
\forall x\in \mathrm{AFix}(T_2,\varepsilon),\quad
\mathrm{infEDist}(x,\mathrm{AFix}(T_1,\varepsilon))\le C.
$$

This is exactly how Hausdorff distance controls how far each point of one set is from the other set, in both directions.

For the first of these two subgoals, `intro` introduces an arbitrary point $x$ and a proof that $x\in\mathrm{AFix}(T_1,\varepsilon)$. The proof then invokes the cited estimate `approximateFixedPoint_infEDist_le`. That lemma says, concretely, that if $S$ is $\lambda$-Hausdorff-contractive with nonempty values, $T$ has nonempty values, $T$ is uniformly within $D$ of $S$ in Hausdorff distance, and $x$ is an approximate fixed point of $T$ at tolerance $\varepsilon$, then

```math
\mathrm{infEDist}(x,\mathrm{AFix}(S,\varepsilon))
\le
\mathrm{ofReal}\!\left(\frac{\varepsilon}{1-\lambda}\right)
+\left(1-\mathrm{ofReal}\lambda\right)^{-1}D.
```

It is applied here with $T=T_1$ and $S=T_2$. The contraction hypothesis for $S$ is the second half of the standing Lipschitz hypothesis, namely the contraction estimate for $T_2$. The uniform closeness hypothesis is exactly $d_H(T_1(x),T_2(x))\le D$. This yields the first required estimate,

$$
\mathrm{infEDist}(x,\mathrm{AFix}(T_2,\varepsilon))\le C.
$$

For the second subgoal, `intro` again introduces an arbitrary point $x$ and the hypothesis that $x\in\mathrm{AFix}(T_2,\varepsilon)$. The same estimate `approximateFixedPoint_infEDist_le` is now applied with the roles reversed: $T=T_2$ and $S=T_1$. Its contraction hypothesis is the first half of the standing Lipschitz hypothesis, namely the contraction estimate for $T_1$. Its uniform closeness hypothesis requires

$$
d_H(T_2(y),T_1(y))\le D
$$

for all $y$. The proof obtains this from the already established inequality $d_H(T_1(y),T_2(y))\le D$ using `simpa only [Metric.hausdorffEDist_comm]`, which is the symmetry of Hausdorff extended distance: $d_H(T_2(y),T_1(y))=d_H(T_1(y),T_2(y))$. The lemma then gives

$$
\mathrm{infEDist}(x,\mathrm{AFix}(T_1,\varepsilon))\le C.
$$

Thus both one-sided estimates required by `Metric.hausdorffEDist_le_of_infEDist` have been proved, so that result yields the desired final bound

```math
d_H(\mathrm{AFix}(T_1,\varepsilon),\mathrm{AFix}(T_2,\varepsilon))
\le
\mathrm{ofReal}\!\left(\frac{\varepsilon}{1-\lambda}\right)
+\left(1-\mathrm{ofReal}\lambda\right)^{-1}
\sup_{x\in X} d_H(T_1(x),T_2(x)).
```

The tactic `rw` is used in the infinite-supremum case to replace the supremum by $D$, then $D$ by $\infty$, and to simplify the multiplication by $\infty$. The `simp` used inside that step proves the elementary side condition $1\ne\infty$ in the extended nonnegative reals. No use of `linarith` occurs in this proof.

