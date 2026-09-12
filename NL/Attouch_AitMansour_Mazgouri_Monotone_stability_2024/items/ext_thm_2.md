## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_thm_2.lean`

## Lean statement
```lean
theorem ext_thm_2 {X : Type*} [MetricSpace X] [CompleteSpace X]
    (T₁ T₂ : X → Set X) (lam : ℝ) (hlam₁ : 0 ≤ lam) (hlam₂ : lam < 1)
    (hclosed₁ : ∀ x : X, IsClosed (T₁ x)) (hnonempty₁ : ∀ x : X, (T₁ x).Nonempty)
    (hclosed₂ : ∀ x : X, IsClosed (T₂ x)) (hnonempty₂ : ∀ x : X, (T₂ x).Nonempty)
    (hlip : ∀ x y : X,
      Metric.hausdorffEDist (T₁ x) (T₁ y) ≤ ENNReal.ofReal lam * edist x y ∧
      Metric.hausdorffEDist (T₂ x) (T₂ y) ≤ ENNReal.ofReal lam * edist x y) :
    Metric.hausdorffEDist (fixedPoints T₁) (fixedPoints T₂) ≤
      (1 - ENNReal.ofReal lam)⁻¹ *
        ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)
```

## Statement explanation
This declaration, `ext_thm_2`, is a stability theorem for fixed point sets of set-valued contractions in a complete metric space. Let $X$ be a complete metric space. Let $T_1,T_2:X\to \mathcal P(X)$ be set-valued maps, and let $\lambda$ be a real number with $0\le \lambda$ and $\lambda<1$. For each $x\in X$, both $T_1(x)$ and $T_2(x)$ are assumed to be closed and nonempty. The hypothesis `hlip` says that for every $x,y\in X$,

$$
d_H(T_1(x),T_1(y))\le \operatorname{ENNReal.ofReal}\lambda \cdot \operatorname{edist}(x,y)
$$

and also

$$
d_H(T_2(x),T_2(y))\le \operatorname{ENNReal.ofReal}\lambda \cdot \operatorname{edist}(x,y).
$$

Here $d_H$ denotes `Metric.hausdorffEDist`, the Hausdorff distance between sets taking values in the extended nonnegative reals, and $\operatorname{edist}$ is the extended distance between points. Thus each $T_i$ is a $\lambda$-contraction in the Hausdorff extended distance.

The Lean definition `fixedPoints T` is

$$
\operatorname{fixedPoints}(T)=\{x\in X\mid x\in T(x)\}.
$$

For a set-valued map, this is the set of points contained in their own image under $T$. The conclusion of `ext_thm_2` is

$$
d_H\bigl(\operatorname{fixedPoints}(T_1),\operatorname{fixedPoints}(T_2)\bigr)
\le
\bigl(1-\operatorname{ENNReal.ofReal}\lambda\bigr)^{-1}
\cdot
\sup_{x\in X} d_H(T_1(x),T_2(x)).
$$

The supremum is the uniform pointwise Hausdorff discrepancy between the two set-valued maps. Thus the theorem says that if two set-valued $\lambda$-contractions with closed nonempty values are uniformly close by $D$, then their fixed point sets are close by the contraction amplification factor $(1-\lambda)^{-1}$ times $D$. The hypothesis $0\le\lambda$ is part of the statement, although the supplied proof only explicitly uses $\lambda<1$.

## Lean proof
```lean
by
  let K : ENNReal := ENNReal.ofReal lam
  let D : ENNReal := ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x)
  have hK : K < 1 := by
    simpa [K] using ENNReal.ofReal_lt_one.2 hlam₂
  by_cases hD : D = ⊤
  · have hsub : 1 - K ≠ 0 := ne_of_gt (tsub_pos_iff_lt.2 hK)
    have hRHS : (1 - K)⁻¹ * D = ⊤ := by
      rw [hD, ENNReal.mul_top]
      exact ENNReal.inv_ne_zero.2 (by simp)
    rw [show (1 - ENNReal.ofReal lam)⁻¹ *
        ⨆ x : X, Metric.hausdorffEDist (T₁ x) (T₂ x) = (1 - K)⁻¹ * D by rfl, hRHS]
    exact le_top
  · have hDle (x : X) : Metric.hausdorffEDist (T₁ x) (T₂ x) ≤ D := by
      simpa [D] using le_iSup (fun z : X => Metric.hausdorffEDist (T₁ z) (T₂ z)) x
    suffices hside : ∀ (S U : X → Set X),
        (∀ x : X, IsClosed (S x)) → (∀ x : X, (S x).Nonempty) →
        (∀ x : X, IsClosed (U x)) → (∀ x : X, (U x).Nonempty) →
        (∀ x y : X, Metric.hausdorffEDist (S x) (S y) ≤ K * edist x y) →
        (∀ x y : X, Metric.hausdorffEDist (U x) (U y) ≤ K * edist x y) →
        (∀ x : X, Metric.hausdorffEDist (S x) (U x) ≤ D) →
        ∀ p : X, p ∈ fixedPoints S →
          Metric.infEDist p (fixedPoints U) ≤ (1 - K)⁻¹ * D by
      apply Metric.hausdorffEDist_le_of_infEDist
      · intro p hp
        exact hside T₁ T₂ hclosed₁ hnonempty₁ hclosed₂ hnonempty₂
          (fun x y => (hlip x y).1) (fun x y => (hlip x y).2) hDle p hp
      · intro p hp
        have hDle' (x : X) : Metric.hausdorffEDist (T₂ x) (T₁ x) ≤ D := by
          simpa only [Metric.hausdorffEDist_comm] using hDle x
        exact hside T₂ T₁ hclosed₂ hnonempty₂ hclosed₁ hnonempty₁
          (fun x y => (hlip x y).2) (fun x y => (hlip x y).1) hDle' p hp
    intro S U hSclosed hSne hUclosed hUne hS hU hSU p hp
    exact one_sided_lims_bound S U K D hK hD hSclosed hSne hUclosed hUne hS hU hSU p hp
```

## Proof explanation
The proof begins by introducing two abbreviations. Let

$$
K:=\operatorname{ENNReal.ofReal}\lambda
$$

and

$$
D:=\sup_{x\in X} d_H(T_1(x),T_2(x)).
$$

These are the Lean local definitions `K` and `D`. The first step is to prove $K<1$. The proof uses `ENNReal.ofReal_lt_one.2 hlam₂`. The theorem `ENNReal.ofReal_lt_one` says that a real number is less than $1$ exactly when its image in the extended nonnegative reals is less than $1$. Applying it to $\lambda<1$ gives $\operatorname{ENNReal.ofReal}\lambda<1$, and `simpa [K]` converts this to $K<1$.

Next the proof splits by cases on whether $D=\top$.

In the case $D=\top$, the right-hand side is infinite. The proof first records that $1-K\ne0$. Since $K<1$, the extended-real fact `tsub_pos_iff_lt` gives $0<1-K$, and `ne_of_gt` turns this positivity into $1-K\ne0$. Then the proof shows

$$
(1-K)^{-1}D=\top.
$$

Since $D=\top$, this becomes a statement about multiplication by $\top$ in the extended nonnegative reals. The relevant fact is that $a\cdot \top=\top$ whenever $a\ne0$. The proof verifies that $a=(1-K)^{-1}$ is nonzero using `ENNReal.inv_ne_zero`; this reduces to $1-K\ne\top$, which holds because $1-K\le 1$ and $1\ne\top$. Once the right-hand side is known to be $\top$, the proof rewrites the original expression using the definitional equalities for $K$ and $D$, obtains the target inequality with right-hand side $\top$, and closes it with `le_top`, since every extended nonnegative real is at most $\top$.

In the remaining case, $D\ne\top$. First the proof derives the pointwise bound

$$
d_H(T_1(x),T_2(x))\le D
$$

for every $x\in X$. This is exactly the supremum property `le_iSup`: for any index $x$, the $x$-th term of a family is at most the supremum of the whole family. The command `simpa [D]` unfolds the definition of $D$.

The proof then introduces an auxiliary claim `hside`. It says that for arbitrary set-valued maps $S,U:X\to\mathcal P(X)$, if both have closed nonempty values, if both are $K$-Lipschitz in the Hausdorff extended distance,

$$
d_H(S(x),S(y))\le K\cdot \operatorname{edist}(x,y),
\qquad
d_H(U(x),U(y))\le K\cdot \operatorname{edist}(x,y),
$$

and if they are uniformly pointwise close,

$$
d_H(S(x),U(x))\le D
$$

for every $x$, then every fixed point $p\in\operatorname{fixedPoints}(S)$ satisfies

$$
\operatorname{infEDist}\bigl(p,\operatorname{fixedPoints}(U)\bigr)
\le (1-K)^{-1}D.
$$

This auxiliary claim is proved by `intro` and then by applying the cited theorem `one_sided_lims_bound`. That theorem is precisely the one-sided contraction stability estimate: in a complete metric space, if two closed nonempty set-valued maps $S,U$ are both $K$-contractions with $K<1$, if $D\ne\top$, and if $d_H(S(x),U(x))\le D$ for all $x$, then every fixed point of $S$ lies within extended distance $(1-K)^{-1}D$ of the fixed point set of $U$. The proof of `hside` supplies exactly those hypotheses and obtains exactly that conclusion.

With `hside` available, the main goal is proved by applying `Metric.hausdorffEDist_le_of_infEDist`. This lemma reduces a bound on the Hausdorff distance between two sets to two one-sided point-to-set bounds: it is enough to show that every point of the first set has `infEDist` at most $(1-K)^{-1}D$ from the second set, and every point of the second set has `infEDist` at most $(1-K)^{-1}D$ from the first set.

The first such one-sided bound is obtained by applying `hside` with $S=T_1$ and $U=T_2$. The closedness and nonemptiness hypotheses come from `hclosed₁`, `hnonempty₁`, `hclosed₂`, and `hnonempty₂`. The Lipschitz hypotheses come from the two components of `hlip`: the first component bounds $d_H(T_1(x),T_1(y))$, and the second bounds $d_H(T_2(x),T_2(y))$. The uniform proximity hypothesis is exactly the previously proved bound $d_H(T_1(x),T_2(x))\le D$.

The second one-sided bound is obtained by applying `hside` with the roles reversed, $S=T_2$ and $U=T_1$. To do this, the proof needs the swapped pointwise bound

$$
d_H(T_2(x),T_1(x))\le D.
$$

It obtains this from $d_H(T_1(x),T_2(x))\le D$ using `Metric.hausdorffEDist_comm`, the symmetry of the Hausdorff extended distance. The Lipschitz hypotheses are swapped accordingly, using the second component of `hlip` for $T_2$ and the first component for $T_1$. Applying `hside` then gives the second one-sided `infEDist` bound.

Finally, `Metric.hausdorffEDist_le_of_infEDist` combines the two one-sided bounds and yields the desired inequality

$$
d_H\bigl(\operatorname{fixedPoints}(T_1),\operatorname{fixedPoints}(T_2)\bigr)
\le (1-K)^{-1}D,
$$

which is the stated conclusion after unfolding $K$ and $D$. The commands `rw`, `simpa`, `apply`, and `exact` perform the rewriting, simplification, application of the cited lemmas, and closing of goals with the supplied hypotheses. No `linarith` step occurs in this proof.

