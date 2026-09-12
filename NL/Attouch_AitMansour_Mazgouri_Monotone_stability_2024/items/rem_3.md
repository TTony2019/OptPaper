## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/rem_3.lean`

## Lean statement
```lean
theorem rem_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedSpace ℝ H] [NormedAddCommGroup M]
    (_φ : M → H → ℝ) (gradE : M → H → H) (gradφ : M → H → H) (X : M → ℝ → H)
    (β r T : ℝ) (hβ : 0 < β) (hr : 0 < r) (_hT : 0 < T)
    (hgradE : ∀ (μ : M) (q : H), gradE μ q = β • gradφ μ q)
    (hD_bdd : ∀ μ μ' : M,
      BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖gradφ μ u - gradφ μ' u‖})
    (hball : ∀ μ : M, ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖X μ t‖ ≤ r) :
    ∀ μ μ' : M, ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      ‖(gradE μ) (X μ t) - (gradE μ') (X μ t)‖ ≤ β * def_6 r hr (gradφ μ) (gradφ μ')
```

## Statement explanation
The theorem `rem_3` is a quantitative almost-everywhere stability statement for two parameterized families of maps on a normed space $H$, indexed by a parameter space $M$. Here $H$ is a real inner product space and in particular a normed additive commutative group, while $M$ is a normed additive commutative group. The declaration includes a map

$$
\varphi : M \to H \to \mathbb{R},
$$

which is not used, two maps

$$
\mathrm{gradE},\mathrm{grad}\varphi : M \to H \to H,
$$

and a trajectory map

$$
X : M \to \mathbb{R} \to H.
$$

For each $\mu \in M$, it is useful to write

$$
\mathrm{gradE}_\mu(q)=\mathrm{gradE}(\mu,q),\qquad
\mathrm{grad}\varphi_\mu(q)=\mathrm{grad}\varphi(\mu,q),\qquad
X_\mu(t)=X(\mu,t).
$$

The real parameters are $\beta,r,T$, with hypotheses

$$
0<\beta,\qquad 0<r,\qquad 0<T.
$$

The positivity $0\lt T$ is present in the statement but is not used in the proof.

The first substantive hypothesis is

$$
\forall \mu\in M,\ \forall q\in H,\qquad
\mathrm{gradE}_\mu(q)=\beta \bullet \mathrm{grad}\varphi_\mu(q).
$$

Thus, for every fixed $\mu$, the map $\mathrm{gradE}_\mu$ is pointwise equal to the scalar multiple of $\mathrm{grad}\varphi_\mu$ by $\beta$.

The second substantive hypothesis, `hD_bdd`, says that for every pair $\mu,\mu' \in M$, the set

```math
\left\{q\in\mathbb{R}\ \middle|\ \exists u\in H,\ \|u\|\le r
\text{ and } q=\|\mathrm{grad}\varphi_\mu(u)-\mathrm{grad}\varphi_{\mu'}(u)\|\right\}
```

is bounded above. In words, the discrepancy between the two maps $\mathrm{grad}\varphi_\mu$ and $\mathrm{grad}\varphi_{\mu'}$ over the closed ball of radius $r$ is bounded above. This is exactly the boundedness condition needed to apply the cited discrepancy bound.

The third hypothesis, `hball`, says that for every $\mu\in M$, for almost every $t$ with respect to Lebesgue measure on $\mathbb{R}$,

```math
t\in[0,T]\implies \|X_\mu(t)\|\le r.
```

So the curve $X_\mu$ is almost everywhere confined to the closed ball of radius $r$ on the interval $[0,T]$.

The conclusion is:

```math
\forall \mu,\mu'\in M,\quad
\forall^{\mathrm{a.e.}} t,\quad
t\in[0,T]\implies
\left\|\mathrm{gradE}_\mu(X_\mu(t))
-\mathrm{gradE}_{\mu'}(X_\mu(t))\right\|
\le
\beta\,\mathrm{def_6}\!\left(r,hr,\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}\right).
```

Thus, under the pointwise scaling relation between $\mathrm{gradE}$ and $\mathrm{grad}\varphi$, and under the almost-everywhere ball confinement of $X_\mu$, the difference between the two $\mathrm{gradE}$-maps evaluated at the same point $X_\mu(t)$ is bounded almost everywhere by $\beta$ times the discrepancy quantity associated to the corresponding $\mathrm{grad}\varphi$-maps.

The identifier `def_6` is an abbreviation:

$$
\mathrm{def_6}(r,hr,A,B)
=\mathrm{supDiscrepancyOnBall}(r,hr,A,B).
$$

The source does not give the full definition of `supDiscrepancyOnBall`, but the cited lemma `def_6_le_of_norm_le` supplies the exact property used here: if $0\lt r$, if $A,B:H\to H$, if the set

```math
\{q\in\mathbb{R}\mid \exists u\in H,\ \|u\|\le r
\text{ and } q=\|A u-B u\|\}
```

is bounded above, and if $u\in H$ satisfies $`\|u\|\le r`$, then

```math
\|A u-B u\|\le \mathrm{def_6}(r,hr,A,B).
```

So `def_6` is being used as an upper bound for the discrepancy of two maps on the ball of radius $r$. The theorem therefore transfers the uniform discrepancy bound for $\mathrm{grad}\varphi_\mu$ and $\mathrm{grad}\varphi_{\mu'}$ on the ball into an almost-everywhere bound for the corresponding $\mathrm{gradE}$-maps along $X_\mu$, with the extra factor $\beta$ coming from the pointwise scaling hypothesis.

## Lean proof
```lean
by
  intro μ μ'
  filter_upwards [hball μ] with t ht
  intro hmem
  have hD : ‖gradφ μ (X μ t) - gradφ μ' (X μ t)‖ ≤
      def_6 r hr (gradφ μ) (gradφ μ') :=
    def_6_le_of_norm_le hr (gradφ μ) (gradφ μ') (hD_bdd μ μ') (ht hmem)
  calc
    ‖gradE μ (X μ t) - gradE μ' (X μ t)‖ =
        ‖β • (gradφ μ (X μ t) - gradφ μ' (X μ t))‖ := by
          rw [hgradE μ (X μ t), hgradE μ' (X μ t), ← smul_sub]
    _ = β * ‖gradφ μ (X μ t) - gradφ μ' (X μ t)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    _ ≤ β * def_6 r hr (gradφ μ) (gradφ μ') :=
          mul_le_mul_of_nonneg_left hD hβ.le
```

## Proof explanation
The proof begins with `intro μ μ'`, fixing arbitrary parameters $\mu,\mu'\in M$. The goal is then the almost-everywhere statement

```math
\forall^{\mathrm{a.e.}} t,\quad
t\in[0,T]\implies
\left\|\mathrm{gradE}_\mu(X_\mu(t))
-\mathrm{gradE}_{\mu'}(X_\mu(t))\right\|
\le
\beta\,\mathrm{def_6}(r,hr,\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
```

Next, the tactic `filter_upwards [hball μ] with t ht` uses the almost-everywhere hypothesis `hball μ`. Mathematically, it restricts attention to the full-measure set on which the assertion

```math
t\in[0,T]\implies \|X_\mu(t)\|\le r
```

holds. After this step, $t$ is an arbitrary point satisfying that assertion, and the name `ht` denotes this fact:

```math
ht:\quad t\in[0,T]\implies \|X_\mu(t)\|\le r.
```

The goal becomes to prove the desired bound for such $t$. The tactic `intro hmem` then assumes the remaining hypothesis

$$
hmem:\quad t\in[0,T].
$$

Therefore `ht hmem` gives the ball condition

```math
\|X_\mu(t)\|\le r.
```

The proof then establishes the auxiliary inequality

```math
\|\mathrm{grad}\varphi_\mu(X_\mu(t))
-\mathrm{grad}\varphi_{\mu'}(X_\mu(t))\|
\le
\mathrm{def_6}(r,hr,\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
```

This is done by calling `def_6_le_of_norm_le` with $A=\mathrm{grad}\varphi_\mu$, $B=\mathrm{grad}\varphi_{\mu'}$, and $u=X_\mu(t)$. The hypotheses supplied are:
- $hr:0\lt r$;
- `hD_bdd μ μ'`, which says that the discrepancy set

```math
\{q\in\mathbb{R}\mid \exists u\in H,\ \|u\|\le r
\text{ and } q=\|\mathrm{grad}\varphi_\mu(u)-\mathrm{grad}\varphi_{\mu'}(u)\|\}
```

is bounded above;
- `ht hmem`, which gives $`\|X_\mu(t)\|\le r`$.

The cited lemma then yields precisely the displayed inequality. This inequality is named `hD` in the proof. Its role is to bound the difference of the two $\mathrm{grad}\varphi$-maps at the specific point $X_\mu(t)$ by the global discrepancy quantity `def_6`.

The remaining argument is a `calc` block that transforms the left-hand side into a multiple of the quantity bounded by `hD`.

First, the proof proves

```math
\|\mathrm{gradE}_\mu(X_\mu(t))
-\mathrm{gradE}_{\mu'}(X_\mu(t))\|
=\|\beta\bullet
(\mathrm{grad}\varphi_\mu(X_\mu(t))
-\mathrm{grad}\varphi_{\mu'}(X_\mu(t)))\|.
```

This uses the hypothesis `hgradE` twice, with $\mu$ and with $\mu'$, both evaluated at $X_\mu(t)$:

$$
\mathrm{gradE}_\mu(X_\mu(t))
=\beta\bullet \mathrm{grad}\varphi_\mu(X_\mu(t)),
\qquad
\mathrm{gradE}_{\mu'}(X_\mu(t))
=\beta\bullet \mathrm{grad}\varphi_{\mu'}(X_\mu(t)).
$$

After rewriting with these equalities, the expression becomes

```math
\|\beta\bullet \mathrm{grad}\varphi_\mu(X_\mu(t))
-\beta\bullet \mathrm{grad}\varphi_{\mu'}(X_\mu(t))\|.
```

The reverse rewrite `← smul_sub` uses the distributive law for scalar multiplication over subtraction:

$$
\beta\bullet a-\beta\bullet b
=\beta\bullet(a-b).
$$

Applying it gives the displayed equality.

Second, the proof proves

```math
\|\beta\bullet
(\mathrm{grad}\varphi_\mu(X_\mu(t))
-\mathrm{grad}\varphi_{\mu'}(X_\mu(t)))\|
=\beta\,
\|\mathrm{grad}\varphi_\mu(X_\mu(t))
-\mathrm{grad}\varphi_{\mu'}(X_\mu(t))\|.
```

The rewrite `norm_smul` gives

```math
\|\beta\bullet v\|=\|\beta\|\,\|v\|.
```

The rewrite `Real.norm_eq_abs` replaces $`\|\beta\|`$by$|\beta|$. Finally, since$hβ:0<\beta$, the lemma `abs_of_pos` gives $|\beta|=\beta$. Thus the scalar factor becomes simply $\beta$.

Third, the proof uses `mul_le_mul_of_nonneg_left hD hβ.le`. The lemma states that if $a\le b$ and $0\le c$, then $c a\le c b$. Here

```math
a=\|\mathrm{grad}\varphi_\mu(X_\mu(t))
-\mathrm{grad}\varphi_{\mu'}(X_\mu(t))\|,
```

$$
b=\mathrm{def_6}(r,hr,\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}),
\qquad
c=\beta.
$$

The inequality `hD` gives $a\le b$, and `hβ.le` gives $0\le\beta$. Therefore

$$
\beta a\le \beta b,
$$

which is exactly

```math
\beta\,
\|\mathrm{grad}\varphi_\mu(X_\mu(t))
-\mathrm{grad}\varphi_{\mu'}(X_\mu(t))\|
\le
\beta\,\mathrm{def_6}(r,hr,\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
```

Combining the equalities and this inequality through the `calc` block yields the required bound for

```math
\|\mathrm{gradE}_\mu(X_\mu(t))-\mathrm{gradE}_{\mu'}(X_\mu(t))\|.
```

Since $t$ was an arbitrary point on the full-measure set specified by `hball μ`, and since $t\in[0,T]$ was arbitrary under that condition, the `filter_upwards` step closes the almost-everywhere goal for the fixed $\mu,\mu'$. Finally, because $\mu,\mu'$ were arbitrary, the proof establishes the stated result for all pairs $\mu,\mu'\in M$.

