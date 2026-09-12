## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/lem_1.lean`

## Lean statement
```lean
lemma lemma_2_1
    {sigma : ℝ} (hsigma : 0 ≤ sigma ∧ sigma < 1)
    {u v eta : H}
    (hv : v = u + eta)
    (heta : ‖eta‖ ≤ sigma * max ‖u‖ ‖v‖) :
    ‖v‖ ≤ ‖u‖ / (1 - sigma) ∧
      (1 - sigma) * ‖u‖ * ‖v‖ ≤ ⟪v, u⟫_ℝ
```

## Statement explanation
The lemma `lemma_2_1` is a purely metric and inner-product estimate. The variables $u,v,\eta$ all lie in the same ambient type $H$, on which a norm $`\|\cdot\|`$and a real inner product$\langle\cdot,\cdot\rangle_{\mathbb R}$are used. The scalar$\sigma\in\mathbb R$ is assumed to satisfy

$$
0\le \sigma<1.
$$

The two vector hypotheses are

$$
v=u+\eta
$$

and

```math
\|\eta\|\le \sigma\max(\|u\|,\|v\|).
```

Thus $v$ is obtained from $u$ by adding a perturbation $\eta$, and the size of this perturbation is controlled by a fraction $\sigma$ of the larger of the two norms $`\|u\|`$and$`\|v\|`$. The conclusion is the conjunction of two inequalities:

```math
\|v\|\le \frac{\|u\|}{1-\sigma}
```

and

```math
(1-\sigma)\|u\|\|v\|\le \langle v,u\rangle_{\mathbb R}.
```

The first inequality says that the norm of $v$ is not much larger than the norm of $u$; the factor $1/(1-\sigma)$ is finite because $\sigma\lt 1$. The second inequality gives a lower bound for the real inner product $\langle v,u\rangle_{\mathbb R}$. If $u$ and $v$ are nonzero, dividing by $`\|u\|\|v\|`$shows that the cosine of the angle between$v$and$u$ satisfies

$$
\cos\angle(u,v)\ge 1-\sigma.
$$

Since $1-\sigma\gt 0$, this is a positive alignment estimate between $u$ and $v$. In the extreme case $\sigma=0$, the hypothesis on $\eta$ forces $\eta=0$, hence $v=u$, and both conclusions become equalities. Thus the lemma states a quantitative stability property: a small relative perturbation of $u$ produces a vector $v$ whose norm is controlled and whose inner product with $u$ remains large enough.

## Lean proof
```lean
by
  rcases hsigma with ⟨hsig0, hsigl1⟩
  have hpos : 0 < 1 - sigma := sub_pos.mpr hsigl1
  have h1sub_nonneg : 0 ≤ 1 - sigma := le_of_lt hpos
  have part_i : ‖v‖ ≤ ‖u‖ / (1 - sigma) := by
    by_cases hcase : ‖v‖ ≤ ‖u‖
    · have hineq : ‖v‖ * (1 - sigma) ≤ ‖u‖ := by
        have hle1 : 1 - sigma ≤ 1 := by nlinarith
        have hmul₁ : ‖v‖ * (1 - sigma) ≤ ‖u‖ * (1 - sigma) :=
          mul_le_mul_of_nonneg_right hcase h1sub_nonneg
        have hmul₂ : ‖u‖ * (1 - sigma) ≤ ‖u‖ * 1 :=
          mul_le_mul_of_nonneg_left hle1 (norm_nonneg u)
        nlinarith
      exact (le_div_iff₀' hpos).mpr (by simpa [mul_comm] using hineq)
    · have hlt : ‖u‖ < ‖v‖ := lt_of_not_ge hcase
      have hmax : max ‖u‖ ‖v‖ = ‖v‖ := max_eq_right (le_of_lt hlt)
      have heta' : ‖eta‖ ≤ sigma * ‖v‖ := by
        simpa [hmax] using heta
      have htri : ‖v‖ ≤ ‖u‖ + ‖eta‖ := by
        calc
          ‖v‖ = ‖u + eta‖ := by rw [hv]
          _ ≤ ‖u‖ + ‖eta‖ := norm_add_le u eta
      have hchain : ‖v‖ ≤ ‖u‖ + sigma * ‖v‖ := by nlinarith
      have hineq : ‖v‖ * (1 - sigma) ≤ ‖u‖ := by nlinarith
      exact (le_div_iff₀' hpos).mpr (by simpa [mul_comm] using hineq)
  have part_ii : (1 - sigma) * ‖u‖ * ‖v‖ ≤ ⟪v, u⟫_ℝ := by
    by_cases hcase : ‖v‖ ≤ ‖u‖
    · have hmax : max ‖u‖ ‖v‖ = ‖u‖ := max_eq_left hcase
      have heta_bound : ‖eta‖ ≤ sigma * ‖u‖ := by
        simpa [hmax] using heta
      have h_inner_expand : ⟪v, u⟫_ℝ = ‖u‖ ^ 2 + ⟪eta, u⟫_ℝ := by
        calc
          ⟪v, u⟫_ℝ = ⟪u + eta, u⟫_ℝ := by rw [hv]
          _ = ⟪u, u⟫_ℝ + ⟪eta, u⟫_ℝ := by rw [inner_add_left]
          _ = ‖u‖ ^ 2 + ⟪eta, u⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      have hlow : -‖eta‖ * ‖u‖ ≤ ⟪eta, u⟫_ℝ := by
        have hcs := abs_real_inner_le_norm eta u
        have hlow' := (abs_le.mp hcs).1
        nlinarith
      rw [h_inner_expand]
      have h_nonneg_u : 0 ≤ ‖u‖ := norm_nonneg u
      have h_nonneg_v : 0 ≤ ‖v‖ := norm_nonneg v
      calc
        (1 - sigma) * ‖u‖ * ‖v‖ ≤ (1 - sigma) * ‖u‖ * ‖u‖ := by
          exact mul_le_mul_of_nonneg_left hcase (mul_nonneg h1sub_nonneg h_nonneg_u)
        _ = (1 - sigma) * ‖u‖ ^ 2 := by ring
        _ = ‖u‖ ^ 2 - sigma * ‖u‖ ^ 2 := by ring
        _ ≤ ‖u‖ ^ 2 + (-‖eta‖ * ‖u‖) := by nlinarith
        _ ≤ ‖u‖ ^ 2 + ⟪eta, u⟫_ℝ := by nlinarith
    · have hlt : ‖u‖ < ‖v‖ := lt_of_not_ge hcase
      have hmax : max ‖u‖ ‖v‖ = ‖v‖ := max_eq_right (le_of_lt hlt)
      have heta_bound : ‖eta‖ ≤ sigma * ‖v‖ := by
        simpa [hmax] using heta
      have hu_eq : u = v - eta := by
        calc
          u = (u + eta) - eta := by abel
          _ = v - eta := by rw [hv]
      have h_inner_expand : ⟪v, u⟫_ℝ = ‖v‖ ^ 2 - ⟪v, eta⟫_ℝ := by
        calc
          ⟪v, u⟫_ℝ = ⟪v, v - eta⟫_ℝ := by rw [hu_eq]
          _ = ⟪v, v⟫_ℝ - ⟪v, eta⟫_ℝ := by rw [inner_sub_right]
          _ = ‖v‖ ^ 2 - ⟪v, eta⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      have h_cauchy_high : ⟪v, eta⟫_ℝ ≤ ‖v‖ * ‖eta‖ := by
        exact (abs_le.mp (abs_real_inner_le_norm v eta)).2
      rw [h_inner_expand]
      have h_nonneg_u : 0 ≤ ‖u‖ := norm_nonneg u
      have h_nonneg_v : 0 ≤ ‖v‖ := norm_nonneg v
      calc
        (1 - sigma) * ‖u‖ * ‖v‖ ≤ (1 - sigma) * ‖v‖ * ‖v‖ := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left (le_of_lt hlt) (mul_nonneg h1sub_nonneg h_nonneg_v)
        _ = (1 - sigma) * ‖v‖ ^ 2 := by ring
        _ = ‖v‖ ^ 2 - sigma * ‖v‖ ^ 2 := by ring
        _ ≤ ‖v‖ ^ 2 - (‖v‖ * ‖eta‖) := by nlinarith
        _ ≤ ‖v‖ ^ 2 - ⟪v, eta⟫_ℝ := by nlinarith
  exact ⟨part_i, part_ii⟩
```

## Proof explanation
The proof begins with `rcases hsigma with ⟨hsig0, hsigl1⟩`, which unpacks the hypothesis $0\le \sigma\lt 1$ into the two facts $0\le\sigma$ and $\sigma\lt 1$. From $\sigma\lt 1$, the proof obtains

$$
0<1-\sigma
$$

using `sub_pos.mpr hsigl1`, and then weakens this to

$$
0\le 1-\sigma
$$

using `le_of_lt hpos`. The positivity of $1-\sigma$ is essential later because it permits division by $1-\sigma$.

The first conjunct is proved as `part_i`. The proof splits into two cases via `by_cases hcase : ‖v‖ ≤ ‖u‖`.

In the first case, $`\|v\|\le\|u\|`$. The goal is

```math
\|v\|\le \frac{\|u\|}{1-\sigma}.
```

The proof first shows the equivalent crossed inequality

```math
\|v\|(1-\sigma)\le \|u\|.
```

It uses `hle1 : 1-\sigma\le 1`, obtained by `nlinarith` from $0\le\sigma$. Then `mul_le_mul_of_nonneg_right` is the monotonicity rule for multiplication on the right: if $a\le b$ and $0\le c$, then $ac\le bc$. With $`a=\|v\|`$,$`b=\|u\|`$, and$c=1-\sigma$, it gives

```math
\|v\|(1-\sigma)\le \|u\|(1-\sigma).
```

Next, `mul_le_mul_of_nonneg_left` is the analogous rule on the left: if $a\le b$ and $0\le c$, then $ca\le cb$. With $a=1-\sigma$, $b=1$, and $`c=\|u\|`$, and using$`\|u\|\ge0`$, it gives

```math
\|u\|(1-\sigma)\le \|u\|\cdot 1=\|u\|.
```

Combining these two inequalities by `nlinarith` yields $`\|v\|(1-\sigma)\le\|u\|`$. Finally, `le_div_iff₀' hpos` is the equivalence that for a positive denominator $1-\sigma$,

$$
a\le \frac{b}{1-\sigma}
\quad\Longleftrightarrow\quad
a(1-\sigma)\le b.
$$

Applying it with $`a=\|v\|`$and$`b=\|u\|`$ gives the desired inequality, with `simpa [mul_comm]` reordering the product to match the form expected by the lemma.

In the second case, $`\|v\|\le\|u\|`$ is false, so `lt_of_not_ge` gives $`\|u\|<\|v\|`$. Hence `max_eq_right` gives

```math
\max(\|u\|,\|v\|)=\|v\|.
```

Substituting this into the hypothesis on $\eta$ yields

```math
\|\eta\|\le \sigma\|v\|.
```

The proof then uses the triangle inequality through `norm_add_le u eta`, which states

```math
\|u+\eta\|\le \|u\|+\|\eta\|.
```

Since $v=u+\eta$, this gives

```math
\|v\|=\|u+\eta\|\le \|u\|+\|\eta\|.
```

Together with $`\|\eta\|\le\sigma\|v\|`$, `nlinarith` obtains

```math
\|v\|\le \|u\|+\sigma\|v\|,
```

and then rearranges this to

```math
\|v\|(1-\sigma)\le \|u\|.
```

The same division lemma `le_div_iff₀'` with positive denominator $1-\sigma$ converts this into

```math
\|v\|\le \frac{\|u\|}{1-\sigma}.
```

This completes `part_i`.

The second conjunct is proved as `part_ii`. Again there is a case split on $`\|v\|\le\|u\|`$.

In the case $`\|v\|\le\|u\|`$, `max_eq_left` gives

```math
\max(\|u\|,\|v\|)=\|u\|,
```

so the perturbation bound becomes

```math
\|\eta\|\le \sigma\|u\|.
```

The proof then expands the inner product. Because $v=u+\eta$, and because `inner_add_left` says

$$
\langle u+\eta,u\rangle_{\mathbb R}
=\langle u,u\rangle_{\mathbb R}+\langle \eta,u\rangle_{\mathbb R},
$$

while `real_inner_self_eq_norm_sq` says

```math
\langle u,u\rangle_{\mathbb R}=\|u\|^2,
```

the proof obtains

```math
\langle v,u\rangle_{\mathbb R}
=\|u\|^2+\langle \eta,u\rangle_{\mathbb R}.
```

The proof also applies Cauchy–Schwarz in the form `abs_real_inner_le_norm eta u`, which gives

```math
|\langle \eta,u\rangle_{\mathbb R}|
\le \|\eta\|\|u\|.
```

Using `abs_le.mp` on this absolute-value inequality produces the two-sided bound

```math
-\|\eta\|\|u\|
\le \langle \eta,u\rangle_{\mathbb R}
\le \|\eta\|\|u\|.
```

The first part is used here, yielding

```math
-\|\eta\|\|u\|
\le \langle \eta,u\rangle_{\mathbb R}.
```

After rewriting the goal using the expansion of $\langle v,u\rangle_{\mathbb R}$, the proof establishes the chain

```math
(1-\sigma)\|u\|\|v\|
\le (1-\sigma)\|u\|^2
=\|u\|^2-\sigma\|u\|^2
\le
\|u\|^2-\|\eta\|\|u\|
\le
\|u\|^2+\langle \eta,u\rangle_{\mathbb R}.
```

The first inequality follows from $`\|v\|\le\|u\|`$and the nonnegativity of$`(1-\sigma)\|u\|`$, via `mul_le_mul_of_nonneg_left`. The two equalities are algebraic rearrangements performed by `ring`. The third inequality uses $`\|\eta\|\le\sigma\|u\|`$and$`\|u\|\ge0`$, which imply$`\|\eta\|\|u\|\le\sigma\|u\|^2`$, hence$`-\sigma\|u\|^2\le-\|\eta\|\|u\|`$. The final inequality uses$`-\|\eta\|\|u\|\le\langle \eta,u\rangle_{\mathbb R}`$. Thus

```math
(1-\sigma)\|u\|\|v\|
\le
\langle v,u\rangle_{\mathbb R}.
```

In the remaining case, $`\|v\|\le\|u\|`$is false, so$`\|u\|<\|v\|`$. Then

```math
\max(\|u\|,\|v\|)=\|v\|,
```

and the perturbation bound becomes

```math
\|\eta\|\le\sigma\|v\|.
```

The proof rewrites $u$ as

$$
u=v-\eta.
$$

Indeed, since $v=u+\eta$, one has $u=(u+\eta)-\eta=v-\eta$; this additive rearrangement is performed by `abel`. Then `inner_sub_right` gives

$$
\langle v,v-\eta\rangle_{\mathbb R}
=\langle v,v\rangle_{\mathbb R}-\langle v,\eta\rangle_{\mathbb R},
$$

and `real_inner_self_eq_norm_sq` gives $`\langle v,v\rangle_{\mathbb R}=\|v\|^2`$. Hence

```math
\langle v,u\rangle_{\mathbb R}
=\|v\|^2-\langle v,\eta\rangle_{\mathbb R}.
```

Cauchy–Schwarz `abs_real_inner_le_norm v eta` gives

```math
|\langle v,\eta\rangle_{\mathbb R}|
\le \|v\|\|\eta\|.
```

Using the upper half of this absolute-value inequality, the proof obtains

```math
\langle v,\eta\rangle_{\mathbb R}\le \|v\|\|\eta\|.
```

After rewriting the goal using the expansion of $\langle v,u\rangle_{\mathbb R}$, it proves the chain

```math
(1-\sigma)\|u\|\|v\|
\le (1-\sigma)\|v\|^2
=\|v\|^2-\sigma\|v\|^2
\le
\|v\|^2-\|v\|\|\eta\|
\le
\|v\|^2-\langle v,\eta\rangle_{\mathbb R}.
```

The first inequality follows from $`\|u\|\le\|v\|`$and the nonnegativity of$`(1-\sigma)\|v\|`$, again via multiplication by a nonnegative factor; `simpa` is used to reorder the products. The two equalities are obtained by `ring`. The third inequality uses $`\|\eta\|\le\sigma\|v\|`$and$`\|v\|\ge0`$, giving$`\|v\|\|\eta\|\le\sigma\|v\|^2`$, hence$`-\sigma\|v\|^2\le-\|v\|\|\eta\|`$. The final inequality uses$`\langle v,\eta\rangle_{\mathbb R}\le\|v\|\|\eta\|`$, which after negation gives$`-\|v\|\|\eta\|\le-\langle v,\eta\rangle_{\mathbb R}`$. Therefore

```math
(1-\sigma)\|u\|\|v\|
\le
\langle v,u\rangle_{\mathbb R}.
```

Finally, `exact ⟨part_i, part_ii⟩` packages the two established inequalities as the required conjunction. No separate local cited theorem statement is used; the proof relies on standard norm, real inner-product, maximum, Cauchy–Schwarz, and ordered-field facts appearing through the named lemmas above.

