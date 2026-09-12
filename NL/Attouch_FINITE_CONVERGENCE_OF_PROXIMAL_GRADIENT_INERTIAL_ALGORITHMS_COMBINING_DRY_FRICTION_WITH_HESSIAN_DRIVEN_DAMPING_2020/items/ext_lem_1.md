## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/ext_lem_1.lean`

## Lean statement
```lean
theorem dryFriction_equivalences {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (_hconvex : ConvexOn ℝ Set.univ phi) (_hcontinuous : Continuous phi)
    (_hmin : ∀ x, phi 0 ≤ phi x) (hzero : phi 0 = 0) :
    (((0 : H) ∈ interior (subdifferential phi 0)) ↔
      (∃ r > 0, Metric.ball (0 : H) r ⊆ subdifferential phi 0)) ∧
    ((∃ r > 0, Metric.ball (0 : H) r ⊆ subdifferential phi 0) ↔
      (∃ r > 0, ∀ xi : H, phi xi ≥ r * ‖xi‖)) ∧
    ((∃ r > 0, ∀ xi : H, phi xi ≥ r * ‖xi‖) ↔
      (∃ r > 0, ∀ g : H, ‖g‖ ≤ r → ∀ xi : H, inner ℝ g xi ≤ phi xi))
```

## Statement explanation
The declaration is stated in a real inner product space $H$. The function is $\phi:H\to\mathbb R$. The assumptions are:

- $H$ is a normed additive commutative group with a real inner product structure.
- $\phi$ is convex on all of $H$: `_hconvex : ConvexOn ℝ Set.univ phi`.
- $\phi$ is continuous: `_hcontinuous : Continuous phi`.
- $0$ is a global minimizer of $\phi$: `_hmin : ∀ x, phi 0 ≤ phi x`.
- The value at the origin is normalized to zero: `hzero : phi 0 = 0`.

The proof does not use `_hconvex`, `_hcontinuous`, or `_hmin`; they are present in the statement but play no role in the formal argument. The only hypothesis actually invoked is `hzero`, together with positivity of the radii chosen in the proof.

Let $\partial \phi(0)$ denote `subdifferential phi 0`. With the normalization $\phi(0)=0$, a vector $g$ belongs to $\partial \phi(0)$ exactly when it satisfies the subgradient inequality at zero:

$$
\forall \xi\in H,\qquad \langle g,\xi\rangle_{\mathbb R}\le \phi(\xi).
$$

The theorem asserts three equivalences, which together say that four conditions are equivalent:

1. $0$ lies in the interior of the subdifferential at zero:

   $$
   0\in \operatorname{int}\bigl(\partial \phi(0)\bigr).
   $$

2. There is an open ball around $0$ contained in the subdifferential:

   $$
   \exists r>0,\qquad B(0,r)\subseteq \partial \phi(0).
   $$

3. The function has a linear lower bound at the origin:

   $$
   \exists r>0,\qquad \forall \xi\in H,\quad \phi(\xi)\ge r\|\xi\|.
   $$

4. Every vector in some ball around $0$ is a subgradient at $0$:

   $$
   \exists r>0,\qquad \forall g\in H,\quad \|g\|\le r\ \Longrightarrow\ \forall \xi\in H,\quad
   \langle g,\xi\rangle_{\mathbb R}\le \phi(\xi).
   $$

Thus the declaration says: having the subdifferential at $0$ contain a full neighborhood of $0$, having it contain some open ball, having a linear lower bound $\phi(\xi)\ge r\|\xi\|$, and having a whole ball of subgradients at $0$ are all equivalent. The factors of $1/2$ appearing in the proof are radius adjustments between the open-ball and closed-ball/linear-bound formulations.

## Lean proof
```lean
by
  constructor
  · constructor
    · intro h
      rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h) with ⟨r, hr, hball⟩
      exact ⟨r, hr, hball⟩
    · rintro ⟨r, hr, hball⟩
      exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, hball⟩)
  constructor
  · constructor
    · rintro ⟨R, hR, hball⟩
      exact ⟨R / 2, by linarith, subgradient_ball_implies_linear_lower_bound phi hzero hR hball⟩
    · rintro ⟨R, hR, hco⟩
      exact ⟨R / 2, by linarith, linear_lower_bound_implies_subgradient_ball phi hzero hR hco⟩
  constructor
  · rintro ⟨R, hR, hco⟩
    refine ⟨R / 2, by linarith, ?_⟩
    intro g hg xi
    have hgr : ‖g‖ ≤ R := le_trans hg (by linarith)
    exact le_trans (le_trans (real_inner_le_norm g xi)
      (mul_le_mul_of_nonneg_right hgr (norm_nonneg xi))) (hco xi)
  · rintro ⟨R, hR, hdual⟩
    refine ⟨R / 2, by linarith, ?_⟩
    intro xi
    by_cases hxi : xi = 0
    · simp [hxi, hzero]
    have hnorm : ‖xi‖ ≠ 0 := norm_ne_zero_iff.mpr hxi
    let g : H := (R / 2) • ((‖xi‖)⁻¹ • xi)
    have hg_norm : ‖g‖ ≤ R := by
      dsimp [g]
      rw [norm_smul, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (by linarith), Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg xi)]
      field_simp
      linarith
    have hinner : inner ℝ g xi = (R / 2) * ‖xi‖ := by
      dsimp [g]
      rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [map_inv₀, starRingEnd_apply, star_trivial]
      field_simp
    simpa [hinner] using hdual g hg_norm xi
```

## Proof explanation
The proof is a sequence of splits of the conjunction and of the biconditionals.

The first `constructor` separates the first equivalence

$$
0\in \operatorname{int}(\partial \phi(0))
\iff
\exists r>0,\ B(0,r)\subseteq \partial \phi(0)
$$

from the remaining two equivalences. The next `constructor` splits this first biconditional into its two directions.

For the forward direction $0\in \operatorname{int}(\partial \phi(0))\Rightarrow \exists r>0,\ B(0,r)\subseteq \partial \phi(0)$, the proof applies `mem_interior_iff_mem_nhds`. This is the standard topological fact that

$$
x\in \operatorname{int} S \iff S\in \mathcal N(x),
$$

where $\mathcal N(x)$ is the neighborhood filter at $x$. Thus from $0\in \operatorname{int}(\partial \phi(0))$ we obtain that $\partial \phi(0)$ is a neighborhood of $0$. Then `Metric.mem_nhds_iff` converts this neighborhood statement into the metric-ball statement

$$
\exists r>0,\qquad B(0,r)\subseteq \partial \phi(0).
$$

The `rcases` tactic destructs that existential into a radius $r$, its positivity $0<r$, and the inclusion $B(0,r)\subseteq \partial \phi(0)$. These are exactly the data required for the desired existential.

For the reverse direction, `rintro ⟨r, hr, hball⟩` assumes $r>0$ and $B(0,r)\subseteq \partial \phi(0)$. Then `Metric.mem_nhds_iff.mpr` turns the containment of a metric ball into the statement that $\partial \phi(0)$ is a neighborhood of $0$. Finally `mem_interior_iff_mem_nhds.mpr` converts that neighborhood statement back into $0\in \operatorname{int}(\partial \phi(0))$.

The second part of the proof handles the equivalence

$$
\bigl(\exists r>0,\ B(0,r)\subseteq \partial \phi(0)\bigr)
\iff
\bigl(\exists r>0,\ \forall \xi,\ \phi(\xi)\ge r\|\xi\|\bigr).
$$

The forward implication uses the cited lemma `subgradient_ball_implies_linear_lower_bound`. Its content is: if $\phi(0)=0$, if $R>0$, and if

$$
B(0,R)\subseteq \partial \phi(0),
$$

then

$$
\forall \xi\in H,\qquad \phi(\xi)\ge \frac{R}{2}\|\xi\|.
$$

In the proof, the hypothesis gives some $R>0$ and an inclusion $B(0,R)\subseteq \partial \phi(0)$. Applying the lemma with that $R$ yields a linear lower bound with constant $R/2$. The proof then chooses $R/2$ as the new radius. Since $R>0$, `linarith` proves $0<R/2$. This proves the right-hand side.

The reverse implication uses `linear_lower_bound_implies_subgradient_ball`. Its content is: if $\phi(0)=0$, if $R>0$, and if

$$
\forall \xi\in H,\qquad \phi(\xi)\ge R\|\xi\|,
$$

then

$$
B\!\left(0,\frac R2\right)\subseteq \partial \phi(0).
$$

Thus a linear lower bound with constant $R$ produces an open subgradient ball of radius $R/2$. Again `linarith` supplies the positivity $0<R/2$. This establishes the second equivalence.

The third part handles

$$
\bigl(\exists r>0,\ \forall \xi,\ \phi(\xi)\ge r\|\xi\|\bigr)
\iff
\bigl(\exists r>0,\ \forall g,\ \|g\|\le r \Rightarrow \forall \xi,\ \langle g,\xi\rangle_{\mathbb R}\le \phi(\xi)\bigr).
$$

For the forward implication, assume a linear lower bound with constant $R>0$:

$$
\forall \xi,\qquad \phi(\xi)\ge R\|\xi\|.
$$

The proof chooses the new radius $R/2$. It must show that every $g$ with $\|g\|\le R/2$ is a subgradient at $0$. So it introduces `g`, a hypothesis `hg : ‖g‖ ≤ R/2`, and `xi`.

First it proves $\|g\|\le R$. Since $\|g\|\le R/2$ and $R/2\le R$, `le_trans` and `linarith` give $\|g\|\le R$.

Next it uses `real_inner_le_norm`, which is the real Cauchy–Schwarz upper bound:

$$
\langle g,\xi\rangle_{\mathbb R}\le \|g\|\|\xi\|.
$$

Then it multiplies $\|g\|\le R$ by the nonnegative quantity $\|\xi\|$. The lemma `mul_le_mul_of_nonneg_right` gives

$$
\|g\|\|\xi\|\le R\|\xi\|.
$$

The assumed linear lower bound gives

$$
R\|\xi\|\le \phi(\xi).
$$

Chaining these inequalities with `le_trans` gives

$$
\langle g,\xi\rangle_{\mathbb R}\le \phi(\xi).
$$

Thus every vector $g$ with $\|g\|\le R/2$ is a subgradient at $0$, which is the desired dual ball condition with radius $R/2$.

For the reverse implication, assume the dual ball condition with some $R>0$:

$$
\forall g,\quad \|g\|\le R\ \Longrightarrow\ \forall \xi,\quad
\langle g,\xi\rangle_{\mathbb R}\le \phi(\xi).
$$

The proof chooses the new linear-lower-bound constant $R/2$. It must show

$$
\forall \xi,\qquad \phi(\xi)\ge \frac{R}{2}\|\xi\|.
$$

So it introduces an arbitrary $\xi$.

The proof splits on whether $\xi=0$. If $\xi=0$, then `simp [hxi, hzero]` rewrites $\xi$ to $0$ and uses $\phi(0)=0$ to reduce the goal to the trivial inequality

$$
0\ge \frac{R}{2}\cdot 0.
$$

If $\xi\neq0$, then `norm_ne_zero_iff.mpr hxi` gives

$$
\|\xi\|\neq0.
$$

The proof defines

$$
g := \frac R2 \cdot \bigl(\|\xi\|^{-1}\cdot \xi\bigr).
$$

This vector points in the direction of $\xi$ and has norm $R/2$.

First it proves $\|g\|\le R$. It unfolds the definition of $g$, rewrites the norm of a scalar multiple using `norm_smul` twice, converts real norms to absolute values using `Real.norm_eq_abs`, uses positivity of $R/2$, uses `abs_inv`, and uses nonnegativity of $\|\xi\|$. After `field_simp` clears the denominator $\|\xi\|$, using $\|\xi\|\neq0$, the inequality reduces to a linear fact about $R$, which `linarith` proves.

Next it proves the inner product identity

$$
\langle g,\xi\rangle_{\mathbb R}= \frac R2\,\|\xi\|.
$$

It unfolds $g$, applies `inner_smul_left` twice to pull out the two scalar factors, and applies `real_inner_self_eq_norm_sq`, which states

$$
\langle \xi,\xi\rangle_{\mathbb R}= \|\xi\|^2.
$$

After simplifying the real scalar conjugation and clearing the denominator $\|\xi\|$, `field_simp` yields the identity.

Finally, the assumed dual condition applied to this particular $g$, with $\|g\|\le R$, gives

$$
\langle g,\xi\rangle_{\mathbb R}\le \phi(\xi).
$$

Using the identity $\langle g,\xi\rangle_{\mathbb R}=(R/2)\|\xi\|$, `simpa [hinner]` rewrites the left-hand side and obtains

$$
\frac R2\|\xi\|\le \phi(\xi),
$$

which is exactly

$$
\phi(\xi)\ge \frac R2\|\xi\|.
$$

This completes the reverse implication and hence the third equivalence.

Therefore the conjunction of the three biconditionals is proved, establishing that the four formulations of the dry-friction/subgradient condition are equivalent under the stated normalization $\phi(0)=0$.

