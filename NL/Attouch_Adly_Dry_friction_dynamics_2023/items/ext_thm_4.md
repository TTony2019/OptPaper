## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_thm_4.lean`

## Lean statement
```lean
theorem classical_gradient_flow_value_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ : ℝ} (f : H → ℝ) (y dy : ℝ → H) (fstar : ℝ)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (hregular : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hflow : ∀ s ∈ Set.Ici s₀, dy s + gradient f (y s) = 0)
    (hmin : ∃ xstar, f xstar = fstar ∧ ∀ x, fstar ≤ f x) :
    Filter.Tendsto (fun s : ℝ => s * (f (y s) - fstar)) Filter.atTop (nhds 0)
```

## Statement explanation
Theorem statement:

Let `H` be a type, assumed to be a normed additive commutative group and an inner product space over `ℝ`, and additionally complete. Let `s₀ : ℝ` be a real number. Let `f : H → ℝ`, `y dy : ℝ → H`, and `fstar : ℝ` be given. Assume:

- `hconvex : ConvexOn ℝ Set.univ f`: `f` is convex on the whole space `H`.
- `hdiff : Differentiable ℝ f`: `f` is differentiable (over `ℝ`) everywhere.
- `hregular : ∀ s, s ∈ Set.Ici s₀ → HasDerivAt y (dy s) s`: for every real `s ≥ s₀`, the function `y` is differentiable at `s` with derivative `dy s`.
- `hflow : ∀ s, s ∈ Set.Ici s₀ → dy s + gradient f (y s) = 0`: for every `s ≥ s₀`, the derivative of `y` plus the gradient of `f` at `y s` equals zero, i.e. `dy s = -gradient f (y s)`.
- `hmin : ∃ xstar, f xstar = fstar ∧ ∀ x, fstar ≤ f x`: there exists a point `xstar` attaining value `fstar`, which is a global minimum of `f` over all of `H`.

Conclusion:

`Filter.Tendsto (fun s : ℝ => s * (f (y s) - fstar)) Filter.atTop (nhds 0)`: as `s` tends to `+∞`, the quantity `s * (f (y s) - fstar)` tends to `0`.

Equivalently, along the gradient-flow trajectory `y`, the product of the independent variable `s` and the excess of the value `f(y s)` over the minimum value `fstar` tends to zero at infinity.

## Lean proof
```lean
by
  have hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (gradient f x) v := by
    intro x v
    rw [(hdiff x).hasGradientAt.hasFDerivAt.fderiv]
    rfl
  rcases hmin with ⟨xstar, hxstar, hmin_le⟩
  let gap : ℝ → ℝ := fun s => f (y s) - fstar
  let dist2 : ℝ → ℝ := fun s => ‖y s - xstar‖ ^ 2
  have hgap_nonneg (s : ℝ) : 0 ≤ gap s := by
    dsimp [gap]
    linarith [hmin_le (y s)]
  have hgap_deriv (s : ℝ) (hs : s ∈ Set.Ici s₀) :
      HasDerivAt gap (inner ℝ (gradient f (y s)) (dy s)) s := by
    have hcomp := hdiff.differentiableAt.hasFDerivAt.comp_hasDerivAt s (hregular s hs)
    simpa [gap, Function.comp_def, hgradient] using hcomp.sub_const fstar
  have hgap_anti : AntitoneOn gap (Set.Ici s₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici s₀)
    · intro s hs
      exact (hgap_deriv s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hgap_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Set.Ici s₀ := interior_subset hs
      rw [(hgap_deriv s hs').deriv]
      have hdy : dy s = -gradient f (y s) := eq_neg_of_add_eq_zero_left (hflow s hs')
      rw [hdy, inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_nonpos.mpr (sq_nonneg _)
  have hdist_deriv (s : ℝ) (hs : s ∈ Set.Ici s₀) :
      HasDerivAt dist2 (2 * inner ℝ (y s - xstar) (dy s)) s := by
    simpa [dist2] using ((hregular s hs).sub_const xstar).norm_sq
  have hdist_bound (s : ℝ) (hs : s ∈ Set.Ici s₀) :
      deriv dist2 s ≤ -2 * gap s := by
    have hsupport := convex_gradient_support f fstar hconvex hdiff hxstar
      (x := y s)
    have hdy : dy s = -gradient f (y s) := eq_neg_of_add_eq_zero_left (hflow s hs)
    rw [(hdist_deriv s hs).deriv, hdy, inner_neg_right, real_inner_comm]
    dsimp [gap] at hsupport ⊢
    nlinarith
  have hdist_anti : AntitoneOn dist2 (Set.Ici s₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici s₀)
    · intro s hs
      exact (hdist_deriv s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hdist_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Set.Ici s₀ := interior_subset hs
      exact (hdist_bound s hs').trans (by nlinarith [hgap_nonneg s])
  have hhalf_bound (t : ℝ) (ht0 : 0 ≤ t) (ht : 2 * s₀ ≤ t) :
      t * gap t ≤ dist2 (t / 2) - dist2 t := by
    have hhalf : s₀ ≤ t / 2 := by linarith
    have hq_anti : AntitoneOn (fun r : ℝ => dist2 r + 2 * gap t * r) (Set.Icc (t / 2) t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro r hr
        have hr' : r ∈ Set.Ici s₀ := hhalf.trans hr.1
        have hq_deriv : HasDerivAt (fun u : ℝ => dist2 u + 2 * gap t * u)
            (2 * inner ℝ (y r - xstar) (dy r) + 2 * gap t) r := by
          convert (hdist_deriv r hr').add ((hasDerivAt_id r).const_mul (2 * gap t)) using 1
          all_goals ring_nf
        exact hq_deriv.continuousAt.continuousWithinAt
      · intro r hr
        have hrIcc : r ∈ Set.Icc (t / 2) t := interior_subset hr
        have hr' : r ∈ Set.Ici s₀ := hhalf.trans hrIcc.1
        have hq_deriv : HasDerivAt (fun u : ℝ => dist2 u + 2 * gap t * u)
            (2 * inner ℝ (y r - xstar) (dy r) + 2 * gap t) r := by
          convert (hdist_deriv r hr').add ((hasDerivAt_id r).const_mul (2 * gap t)) using 1
          all_goals ring_nf
        exact hq_deriv.differentiableAt.differentiableWithinAt
      · intro r hr
        have hrIcc : r ∈ Set.Icc (t / 2) t := interior_subset hr
        have hr' : r ∈ Set.Ici s₀ := hhalf.trans hrIcc.1
        have ht' : t ∈ Set.Ici s₀ := hhalf.trans (by linarith)
        have hgap_le : gap t ≤ gap r := hgap_anti hr' ht' hrIcc.2
        have hq_deriv : HasDerivAt (fun u : ℝ => dist2 u + 2 * gap t * u)
            (2 * inner ℝ (y r - xstar) (dy r) + 2 * gap t) r := by
          convert (hdist_deriv r hr').add ((hasDerivAt_id r).const_mul (2 * gap t)) using 1
          all_goals ring_nf
        rw [hq_deriv.deriv]
        have hderiv_eq : deriv dist2 r = 2 * inner ℝ (y r - xstar) (dy r) :=
          (hdist_deriv r hr').deriv
        nlinarith [hdist_bound r hr']
    have hleft : t / 2 ∈ Set.Icc (t / 2) t := ⟨le_rfl, by linarith⟩
    have hright : t ∈ Set.Icc (t / 2) t := ⟨by linarith, le_rfl⟩
    have hq := hq_anti hleft hright (by linarith)
    dsimp at hq
    nlinarith
  let D : ℝ → ℝ := fun r => dist2 (max r s₀)
  have hD_nonneg (r : ℝ) : 0 ≤ D r := by
    dsimp [D, dist2]
    exact sq_nonneg _
  have hD_anti : Antitone D := by
    intro a b hab
    apply hdist_anti
    · show s₀ ≤ max a s₀
      exact le_max_right _ _
    · show s₀ ≤ max b s₀
      exact le_max_right _ _
    · exact max_le_max_right s₀ hab
  have hD_bdd : BddBelow (Set.range D) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact hD_nonneg r
  have hD_lim : Filter.Tendsto D Filter.atTop (nhds (sInf (Set.range D))) :=
    tendsto_atTop_ciInf hD_anti hD_bdd
  have hhalf_top : Filter.Tendsto (fun t : ℝ => t / 2) Filter.atTop Filter.atTop := by
    exact (Filter.tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr Filter.tendsto_id
  have hdist_lim : Filter.Tendsto dist2 Filter.atTop (nhds (sInf (Set.range D))) := by
    apply hD_lim.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨s₀, fun t ht => ht⟩] with t ht
    simp [D, max_eq_left ht]
  have hdist_half_lim : Filter.Tendsto (fun t : ℝ => dist2 (t / 2)) Filter.atTop
      (nhds (sInf (Set.range D))) := by
    apply (hD_lim.comp hhalf_top).congr'
    filter_upwards [hhalf_top.eventually (Filter.eventually_atTop.2 ⟨s₀, fun t ht => ht⟩)] with t ht
    simp [D, max_eq_left ht]
  have hdrop_lim : Filter.Tendsto (fun t : ℝ => dist2 (t / 2) - dist2 t) Filter.atTop (nhds 0) := by
    simpa using hdist_half_lim.sub hdist_lim
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_atTop.2 ⟨(0 : ℝ), fun t ht => ht⟩] with t ht
    exact mul_nonneg ht (hgap_nonneg t)
  · filter_upwards [Filter.eventually_atTop.2 ⟨max 0 (2 * s₀), fun t ht => ht⟩] with t ht
    exact hhalf_bound t (le_trans (le_max_left _ _) ht) (le_trans (le_max_right _ _) ht)
  · simpa [gap] using hdrop_lim
```

## Proof explanation
The proof first prepares several facts about derivatives, monotonicity, and limits, then uses a squeeze argument.

1. Define the gradient property.  
   `hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (gradient f x) v`.  
   This says that the Fréchet derivative of `f` at `x`, applied to `v`, equals the inner product of the gradient with `v`. The proof fixes `x` and `v` with `intro`, uses `hgradient` on `fderiv` by rewriting with the `fderiv` of the `HasGradientAt` statement obtained from differentiability of `f`, and then `rfl`.

2. Extract the minimizer.  
   `rcases hmin with ⟨xstar, hxstar, hmin_le⟩` splits the existential into a point `xstar`, the equality `f xstar = fstar`, and the universal lower bound `∀ x, fstar ≤ f x`.

3. Define two auxiliary functions:  
   `gap s = f (y s) - fstar` and `dist2 s = ‖y s - xstar‖^2`.  
   These represent the gap to the minimum value and the squared distance from the trajectory to the minimizer.

4. Prove `hgap_nonneg`: `0 ≤ gap s` for all real `s`.  
   This follows by unfolding `gap` and applying `hmin_le (y s)` plus linear arithmetic (`linarith`).

5. Prove `hgap_deriv`: on `s ≥ s₀`, `gap` has derivative `inner ℝ (gradient f (y s)) (dy s)`.  
   The derivative of `f ∘ y` is obtained by composing the derivative of `f` with the derivative of `y`: `differentiableAt.hasFDerivAt.comp_hasDerivAt`. Then one subtracts the constant `fstar`, giving the derivative as the fderiv of `f` applied to `dy s`; rewriting with `hgradient` converts this to the inner product with the gradient.

6. Prove `hgap_anti`: `gap` is antitone on `[s₀, ∞)`, meaning `r ≤ s` implies `gap r ≥ gap s` there.  
   The proof applies `antitoneOn_of_deriv_nonpos` to the interval `Set.Ici s₀`, which is convex. This lemma requires three things:
   - continuity of `gap` on the interval: obtained from the derivative statement via `continuousAt.continuousWithinAt`;
   - differentiability within the interval: from the derivative statement;
   - nonpositivity of the derivative inside the interval:  
     It rewrites the derivative to `inner (gradient f (y s)) (dy s)`. Using `hflow`, one gets `dy s = -gradient f (y s)`. Then `rw [hdy, inner_neg_right, real_inner_self_eq_norm_sq]` transforms the derivative to `-‖gradient f (y s)‖^2`, which is nonpositive because the square is nonnegative. Thus the gap decreases.

7. Prove `hdist_deriv`: `dist2` has derivative `2 * inner ℝ (y s - xstar) (dy s)` on `s ≥ s₀`.  
   Since `dist2 s = ‖y s - xstar‖^2`, this follows from the derivative of `y` via `(hregular s hs).sub_const xstar` and the derivative of the squared norm, using `norm_sq`.

8. Prove `hdist_bound`: for `s ≥ s₀`,  
   `deriv dist2 s ≤ -2 * gap s`.  
   The proof uses a support inequality: convexity and differentiability imply that for every point `x`, `f xstar + inner (gradient f x) (x - xstar) ≤ f x`. In code this is called `hsupport := convex_gradient_support f fstar hconvex hdiff hxstar (x := y s)`.  
   Using `hflow`, rewrite `dy s = -gradient f (y s)`, so the derivative of `dist2` becomes  
   `2 * inner (y s - xstar) (dy s) = -2 * inner (y s - xstar) (gradient f (y s))`.  
   By symmetry of the real inner product and the support inequality, this is at most `-2 * (f (y s) - fstar) = -2 * gap s`. The nonlinear arithmetic tactic `nlinarith` handles the rearrangement and uses the support inequality.

9. Prove `hdist_anti`: `dist2` is antitone on `[s₀, ∞)`.  
   Similar to `hgap_anti`, using `antitoneOn_of_deriv_nonpos`. The derivative is nonpositive because of `hdist_bound` and because `gap s ≥ 0`. The last condition is handled by `nlinarith [hgap_nonneg s]` after rewriting the derivative.

10. Prove `hhalf_bound`: for `t ≥ 0` and `2 * s₀ ≤ t`,  
    `t * gap t ≤ dist2 (t / 2) - dist2 t`.  
    This is the key quantitative estimate. It defines an auxiliary affine combination  
    `q(r) = dist2 r + 2 * gap t * r` on the interval `[t / 2, t]`.  
    On this interval, `q` is antitone:
    - Its derivative is `2 * inner (y r - xstar) (dy r) + 2 * gap t`, obtained by adding the derivative of `dist2` and the derivative of `2 * gap t * r`.
    - For `r` in this interval, one has `r ≥ s₀` since `s₀ ≤ t/2 ≤ r`. Also `t ≥ r`, so by antitone monotonicity of `gap`, `gap t ≤ gap r`.
    - Using `hdist_bound r`, the derivative of `q` is at most  
      `-2 * gap r + 2 * gap t ≤ 0`, since `gap t ≤ gap r`.  
      The nonlinear arithmetic `nlinarith` proves this.
    Since `q` is antitone on `[t/2, t]`, applying it to the endpoints `t/2 ≤ t` gives  
    `q(t) ≤ q(t/2)`.  
    Expanding `q` and rearranging with `nlinarith` yields exactly  
    `dist2 (t/2) - dist2 t ≥ t * gap t` because the `2 * gap t * t` terms cancel after algebraic manipulation.

11. Define `D r = dist2 (max r s₀)`.  
    This truncates the argument at `s₀` from below, so the domain can start at `s₀`.

12. Show `D` is nonnegative, antitone, and bounded below.  
    - `hD_nonneg`: `0 ≤ D r` because it is a squared norm.
    - `hD_anti`: if `a ≤ b`, then `max a s₀ ≤ max b s₀`, and by `hdist_anti` applied on `[s₀, ∞)`, `D a ≥ D b`.
    - `hD_bdd`: `Set.range D` is bounded below by `0`.

13. Since `D` is antitone and bounded below, its limit at `+∞` is the infimum:  
    `hD_lim : Tendsto D atTop (nhds (sInf (Set.range D)))`, using `tendsto_atTop_ciInf hD_anti hD_bdd`.

14. Relate this limit to `dist2`.  
    For `t → +∞`, eventually `t ≥ s₀`, so `max t s₀ = t`. Therefore `D t = dist2 t` eventually, hence  
    `hdist_lim : Tendsto dist2 atTop (nhds (sInf (Set.range D)))`.  
    Similarly, since `t / 2 → +∞`, eventually `t / 2 ≥ s₀`, so `D (t / 2) = dist2 (t / 2)`, giving  
    `hdist_half_lim : Tendsto (fun t => dist2 (t / 2)) atTop (nhds (sInf (Set.range D)))`.

15. Subtract these two limits:  
    `hdrop_lim : Tendsto (fun t => dist2 (t / 2) - dist2 t) atTop (nhds 0)`.  
    Since both sequences converge to the same constant, their difference tends to `0`.

16. Conclude with a squeeze theorem.  
    The goal is to show `s * gap s → 0` as `s → +∞`. The proof uses `squeeze_zero'`, which requires:
    - a lower bound eventually nonnegative: `0 ≤ t * gap t`, since `t ≥ 0` eventually and `hgap_nonneg t`;
    - an upper bound eventually: `t * gap t ≤ dist2 (t / 2) - dist2 t`, from `hhalf_bound` applied after choosing `t` large enough so that `t ≥ 0` and `t ≥ 2 * s₀`;
    - convergence of the upper bound to zero: `(dist2 (t / 2) - dist2 t) → 0`, from `hdrop_lim`.

    The `filter_upwards` commands specify the eventual conditions. The final `simpa [gap] using hdrop_lim` converts the expression in the squeeze statement to the function whose limit is zero. Therefore `t * (f (y t) - fstar) → 0`, which is the desired conclusion.

