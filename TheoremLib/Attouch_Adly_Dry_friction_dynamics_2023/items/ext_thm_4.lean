import Mathlib

namespace AttouchAdlyDryFrictionDynamics2023

private theorem convex_gradient_support {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (fstar : ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    {x xstar : H} (hxstar : f xstar = fstar) :
    f x - fstar ≤ inner ℝ (gradient f x) (x - xstar) := by
  have hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (gradient f x) v := by
    intro x v
    rw [(hdiff x).hasGradientAt.hasFDerivAt.fderiv]
    rfl
  let g : ℝ → ℝ := fun t => f (x + t • (xstar - x))
  have hconv_g : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun p hp q hq a b ha hb hab => ?_⟩
    dsimp [g]
    have hident : x + ((a * p + b * q) • (xstar - x)) =
        a • (x + p • (xstar - x)) + b • (x + q • (xstar - x)) := by
      calc
        x + ((a * p + b * q) • (xstar - x)) =
            (a + b) • x + ((a * p + b * q) • (xstar - x)) := by simp [hab]
        _ = (a • x + b • x) + ((a * p) • (xstar - x) + (b * q) • (xstar - x)) := by
          simp [add_smul, mul_smul]
        _ = a • (x + p • (xstar - x)) + b • (x + q • (xstar - x)) := by module
    rw [hident]
    exact hconvex.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hderiv : HasDerivAt g (inner ℝ (gradient f x) (xstar - x)) 0 := by
    have hline : HasLineDerivAt ℝ f (inner ℝ (gradient f x) (xstar - x)) x (xstar - x) := by
      simpa [hgradient] using
        hdiff.differentiableAt.hasFDerivAt.hasLineDerivAt (xstar - x)
    simpa [g, HasLineDerivAt] using hline
  have hslope : inner ℝ (gradient f x) (xstar - x) ≤ g 1 - g 0 := by
    have h := ConvexOn.le_slope_of_hasDerivAt hconv_g (Set.mem_univ 0) (Set.mem_univ 1)
      (by norm_num : (0 : ℝ) < 1) hderiv
    simpa [slope, div_one] using h
  have hvals : g 1 = f xstar ∧ g 0 = f x := by simp [g]
  rw [hvals.1, hvals.2, hxstar] at hslope
  rw [← neg_sub, inner_neg_right] at hslope
  linarith

/- EXTERNAL DEPENDENCY: Classical gradient-flow value rate
   Source: Unspecified classical gradient-flow convergence result
   Status: proof supplied by the cited classical result.
-/
/-- A classical convex gradient flow has value error `o(1/s)` when its infimum is attained. -/
theorem classical_gradient_flow_value_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ : ℝ} (f : H → ℝ) (y dy : ℝ → H) (fstar : ℝ)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (hregular : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hflow : ∀ s ∈ Set.Ici s₀, dy s + gradient f (y s) = 0)
    (hmin : ∃ xstar, f xstar = fstar ∧ ∀ x, fstar ≤ f x) :
    Filter.Tendsto (fun s : ℝ => s * (f (y s) - fstar)) Filter.atTop (nhds 0) := by
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

end AttouchAdlyDryFrictionDynamics2023
