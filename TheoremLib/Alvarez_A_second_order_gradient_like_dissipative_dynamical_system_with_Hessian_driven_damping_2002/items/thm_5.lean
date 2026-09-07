import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_thm_4
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_8

namespace Alvarez2002

open Filter

-- def IsSolution_gDIN {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
--  [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (β a b : ℝ) (x₀ y₀ : H)
--  (x y : ℝ → H) :=
--  (∀ t, 0 ≤ t → deriv x t + β • gradient Φ (x t) + a • x t + b • y t = 0) ∧
--  (∀ t, 0 ≤ t → deriv y t + a • x t + b • y t = 0) ∧
--  (x 0 = x₀) ∧ (y 0 = y₀) ∧
--  ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0) ∧
--  (∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t) ∧
--  (∀ t, 0 ≤ t → HasDerivAt y (deriv y t) t)

def LipschitzOnBoundedSets {H : Type*} [NormedAddCommGroup H]
    (f : H → H) : Prop := ∀ s : Set H, Bornology.IsBounded s →
      ∃ K : NNReal, LipschitzOnWith K f s

def SameTrajectoryOnNonnegative {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (x1 y1 x2 y2 : ℝ → H) : Prop :=
  ∀ t, 0 ≤ t → (x1 t = x2 t ∧ y1 t = y2 t)

noncomputable def LyapunovEnergy {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : H → ℝ) (a b ell : ℝ) (x y : H) : ℝ :=
  ell * Φ x + (1 / 2) * ‖a • x + b • y‖ ^ 2

def MemL2OnNonnegative {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) : Prop :=
  MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))

def BoundedOnNonnegative {H : Type*} [NormedAddCommGroup H]
    (f : ℝ → H) : Prop := Bornology.IsBounded (f '' Set.Ici (0 : ℝ))

open scoped Topology

private theorem gdin_grad_lipschitzOnBounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gradΦ : H → H)
    (hloclip : ∀ R : ℝ, ∃ L : ℝ, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖gradΦ x - gradΦ y‖ ≤ L * ‖x - y‖) :
    LipschitzOnBoundedSets gradΦ := by
  intro s hs
  rcases (isBounded_iff_forall_norm_le.1 hs) with ⟨R, hR⟩
  let R' : ℝ := max R 0
  rcases hloclip R' with ⟨L, hL⟩
  let K : NNReal := ⟨max L 0, le_max_right L 0⟩
  refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxR : ‖x‖ ≤ R' := (hR x hx).trans (le_max_left _ _)
  have hyR : ‖y‖ ≤ R' := (hR y hy).trans (le_max_left _ _)
  have hxy := hL x y hxR hyR
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    hxy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

private theorem gdin_phi_contDiff_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → ℝ) (gradΦ : H → H)
    (hgradΦ : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradΦ z)) z)
    (hgrad_lip : LipschitzOnBoundedSets gradΦ) :
    ContDiff ℝ 1 Φ := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun z => innerSL ℝ (gradΦ z), ?_, hgradΦ⟩
  have hlocal : LocallyLipschitz gradΦ := by
    intro z
    rcases hgrad_lip (Metric.closedBall z 1) Metric.isBounded_closedBall with ⟨K, hK⟩
    exact ⟨K, Metric.closedBall z 1, Metric.closedBall_mem_nhds z zero_lt_one, hK⟩
  exact (InnerProductSpace.toDualMap ℝ H).continuous.comp hlocal.continuous

private theorem gdin_to_aabr_solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∃ sys : AlvarezAttouchBolteRedont.NonnegativeDissipativeSystem H (gradient Φ) β a b x₀ y₀,
      sys.x = x ∧ sys.y = y ∧ sys.xdot = deriv x ∧ sys.ydot = deriv y ∧
        AlvarezAttouchBolteRedont.IsSolutionOnNonnegative sys := by
  rcases hsol with ⟨hx, hy, hx₀, hy₀⟩
  rcases hxy with ⟨hcx, hcy⟩
  let sys : AlvarezAttouchBolteRedont.NonnegativeDissipativeSystem H (gradient Φ) β a b x₀ y₀ :=
    { x := x
      y := y
      xdot := deriv x
      ydot := deriv y
      beta_pos := hβ
      b_pos := hb
      a_add_b_pos := hab
      initial_x := hx₀
      initial_y := hy₀
      equation_x := hx
      equation_y := hy }
  have hdx : ∀ t : ℝ, 0 < t → HasDerivAt x (deriv x t) t := by
    intro t ht
    have hwithin : DifferentiableWithinAt ℝ x (Set.Ici 0) t :=
      hcx.differentiableOn (by norm_num) t ht.le
    exact (hwithin.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
  have hdy : ∀ t : ℝ, 0 < t → HasDerivAt y (deriv y t) t := by
    intro t ht
    have hwithin : DifferentiableWithinAt ℝ y (Set.Ici 0) t :=
      hcy.differentiableOn (by norm_num) t ht.le
    exact (hwithin.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
  refine ⟨sys, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨hcx, hcy⟩,
    ⟨hcx.continuousOn, hcy.continuousOn⟩⟩
  · intro t ht
    exact hdx t ht
  · intro t ht
    exact hdy t ht

private theorem aabr_to_gdin_solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (x₀ y₀ : H)
    (sys : AlvarezAttouchBolteRedont.NonnegativeDissipativeSystem H (gradient Φ) β a b x₀ y₀)
    (hsol : AlvarezAttouchBolteRedont.IsSolutionOnNonnegative sys) :
    IsSolution_gDIN Φ β a b x₀ y₀ sys.x sys.y := by
  have hdx0 : HasDerivAt sys.x (sys.xdot 0) 0 := by
    -- `IsSolutionOnNonnegative` only records interior derivatives; endpoint
    -- differentiability needs an additional hypothesis beyond `ContDiffOn (Ici 0)`.
    sorry
  have hdy0 : HasDerivAt sys.y (sys.ydot 0) 0 := by
    -- The same one-sided-versus-two-sided issue occurs for the y trajectory.
    sorry
  refine ⟨?_, ?_, sys.initial_x, sys.initial_y⟩
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hdx0.deriv]
      exact sys.equation_x 0 le_rfl
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hder := hsol.1.1 t htpos
      rw [hder.deriv]
      exact sys.equation_x t ht
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hdy0.deriv]
      exact sys.equation_y 0 le_rfl
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hder := hsol.1.2 t htpos
      rw [hder.deriv]
      exact sys.equation_y t ht

private theorem gdin_midpoint_bounds (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hab : 0 < a + b) :
    β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ β * (a + 2 * b) ∧
      β * (a + 2 * b) ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
  have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
  have ht : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hnonneg : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  constructor <;> nlinarith

theorem alvarez_attouch_bolte_redont_theorem_1_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b) :
    ∀ x₀ y₀, (∃ x y : ℝ → H, IsSolution_gDIN Φ β a b x₀ y₀ x y ∧ ContDiffOn ℝ 1 x (Set.Ici 0) ∧
    ContDiffOn ℝ 2 y (Set.Ici 0) ∧
    (∀ x' : ℝ → H, ∀ y' : ℝ → H, IsSolution_gDIN Φ β a b x₀ y₀ x' y' →
    (ContDiffOn ℝ 1 x' (Set.Ici 0) ∧ ContDiffOn ℝ 2 y' (Set.Ici 0)) →
    SameTrajectoryOnNonnegative x y x' y')) := by
  have hgrad_lip := hloclip
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hgrad_lip hβ hb hab
  intro x₀ y₀
  rcases hmain.1 x₀ y₀ with ⟨sys, hsys, huniq⟩
  have hlocal := aabr_to_gdin_solution Φ β a b x₀ y₀ sys hsys
  refine ⟨sys.x, sys.y, hlocal, hsys.2.1.1, hsys.2.1.2, ?_⟩
  intro x' y' hsol'
  intro hxy'
  obtain ⟨sys', hsx, hsy, hsxdot, hsydot, hsys'⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x' y' hxy' hsol'
  have hsame := huniq sys' hsys'
  intro t ht
  have h := hsame t ht
  exact ⟨by simpa [hsx] using h.1.symm,
    by simpa [hsy] using h.2.1.symm⟩

/-- The Lyapunov energy conclusions in part (ii) of Theorem 6.2. -/
theorem gdin_lyapunov_energy_properties
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∀ ell : ℝ,
      β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell →
      ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 →
        AntitoneOn (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) (Set.Ici 0) ∧
        (∃ m : ℝ, ∀ t : ℝ, 0 ≤ t → m ≤ LyapunovEnergy Φ a b ell (x t) (y t)) ∧
        ∃ l : ℝ, Tendsto (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) atTop (nhds l) := by
  have hgrad_lip := hloclip
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hgrad_lip hβ hb hab
  obtain ⟨sys, hsx, hsy, hsxdot, hsydot, hsys⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x y hxy hsol
  intro ell hell_low hell_high
  have h := hmain.2.1 x₀ y₀ sys hsys ell hell_low hell_high
  rcases h with ⟨hanti, hlower, hlim, hxdot_l2, hphi_lim, hydot_l2, hydot_lim⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [LyapunovEnergy, AlvarezAttouchBolteRedont.LyapunovEnergy, hsx, hsy] using hanti
  · simpa [LyapunovEnergy, AlvarezAttouchBolteRedont.LyapunovEnergy, hsx, hsy] using hlower
  · simpa [LyapunovEnergy, AlvarezAttouchBolteRedont.LyapunovEnergy, hsx, hsy] using hlim

/-- The L2 conclusion for the x derivative in part (ii) of Theorem 6.2. -/
theorem gdin_x_derivative_memL2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    MemL2OnNonnegative (deriv x) := by
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hloclip hβ hb hab
  obtain ⟨sys, hsx, hsy, hsxdot, hsydot, hsys⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x y hxy hsol
  obtain ⟨hlow, hhigh⟩ := gdin_midpoint_bounds β a b hβ hb hab
  have h := hmain.2.1 x₀ y₀ sys hsys (β * (a + 2 * b)) hlow hhigh
  simpa [hsxdot] using h.2.2.2.1

/-- The L2 conclusion for the gradient in part (ii) of Theorem 6.2. -/
theorem gdin_gradient_memL2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    MemL2OnNonnegative (fun t => gradient Φ (x t)) := by
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hloclip hβ hb hab
  obtain ⟨sys, hsx, hsy, hsxdot, hsydot, hsys⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x y hxy hsol
  obtain ⟨hlow, hhigh⟩ := gdin_midpoint_bounds β a b hβ hb hab
  have hmid := hmain.2.1 x₀ y₀ sys hsys (β * (a + 2 * b)) hlow hhigh
  have hsub := hmid.2.2.2.2.2.1.sub hmid.2.2.2.1
  have hscaled := hsub.const_smul (1 / β)
  have heq : (fun t => gradient Φ (sys.x t)) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))]
      fun t => (1 / β) • (sys.ydot t - sys.xdot t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have hx := sys.equation_x t ht
    have hy := sys.equation_y t ht
    have hdiff : sys.ydot t - sys.xdot t = β • gradient Φ (sys.x t) := by
      calc
        sys.ydot t - sys.xdot t =
            (sys.ydot t + a • sys.x t + b • sys.y t) -
              (sys.xdot t + β • gradient Φ (sys.x t) + a • sys.x t + b • sys.y t) +
                β • gradient Φ (sys.x t) := by module
        _ = β • gradient Φ (sys.x t) := by rw [hx, hy]; module
    rw [hdiff]
    calc
      gradient Φ (sys.x t) = (1 : ℝ) • gradient Φ (sys.x t) := (one_smul ℝ _).symm
      _ = (1 / β * β) • gradient Φ (sys.x t) := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hβ)]
      _ = (1 / β) • β • gradient Φ (sys.x t) := by rw [smul_smul]
  have hgrad_l2 : AlvarezAttouchBolteRedont.MemL2OnNonnegative
      (fun t => gradient Φ (sys.x t)) := by
    apply hscaled.congr_norm
    · exact hscaled.1.congr heq.symm
    · filter_upwards [heq] with t ht
      rw [ht]
      rfl
  simpa [hsx] using hgrad_l2

/-- The convergence of the potential value in part (ii) of Theorem 6.2. -/
theorem gdin_phi_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := by
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hloclip hβ hb hab
  obtain ⟨sys, hsx, hsy, hsxdot, hsydot, hsys⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x y hxy hsol
  obtain ⟨hlow, hhigh⟩ := gdin_midpoint_bounds β a b hβ hb hab
  have h := hmain.2.1 x₀ y₀ sys hsys (β * (a + 2 * b)) hlow hhigh
  simpa [hsx] using h.2.2.2.2.1

/-- The residual convergence conclusion in part (ii) of Theorem 6.2. -/
theorem gdin_residual_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) := by
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hloclip hβ hb hab
  obtain ⟨sys, hsx, hsy, hsxdot, hsydot, hsys⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x y hxy hsol
  obtain ⟨hlow, hhigh⟩ := gdin_midpoint_bounds β a b hβ hb hab
  have hmid := hmain.2.1 x₀ y₀ sys hsys (β * (a + 2 * b)) hlow hhigh
  have hrel : ∀ᶠ t in atTop,
      deriv x t + β • gradient Φ (x t) = sys.ydot t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hx := sys.equation_x t ht
    have hy := sys.equation_y t ht
    rw [← hsxdot, ← hsx]
    calc
      sys.xdot t + β • gradient Φ (sys.x t) =
          (sys.xdot t + β • gradient Φ (sys.x t) + a • sys.x t + b • sys.y t) -
            (sys.ydot t + a • sys.x t + b • sys.y t) + sys.ydot t := by module
      _ = sys.ydot t := by rw [hx, hy]; module
  apply hmid.2.2.2.2.2.2.congr'
  filter_upwards [hrel] with t ht
  exact ht.symm

/-- The bounded-trajectory conclusions in part (iii) of Theorem 6.2. -/
theorem gdin_bounded_asymptotics
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y)
    (hxbounded : BoundedOnNonnegative x) :
    BoundedOnNonnegative (deriv x) ∧
      BoundedOnNonnegative (fun t => gradient Φ (x t)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
  have hgrad : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ (gradient Φ) β a b hΦ hgrad hbounded hloclip hβ hb hab
  obtain ⟨sys, hsx, hsy, hsxdot, hsydot, hsys⟩ :=
    gdin_to_aabr_solution Φ β a b hβ hb hab x₀ y₀ x y hxy hsol
  have hxbounded_sys : AlvarezAttouchBolteRedont.BoundedOnNonnegative sys.x := by
    simpa [hsx] using hxbounded
  rcases hmain.2.2 x₀ y₀ sys hsys hxbounded_sys with
    ⟨hgrad_bdd, hxdot_bdd, hxdot_lim, hgrad_lim⟩
  exact ⟨by simpa [hsxdot] using hxdot_bdd,
    by simpa [hsx] using hgrad_bdd,
    by simpa [hsxdot] using hxdot_lim,
    by simpa [hsx] using hgrad_lim⟩

end Alvarez2002
