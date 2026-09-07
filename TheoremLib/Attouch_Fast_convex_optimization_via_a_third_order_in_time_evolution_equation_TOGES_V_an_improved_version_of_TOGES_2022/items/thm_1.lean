import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_2
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_3

open Filter
open MeasureTheory

/-- The TOGES-V change of variables satisfies the rescaled second-order equation. -/
private theorem togesV_auxiliary_equation {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (u uDot uDdot uDddot : ℝ → H) (grad : H → H)
    (alpha t0 : ℝ) (ht0pos : 0 < t0)
    (hTrajectory : ∀ t, t0 ≤ t →
      uDddot t + ((alpha + 7) / t) • uDdot t +
        (5 * (alpha + 1) / t ^ 2) • uDot t +
        grad (u t + (t / 4) • uDot t) = 0) :
    ∀ t, t0 ≤ t →
      let v : ℝ → H := fun s => u s + (s / 4) • uDot s
      let vDot : ℝ → H := fun s => (5 / 4 : ℝ) • uDot s + (s / 4) • uDdot s
      let vDdot : ℝ → H := fun s => (3 / 2 : ℝ) • uDdot s + (s / 4) • uDddot s
      vDdot t + ((alpha + 1) / t) • vDot t + (t / 4) • grad (v t) = 0 := by
  intro t ht
  dsimp
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hscaled := congrArg (fun q : H => (t / 4) • q) (hTrajectory t ht)
  simp only [smul_zero, smul_add, smul_smul] at hscaled
  have hacc : (t / 4) * ((alpha + 7) / t) = (alpha + 7) / 4 := by
    field_simp [htne]
  have hvel : (t / 4) * (5 * (alpha + 1) / t ^ 2) =
      5 * (alpha + 1) / (4 * t) := by
    field_simp [htne]
  rw [hacc, hvel] at hscaled
  have hacc' : (3 / 2 : ℝ) + ((alpha + 1) / t) * (t / 4) = (alpha + 7) / 4 := by
    field_simp [htne]
    ring
  have hvel' : ((alpha + 1) / t) * (5 / 4 : ℝ) = 5 * (alpha + 1) / (4 * t) := by
    field_simp [htne]
  calc
    _ = (t / 4) • uDddot t +
        ((3 / 2 : ℝ) + ((alpha + 1) / t) * (t / 4)) • uDdot t +
        (((alpha + 1) / t) * (5 / 4 : ℝ)) • uDot t +
        (t / 4) • grad (u t + (t / 4) • uDot t) := by module
    _ = (t / 4) • uDddot t + ((alpha + 7) / 4) • uDdot t +
        (5 * (alpha + 1) / (4 * t)) • uDot t +
        (t / 4) • grad (u t + (t / 4) • uDot t) := by rw [hacc', hvel']
    _ = 0 := hscaled

/-- The fourth-power primitive used to average the auxiliary trajectory. -/
private theorem togesV_power_four_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (u uDot : ℝ → H) (t0 : ℝ)
    (hu : ∀ s, t0 ≤ s → HasDerivAt u (uDot s) s) :
    ∀ s, t0 ≤ s → HasDerivAt (fun r => r ^ 4 • u r)
      (((4 : ℝ) * s ^ 3) • (u s + (s / 4) • uDot s)) s := by
  intro s hs
  have hraw := ((hasDerivAt_id s).pow 4).smul (hu s hs)
  have hderiv : ((4 : ℝ) * s ^ 3) • u s + s ^ 4 • uDot s =
      ((4 : ℝ) * s ^ 3) • (u s + (s / 4) • uDot s) := by
    rw [smul_add, smul_smul]
    module
  have hraw' : HasDerivAt (fun r => r ^ 4 • u r)
      (((4 : ℝ) * s ^ 3) • u s + s ^ 4 • uDot s) s := by
    convert hraw using 1; simp [id]
    module
  exact hraw'.congr_deriv hderiv

/-- Integral form of the fourth-power barycentric identity. -/
private theorem togesV_power_four_integral {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H] (u uDot : ℝ → H) (t0 t h : ℝ)
    (hu : ∀ s, t0 ≤ s → HasDerivAt u (uDot s) s) (ht : t0 ≤ t) (hh : 0 ≤ h)
    (hInt : IntervalIntegrable
      (fun s => ((4 : ℝ) * s ^ 3) • (u s + (s / 4) • uDot s)) volume t (t + h)) :
    ∫ s in t..t + h, ((4 : ℝ) * s ^ 3) • (u s + (s / 4) • uDot s) =
      (t + h) ^ 4 • u (t + h) - t ^ 4 • u t := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => r ^ 4 • u r)
    (f' := fun s => ((4 : ℝ) * s ^ 3) • (u s + (s / 4) • uDot s))
    (by
      intro s hs
      rw [Set.uIcc_of_le (by linarith : t ≤ t + h)] at hs
      exact togesV_power_four_hasDerivAt u uDot t0 hu s (le_trans ht hs.1)) hInt

/-- Differentiability data for the TOGES-V auxiliary trajectory. -/
theorem togesV_auxiliary_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (u uDot uDdot uDddot : ℝ → H) (t0 : ℝ)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (uDot t) t)
    (huDot : ∀ t, t0 ≤ t → HasDerivAt uDot (uDdot t) t)
    (huDdot : ∀ t, t0 ≤ t → HasDerivAt uDdot (uDddot t) t) :
    let v : ℝ → H := fun s => u s + (s / 4) • uDot s
    let vDot : ℝ → H := fun s => (5 / 4 : ℝ) • uDot s + (s / 4) • uDdot s
    let vDdot : ℝ → H := fun s => (3 / 2 : ℝ) • uDdot s + (s / 4) • uDddot s
    (∀ t, t0 ≤ t → HasDerivAt v (vDot t) t) ∧
      ∀ t, t0 ≤ t → HasDerivAt vDot (vDdot t) t := by
  dsimp
  constructor
  · intro t ht
    have hraw := (hu t ht).add (((hasDerivAt_id t).div_const 4).smul (huDot t ht))
    convert hraw using 1; simp [id]; module
  · intro t ht
    have hraw := ((huDot t ht).const_smul (5 / 4 : ℝ)).add
      (((hasDerivAt_id t).div_const 4).smul (huDdot t ht))
    convert hraw using 1; simp [id]; module

/-- Lyapunov derivative for the TOGES-V auxiliary trajectory. -/
private theorem togesV_auxiliary_energy_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (grad : H → H)
    (v vDot vDdot : ℝ → H) (alpha s : ℝ) (z : H)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hv : HasDerivAt v (vDot s) s)
    (hvDot : HasDerivAt vDot (vDdot s) s) (hspos : 0 < s)
    (hEq : vDdot s + ((alpha + 1) / s) • vDot s +
      (s / 4) • grad (v s) = 0) :
    HasDerivAt
      (fun r => r ^ 3 / 4 * (f (v r) - f z) +
        (1 / 2) * ‖alpha • (v r - z) + r • vDot r‖ ^ 2)
      (s ^ 2 / 4 * (3 * (f (v s) - f z) -
        alpha * inner ℝ (grad (v s)) (v s - z))) s := by
  let p : ℝ → H := fun r => alpha • (v r - z) + r • vDot r
  have hF : HasDerivAt (fun r => f (v r) - f z)
      (inner ℝ (grad (v s)) (vDot s)) s := by
    simpa [innerSL_apply_apply] using
      ((hGradient (v s)).comp_hasDerivAt s hv).sub_const (f z)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hscaled := congrArg (fun q : H => s • q) hEq
  simp only [smul_zero, smul_add, smul_smul] at hscaled
  have hcoef : s * ((alpha + 1) / s) = alpha + 1 := by field_simp [hsne]
  rw [hcoef] at hscaled
  have hpderiv : HasDerivAt p (-(s ^ 2 / 4) • grad (v s)) s := by
    have hraw := ((hv.sub_const z).const_smul alpha).add
      ((hasDerivAt_id s).smul hvDot)
    have hsolve : s • vDdot s = -(alpha + 1) • vDot s -
        (s ^ 2 / 4) • grad (v s) := by
      calc
        s • vDdot s = -((alpha + 1) • vDot s + (s ^ 2 / 4) • grad (v s)) := by
          apply (eq_neg_iff_add_eq_zero).2
          convert hscaled using 1; module
        _ = -(alpha + 1) • vDot s - (s ^ 2 / 4) • grad (v s) := by module
    have hcancel : alpha • vDot s + (s • vDdot s + (1 : ℝ) • vDot s) =
        -(s ^ 2 / 4) • grad (v s) := by
      rw [hsolve]
      module
    simpa [p, id] using hraw.congr_deriv hcancel
  have hraw := (((hasDerivAt_pow 3 s).div_const 4).mul hF).add
    (hpderiv.norm_sq.const_mul (1 / 2 : ℝ))
  have hderiv_eq :
      ((3 * s ^ 2) / 4) * (f (v s) - f z) +
        (s ^ 3 / 4) * inner ℝ (grad (v s)) (vDot s) +
        (1 / 2) * (2 * inner ℝ (p s) (-(s ^ 2 / 4) • grad (v s))) =
      s ^ 2 / 4 * (3 * (f (v s) - f z) -
        alpha * inner ℝ (grad (v s)) (v s - z)) := by
    rw [show p s = alpha • (v s - z) + s • vDot s by rfl]
    rw [inner_add_left]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (grad (v s)) (vDot s),
      real_inner_comm (v s - z) (grad (v s))]
    ring
  simpa [p, pow_succ] using hraw.congr_deriv hderiv_eq

/-- The first-order support inequality supplied by convex differentiability. -/
private theorem togesV_convex_gradient_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (grad : H → H)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x) (x y : H) :
    f x - f y ≤ inner ℝ (grad x) (x - y) := by
  let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y x
  have hline : HasDerivAt line (x - y) 1 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - y)).add_const y using 1
    all_goals simp
  have hphi : ConvexOn ℝ Set.univ (f ∘ line) := by
    simpa [line] using hConvex.comp_affineMap (AffineMap.lineMap y x)
  have hderiv : HasDerivAt (f ∘ line) (inner ℝ (grad x) (x - y)) 1 := by
    have hgradline : HasFDerivAt f (innerSL ℝ (grad x)) (line 1) := by
      simpa [line] using hGradient x
    simpa [innerSL_apply_apply] using hgradline.comp_hasDerivAt 1 hline
  have hslope := hphi.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
    (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hderiv
  simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using hslope

/-- The non-strict value estimate for the TOGES-V auxiliary trajectory. -/
private theorem togesV_auxiliary_bigO {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ)
    (v vDot vDdot : ℝ → H) (grad : H → H) (alpha t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hMin : ∃ z, IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hv : ∀ t, t0 ≤ t → HasDerivAt v (vDot t) t)
    (hvDot : ∀ t, t0 ≤ t → HasDerivAt vDot (vDdot t) t)
    (hEq : ∀ t, t0 ≤ t → vDdot t + ((alpha + 1) / t) • vDot t +
      (t / 4) • grad (v t) = 0) (hAlpha : 3 ≤ alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ≥ t0,
      f (v t) - sInf (Set.range f) ≤ C / t ^ 3 := by
  rcases hMin with ⟨z, hz⟩
  have hzGlobal : ∀ x : H, f z ≤ f x := by
    simpa [IsMinOn, IsMinFilter] using hz
  have hsInf : sInf (Set.range f) = f z := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨f z, fun y hy => by rcases hy with ⟨x, rfl⟩; exact hzGlobal x⟩
      · exact ⟨z, rfl⟩
    · apply le_csInf
      · exact ⟨f z, ⟨z, rfl⟩⟩
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        exact hzGlobal x
  let E : ℝ → ℝ := fun t => t ^ 3 / 4 * (f (v t) - f z) +
    (1 / 2) * ‖alpha • (v t - z) + t • vDot t‖ ^ 2
  have hEderiv : ∀ t, t0 ≤ t → HasDerivAt E
      (t ^ 2 / 4 * (3 * (f (v t) - f z) -
        alpha * inner ℝ (grad (v t)) (v t - z))) t := by
    intro t ht
    exact togesV_auxiliary_energy_hasDerivAt f grad v vDot vDdot alpha t z hGradient
      (hv t ht) (hvDot t ht) (lt_of_lt_of_le ht0pos ht) (hEq t ht)
  have hE_nonpos : ∀ t, t0 ≤ t → deriv E t ≤ 0 := by
    intro t ht
    have hF : 0 ≤ f (v t) - f z := sub_nonneg.mpr (hzGlobal (v t))
    have hsupp := togesV_convex_gradient_le f grad hConvex hGradient (v t) z
    rw [(hEderiv t ht).deriv]
    have hbracket : 3 * (f (v t) - f z) -
        alpha * inner ℝ (grad (v t)) (v t - z) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hbracket
  have hEcont : ContinuousOn E (Set.Ici t0) := fun t ht =>
    (hEderiv t ht).continuousAt.continuousWithinAt
  have hEdiff : DifferentiableOn ℝ E (interior (Set.Ici t0)) := by
    rw [interior_Ici]
    intro t ht
    exact (hEderiv t ht.le).differentiableAt.differentiableWithinAt
  have hEanti := antitoneOn_of_deriv_nonpos (convex_Ici t0) hEcont hEdiff (by
    intro t ht
    have ht' : t0 < t := by simpa using ht
    exact hE_nonpos t ht'.le)
  let C : ℝ := 4 * (E t0 + 1)
  have hCpos : 0 < C := by
    have hEnonneg : 0 ≤ E t0 := by
      dsimp [E]
      have hF : 0 ≤ f (v t0) - f z := sub_nonneg.mpr (hzGlobal (v t0))
      positivity
    dsimp [C]
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro t ht
  have hEt : E t ≤ E t0 := by
    apply hEanti
    · simp
    · exact ht
    · exact ht
  have hkin : 0 ≤ (1 / 2) * ‖alpha • (v t - z) + t • vDot t‖ ^ 2 := by positivity
  have hmul : t ^ 3 * (f (v t) - f z) ≤ C := by
    dsimp [E, C] at hEt ⊢
    nlinarith
  rw [hsInf]
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  exact (le_div_iff₀ (by positivity : 0 < t ^ 3)).2 (by simpa [mul_comm] using hmul)

/-- For a strict damping parameter, the auxiliary Lyapunov energy dissipates
at a rate controlled by the objective gap. -/
private theorem togesV_auxiliary_strict_dissipation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (grad : H → H)
    (v vDot vDdot : ℝ → H) (alpha t0 : ℝ) (z : H)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hzGlobal : ∀ x : H, f z ≤ f x) (ht0pos : 0 < t0)
    (hv : ∀ t, t0 ≤ t → HasDerivAt v (vDot t) t)
    (hvDot : ∀ t, t0 ≤ t → HasDerivAt vDot (vDdot t) t)
    (hEq : ∀ t, t0 ≤ t → vDdot t + ((alpha + 1) / t) • vDot t +
      (t / 4) • grad (v t) = 0) (hAlpha : 3 < alpha) :
    ∀ t, t0 ≤ t →
      deriv (fun r => r ^ 3 / 4 * (f (v r) - f z) +
        (1 / 2) * ‖alpha • (v r - z) + r • vDot r‖ ^ 2) t ≤
        -((alpha - 3) / 4) * t ^ 2 * (f (v t) - f z) := by
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  have hF : 0 ≤ f (v t) - f z := sub_nonneg.mpr (hzGlobal (v t))
  have hsupp := togesV_convex_gradient_le f grad hConvex hGradient (v t) z
  have hbracket :
      3 * (f (v t) - f z) - alpha * inner ℝ (grad (v t)) (v t - z) ≤
        -(alpha - 3) * (f (v t) - f z) := by
    nlinarith
  rw [(togesV_auxiliary_energy_hasDerivAt f grad v vDot vDdot alpha t z hGradient
    (hv t ht) (hvDot t ht) htpos (hEq t ht)).deriv]
  have hscale : 0 ≤ t ^ 2 / 4 := by positivity
  have := mul_le_mul_of_nonneg_left hbracket hscale
  nlinarith

/-- Transfer the auxiliary `t⁻³` value bound to the original trajectory. -/
private theorem togesV_u_bigO_of_auxiliary_bigO {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ)
    (u uDot v : ℝ → H) (grad : H → H) (t0 C : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hMin : ∃ z, IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (uDot t) t)
    (hv : ∀ t, v t = u t + (t / 4) • uDot t)
    (hC : 0 < C) (hvRate : ∀ t ≥ t0, f (v t) - sInf (Set.range f) ≤ C / t ^ 3) :
    ∃ D : ℝ, 0 < D ∧ ∀ t ≥ t0, f (u t) - sInf (Set.range f) ≤ D / t ^ 3 := by
  rcases hMin with ⟨z, hz⟩
  have hzGlobal : ∀ x : H, f z ≤ f x := by
    simpa [IsMinOn, IsMinFilter] using hz
  have hsInf : sInf (Set.range f) = f z := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨f z, fun y hy => by rcases hy with ⟨x, rfl⟩; exact hzGlobal x⟩
      · exact ⟨z, rfl⟩
    · apply le_csInf
      · exact ⟨f z, ⟨z, rfl⟩⟩
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        exact hzGlobal x
  let G : ℝ → ℝ := fun t => t ^ 4 * (f (u t) - f z) - 4 * C * t
  have hGderiv : ∀ t, t0 ≤ t → deriv G t ≤ 0 := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
    have hFderiv : HasDerivAt (fun r => f (u r) - f z)
        (inner ℝ (grad (u t)) (uDot t)) t := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u t)).comp_hasDerivAt t (hu t ht)).sub_const (f z)
    have hderiv : HasDerivAt G
        (4 * t ^ 3 * (f (u t) - f z) +
          t ^ 4 * inner ℝ (grad (u t)) (uDot t) - 4 * C) t := by
      convert (((hasDerivAt_pow 4 t).mul hFderiv).sub
        ((hasDerivAt_id t).const_mul (4 * C))) using 1; ring
    rw [hderiv.deriv]
    have hsupp := togesV_convex_gradient_le f grad hConvex hGradient (u t) (v t)
    rw [hv t] at hsupp
    have hsupport : 4 * (f (u t) - f z) +
        t * inner ℝ (grad (u t)) (uDot t) ≤ 4 * (f (v t) - f z) := by
      rw [show u t - (u t + (t / 4) • uDot t) = -(t / 4) • uDot t by module,
        real_inner_smul_right] at hsupp
      rw [hv t]
      nlinarith
    have hrate : f (v t) - f z ≤ C / t ^ 3 := by simpa [hsInf] using hvRate t ht
    have hscaled : 4 * t ^ 3 * (f (u t) - f z) +
        t ^ 4 * inner ℝ (grad (u t)) (uDot t) ≤ 4 * C := by
      have := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ t ^ 3 by positivity)
      have hCt : t ^ 3 * (f (v t) - f z) ≤ C :=
        by simpa [mul_comm] using
          (le_div_iff₀ (show 0 < t ^ 3 by positivity)).mp hrate
      nlinarith
    linarith
  have hGcont : ContinuousOn G (Set.Ici t0) := fun t ht =>
    (by
      have hFderiv : HasDerivAt (fun r => f (u r) - f z)
          (inner ℝ (grad (u t)) (uDot t)) t := by
        simpa [innerSL_apply_apply] using
          ((hGradient (u t)).comp_hasDerivAt t (hu t ht)).sub_const (f z)
      exact (((hasDerivAt_pow 4 t).mul hFderiv).sub
        ((hasDerivAt_id t).const_mul (4 * C))).continuousAt.continuousWithinAt)
  have hGdiff : DifferentiableOn ℝ G (interior (Set.Ici t0)) := by
    rw [interior_Ici]
    intro t ht
    have ht' : t0 ≤ t := ht.le
    have hFderiv : HasDerivAt (fun r => f (u r) - f z)
        (inner ℝ (grad (u t)) (uDot t)) t := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u t)).comp_hasDerivAt t (hu t ht')).sub_const (f z)
    exact (((hasDerivAt_pow 4 t).mul hFderiv).sub
      ((hasDerivAt_id t).const_mul (4 * C))).differentiableAt.differentiableWithinAt
  have hGanti := antitoneOn_of_deriv_nonpos (convex_Ici t0) hGcont hGdiff (by
    intro t ht
    have ht' : t0 < t := by simpa using ht
    exact hGderiv t ht'.le)
  let D : ℝ := t0 ^ 3 * (f (u t0) - f z) + 4 * C
  have hDpos : 0 < D := by
    have : 0 ≤ f (u t0) - f z := sub_nonneg.mpr (hzGlobal (u t0))
    dsimp [D]
    have hterm : 0 ≤ t0 ^ 3 * (f (u t0) - f z) := by positivity
    linarith
  refine ⟨D, hDpos, ?_⟩
  intro t ht
  have hGt : G t ≤ G t0 := hGanti (by simp) ht ht
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  rw [hsInf]
  apply (le_div_iff₀ (show 0 < t ^ 3 by positivity)).2
  dsimp [G, D] at hGt ⊢
  have ht0le : t0 ≤ t := ht
  have hF0 : 0 ≤ f (u t0) - f z := sub_nonneg.mpr (hzGlobal (u t0))
  apply le_of_mul_le_mul_right ?_ htpos
  have hfirst : 0 ≤ t0 ^ 3 * (f (u t0) - f z) * (t - t0) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt ht0pos) _) hF0) (sub_nonneg.mpr ht)
  have hsecond : 0 ≤ 4 * C * t0 := by positivity
  nlinarith

/-- The strict auxiliary value estimate transfers through the fourth-power
identity. -/
private theorem togesV_u_littleO_of_auxiliary_littleO {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ)
    (u uDot v : ℝ → H) (grad : H → H) (t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hMin : ∃ z, IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (uDot t) t)
    (hv : ∀ t, v t = u t + (t / 4) • uDot t)
    (hAuxLittle : Asymptotics.IsLittleO atTop
      (fun t => f (v t) - sInf (Set.range f)) (fun t => 1 / t ^ 3)) :
    Asymptotics.IsLittleO atTop
      (fun t => f (u t) - sInf (Set.range f)) (fun t => 1 / t ^ 3) := by
  rcases hMin with ⟨z, hz⟩
  have hzGlobal : ∀ x : H, f z ≤ f x := by
    simpa [IsMinOn, IsMinFilter] using hz
  have hsInf : sInf (Set.range f) = f z := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨f z, fun y hy => by rcases hy with ⟨x, rfl⟩; exact hzGlobal x⟩
      · exact ⟨z, rfl⟩
    · apply le_csInf
      · exact ⟨f z, ⟨z, rfl⟩⟩
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        exact hzGlobal x
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have heps : 0 < c / 5 := by positivity
  obtain ⟨T0, hAuxBound⟩ := Filter.eventually_atTop.1
    ((Asymptotics.isLittleO_iff.1 hAuxLittle) heps)
  let T : ℝ := max t0 (max T0 1)
  have hTt0 : t0 ≤ T := le_max_left _ _
  have hT0 : T0 ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTone : 1 ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  let G : ℝ → ℝ := fun t => t ^ 4 * (f (u t) - f z) - 4 * (c / 5) * t
  have hGderiv : ∀ t, T ≤ t → deriv G t ≤ 0 := by
    intro t ht
    have ht0 : t0 ≤ t := le_trans hTt0 ht
    have htpos : 0 < t := lt_of_lt_of_le ht0pos ht0
    have hFderiv : HasDerivAt (fun r => f (u r) - f z)
        (inner ℝ (grad (u t)) (uDot t)) t := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u t)).comp_hasDerivAt t (hu t ht0)).sub_const (f z)
    have hderiv : HasDerivAt G
        (4 * t ^ 3 * (f (u t) - f z) +
          t ^ 4 * inner ℝ (grad (u t)) (uDot t) - 4 * (c / 5)) t := by
      convert (((hasDerivAt_pow 4 t).mul hFderiv).sub
        ((hasDerivAt_id t).const_mul (4 * (c / 5)))) using 1; ring
    rw [hderiv.deriv]
    have hsupp := togesV_convex_gradient_le f grad hConvex hGradient (u t) (v t)
    rw [hv t] at hsupp
    have hsupport : 4 * (f (u t) - f z) +
        t * inner ℝ (grad (u t)) (uDot t) ≤ 4 * (f (v t) - f z) := by
      rw [show u t - (u t + (t / 4) • uDot t) = -(t / 4) • uDot t by module,
        real_inner_smul_right] at hsupp
      rw [hv t]
      nlinarith
    have haux := hAuxBound t (le_trans hT0 ht)
    have hrate : f (v t) - f z ≤ (c / 5) / t ^ 3 := by
      rw [hsInf] at haux
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hzGlobal (v t))),
        Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / t ^ 3)] at haux
      simpa [div_eq_mul_inv] using haux
    have hscaled := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ t ^ 3 by positivity)
    have hCt : t ^ 3 * (f (v t) - f z) ≤ c / 5 := by
      simpa [mul_comm] using
        (le_div_iff₀ (show 0 < t ^ 3 by positivity)).mp hrate
    nlinarith
  have hGcont : ContinuousOn G (Set.Ici T) := fun t ht =>
    (by
      have ht0 : t0 ≤ t := le_trans hTt0 ht
      have hFderiv : HasDerivAt (fun r => f (u r) - f z)
          (inner ℝ (grad (u t)) (uDot t)) t := by
        simpa [innerSL_apply_apply] using
          ((hGradient (u t)).comp_hasDerivAt t (hu t ht0)).sub_const (f z)
      exact (((hasDerivAt_pow 4 t).mul hFderiv).sub
        ((hasDerivAt_id t).const_mul (4 * (c / 5)))).continuousAt.continuousWithinAt)
  have hGdiff : DifferentiableOn ℝ G (interior (Set.Ici T)) := by
    rw [interior_Ici]
    intro t ht
    have ht0 : t0 ≤ t := le_trans hTt0 ht.le
    have hFderiv : HasDerivAt (fun r => f (u r) - f z)
        (inner ℝ (grad (u t)) (uDot t)) t := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u t)).comp_hasDerivAt t (hu t ht0)).sub_const (f z)
    exact (((hasDerivAt_pow 4 t).mul hFderiv).sub
      ((hasDerivAt_id t).const_mul (4 * (c / 5)))).differentiableAt.differentiableWithinAt
  have hGanti := antitoneOn_of_deriv_nonpos (convex_Ici T) hGcont hGdiff (by
    intro t ht
    have ht' : T < t := by simpa using ht
    exact hGderiv t ht'.le)
  let A : ℝ := T ^ 4 * (f (u T) - f z) - 4 * (c / 5) * T
  let K : ℝ := max T (|A| / (c / 5) + 1)
  filter_upwards [Filter.eventually_ge_atTop K] with t ht
  have htT : T ≤ t := le_max_left _ _ |>.trans ht
  have htpos : 0 < t := lt_of_lt_of_le ht0pos (le_trans hTt0 htT)
  have hGt : G t ≤ G T := hGanti (by simp) htT htT
  have hAt : A / t ≤ c / 5 := by
    have hlarge : |A| / (c / 5) < t := by
      have := le_max_right T (|A| / (c / 5) + 1) |>.trans ht
      linarith
    have habs : A ≤ |A| := le_abs_self A
    have hdiv : |A| / t < c / 5 := by
      rw [div_lt_iff₀ htpos]
      simpa [mul_comm] using (div_lt_iff₀ heps).1 hlarge
    exact (div_le_div_of_nonneg_right habs (le_of_lt htpos)).trans (le_of_lt hdiv)
  have hnonneg : 0 ≤ f (u t) - f z := sub_nonneg.mpr (hzGlobal (u t))
  have hbound : f (u t) - f z ≤ c / t ^ 3 := by
    have hmain : t ^ 3 * (f (u t) - f z) ≤ c := by
      dsimp [G] at hGt
      have htne : t ≠ 0 := ne_of_gt htpos
      have hrewrite : t ^ 4 * (f (u t) - f z) =
          t * (t ^ 3 * (f (u t) - f z)) := by ring
      rw [hrewrite] at hGt
      have hmain' : t * (t ^ 3 * (f (u t) - f z)) ≤ A + 4 * (c / 5) * t := by
        dsimp [A]
        linarith
      have hAt' : A ≤ (c / 5) * t := (div_le_iff₀ htpos).1 hAt
      nlinarith
    exact (le_div_iff₀ (show 0 < t ^ 3 by positivity)).2 (by simpa [mul_comm] using hmain)
  rw [hsInf, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / t ^ 3)]
  simpa [mul_div_assoc] using hbound

private theorem togesV_weighted_cesaro_real_tendsto_zero_local (w g : ℝ → ℝ) (t0 : ℝ)
    (hg : Tendsto g atTop (nhds 0))
    (hw_nonneg : ∀ t ≥ t0, 0 ≤ w t)
    (hw_integrable : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b → IntervalIntegrable w volume a b)
    (hwg_integrable : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b →
      IntervalIntegrable (fun s => w s * g s) volume a b)
    (hW : Tendsto (fun t => ∫ s in t0..t, w s) atTop atTop) :
    Tendsto (fun t => (∫ s in t0..t, w s)⁻¹ * ∫ s in t0..t, w s * g s) atTop
      (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hgabs : Tendsto (fun s => |g s|) atTop (nhds 0) := by
    simpa only [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero.1 hg)
  obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.1
    (hgabs.eventually (eventually_lt_nhds (by linarith : 0 < eps / 2)))
  let T := max t0 T1
  let A := ∫ s in t0..T, w s * g s
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hW (max T (2 * |A| / eps + 1)))
  refine ⟨max T K, fun t ht => ?_⟩
  have hT0 : t0 ≤ T := le_max_left _ _
  have hKt := hK t (le_trans (le_max_right _ _) ht)
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hlarge : 2 * |A| / eps < ∫ s in t0..t, w s := by
    have h := (le_max_right T (2 * |A| / eps + 1)).trans hKt
    linarith
  have hWpos : 0 < ∫ s in t0..t, w s :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) heps.le) hlarge
  have hsplit : (∫ s in t0..t, w s * g s) = A + ∫ s in T..t, w s * g s := by
    dsimp [A]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hwg_integrable (le_refl t0) hT0) (hwg_integrable hT0 htT)]
  have hWsplit : (∫ s in t0..t, w s) = (∫ s in t0..T, w s) + ∫ s in T..t, w s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hw_integrable (le_refl t0) hT0) (hw_integrable hT0 htT)]
  have htail : |∫ s in T..t, w s * g s| ≤ (eps / 2) * (∫ s in T..t, w s) := by
    calc
      |∫ s in T..t, w s * g s| ≤ ∫ s in T..t, |w s * g s| :=
        intervalIntegral.abs_integral_le_integral_abs htT
      _ ≤ ∫ s in T..t, w s * (eps / 2) := by
        apply intervalIntegral.integral_mono_on htT
          (hwg_integrable hT0 htT).abs
          ((hw_integrable hT0 htT).mul_const _)
        intro s hs
        rw [abs_mul, abs_of_nonneg (hw_nonneg s (le_trans hT0 hs.1))]
        exact mul_le_mul_of_nonneg_left
          (le_of_lt (hT1 s (le_trans (le_max_right _ _) hs.1)))
          (hw_nonneg s (le_trans hT0 hs.1))
      _ = (eps / 2) * ∫ s in T..t, w s := by
        rw [intervalIntegral.integral_mul_const]
        ring
  rw [dist_zero_right, Real.norm_eq_abs, hsplit, mul_add]
  calc
    |(∫ s in t0..t, w s)⁻¹ * A + (∫ s in t0..t, w s)⁻¹ * ∫ s in T..t, w s * g s| ≤
        |(∫ s in t0..t, w s)⁻¹ * A| + |(∫ s in t0..t, w s)⁻¹ * ∫ s in T..t, w s * g s| :=
      abs_add_le _ _
    _ < eps / 2 + eps / 2 := by
      apply add_lt_add_of_lt_of_le
      · rw [abs_mul, abs_inv, abs_of_pos hWpos, ← div_eq_inv_mul]
        apply (div_lt_iff₀ hWpos).2
        have hlarge' := (div_lt_iff₀ heps).1 hlarge
        nlinarith
      · rw [abs_mul, abs_inv, abs_of_pos hWpos, ← div_eq_inv_mul]
        have htotal : ∫ s in T..t, w s ≤ ∫ s in t0..t, w s := by
          rw [hWsplit]
          have hprefix : 0 ≤ ∫ s in t0..T, w s := by
            apply intervalIntegral.integral_nonneg hT0
            intro s hs
            exact hw_nonneg s hs.1
          linarith
        apply (div_le_iff₀ hWpos).2
        exact htail.trans (mul_le_mul_of_nonneg_left htotal (by linarith))
    _ = eps := by ring

private theorem togesV_weak_weighted_cesaro_convergence_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (v : ℝ → H) (vInfinity : H) (w : ℝ → ℝ) (t0 : ℝ)
    (hv : Tendsto (fun t => toWeakSpace ℝ H (v t)) atTop (nhds (toWeakSpace ℝ H vInfinity)))
    (hw_nonneg : ∀ t ≥ t0, 0 ≤ w t)
    (hw_integrable : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b → IntervalIntegrable w volume a b)
    (hwv_integrable : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b →
      IntervalIntegrable (fun s => w s • v s) volume a b)
    (hW : Tendsto (fun t => ∫ s in t0..t, w s) atTop atTop) :
    Tendsto (fun t => toWeakSpace ℝ H ((∫ s in t0..t, w s)⁻¹ •
      ∫ s in t0..t, w s • v s)) atTop (nhds (toWeakSpace ℝ H vInfinity)) := by
  apply (weakConvergence_iff_forall_tendsto_inner_right _ vInfinity).2
  intro x
  have hv_coord := (weakConvergence_iff_forall_tendsto_inner_right v vInfinity).1 hv x
  have hcentered : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b →
      IntervalIntegrable (fun s => w s • (v s - vInfinity)) volume a b := by
    intro a b ha hab
    have hconst : IntervalIntegrable (fun s => w s • vInfinity) volume a b :=
      ⟨(hw_integrable ha hab).1.smul_const vInfinity, (hw_integrable ha hab).2.smul_const vInfinity⟩
    convert (hwv_integrable ha hab).sub hconst using 1
    ext s
    module
  have hscalar : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b →
      IntervalIntegrable (fun s => w s * inner ℝ (v s - vInfinity) x) volume a b := by
    intro a b ha hab
    have h := hcentered ha hab
    constructor
    · simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left,
        real_inner_smul_right] using (innerSL ℝ x).integrableOn_comp h.1
    · simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left,
        real_inner_smul_right] using (innerSL ℝ x).integrableOn_comp h.2
  have hcoord : Tendsto (fun t => inner ℝ (v t - vInfinity) x) atTop (nhds 0) := by
    simpa only [inner_sub_left, sub_self] using hv_coord.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => inner ℝ vInfinity x) atTop _)
  have havg := togesV_weighted_cesaro_real_tendsto_zero_local w
    (fun s => inner ℝ (v s - vInfinity) x) t0 hcoord hw_nonneg hw_integrable hscalar hW
  have hnonzero : ∀ᶠ t in atTop, (∫ s in t0..t, w s) ≠ 0 := by
    filter_upwards [(Filter.tendsto_atTop.1 hW 1)] with t ht
    linarith
  have hafter : ∀ᶠ t in atTop, t0 ≤ t := eventually_ge_atTop t0
  have hident : ∀ᶠ t in atTop,
      inner ℝ ((∫ s in t0..t, w s)⁻¹ • ∫ s in t0..t, w s • v s) x =
        inner ℝ vInfinity x + (∫ s in t0..t, w s)⁻¹ *
          ∫ s in t0..t, w s * inner ℝ (v s - vInfinity) x := by
    filter_upwards [hnonzero, hafter] with t ht hle
    have hconst : IntervalIntegrable (fun s => w s • vInfinity) volume t0 t :=
      ⟨(hw_integrable (le_refl t0) hle).1.smul_const vInfinity,
        (hw_integrable (le_refl t0) hle).2.smul_const vInfinity⟩
    have hdecomp : (∫ s in t0..t, w s • v s) =
        (∫ s in t0..t, w s • vInfinity) + ∫ s in t0..t, w s • (v s - vInfinity) := by
      rw [← intervalIntegral.integral_add hconst (hcentered (le_refl t0) hle)]
      apply intervalIntegral.integral_congr
      intro s hs
      module
    have hinter : inner ℝ (∫ s in t0..t, w s • (v s - vInfinity)) x =
        ∫ s in t0..t, w s * inner ℝ (v s - vInfinity) x := by
      simpa [Function.comp_def, innerSL_apply_apply, real_inner_comm, real_inner_smul_left] using
        ((innerSL ℝ x).intervalIntegral_comp_comm (hcentered (le_refl t0) hle)).symm
    rw [hdecomp, intervalIntegral.integral_smul_const]
    simp only [smul_add, inner_add_left, real_inner_smul_left]
    rw [hinter]
    field_simp [ht]
  refine Tendsto.congr' ?_ (by simpa using tendsto_const_nhds.add havg)
  filter_upwards [hident] with t ht
  exact ht.symm

/-- The rate and weak convergence conclusions of Theorem 2.1. -/
theorem togesV_rate_and_weak_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ)
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (alpha t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hMin : ∃ z, IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (uDot t) t)
    (huDot : ∀ t, t0 ≤ t → HasDerivAt uDot (uDdot t) t)
    (huDdot : ∀ t, t0 ≤ t → HasDerivAt uDdot (uDddot t) t)
    (hDerivative : ∀ t, t0 ≤ t →
      deriv u t = uDot t ∧ deriv (deriv u) t = uDdot t ∧
        deriv (deriv (deriv u)) t = uDddot t)
    (hAuxiliaryStrict : 3 < alpha → ∃ vInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t : ℝ => f (u t + (t / 4) • uDot t) - sInf (Set.range f))
        (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t + (t / 4) • uDot t)) atTop
        (nhds (toWeakSpace ℝ H vInfinity)) ∧
      f vInfinity = sInf (Set.range f))
    (hTrajectory : IsTOGESV alpha u f) :
    (3 ≤ alpha → ∃ C : ℝ, 0 < C ∧ ∀ t ≥ t0,
      f (u t + (t / 4) • uDot t) - sInf (Set.range f) ≤ C / t ^ 3 ∧
      f (u t) - sInf (Set.range f) ≤ C / t ^ 3) ∧
    (3 < alpha → ∃ uInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t : ℝ => f (u t + (t / 4) • uDot t) - sInf (Set.range f))
        (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t : ℝ => f (u t) - sInf (Set.range f))
        (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t)) atTop
        (nhds (toWeakSpace ℝ H uInfinity)) ∧
      f uInfinity = sInf (Set.range f)) := by
  have hvData := togesV_auxiliary_hasDerivAt u uDot uDdot uDddot t0 hu huDot huDdot
  have hgrad_eq : ∀ x : H, gradient f x = grad x := by
    intro x
    have h2 : HasGradientAt f (grad x) x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa only [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
        InnerProductSpace.toContinuousLinearMap_toDualMap] using hGradient x
    exact (h2.unique ((hGradient x).differentiableAt.hasGradientAt)).symm
  have hEquation : ∀ t, t0 ≤ t →
      uDddot t + ((alpha + 7) / t) • uDdot t +
        (5 * (alpha + 1) / t ^ 2) • uDot t +
        grad (u t + (t / 4) • uDot t) = 0 := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ht0pos ht)
    rcases hDerivative t ht with ⟨hdu, hddu, hdddu⟩
    exact IsTOGESV.equation_of_derivatives hTrajectory hdu hddu hdddu htne
      (hgrad_eq (u t + (t / 4) • uDot t))
  have hveq := togesV_auxiliary_equation u uDot uDdot uDddot grad alpha t0 ht0pos hEquation
  constructor
  · intro hAlpha
    rcases togesV_auxiliary_bigO f
      (fun t => u t + (t / 4) • uDot t)
      (fun t => (5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)
      (fun t => (3 / 2 : ℝ) • uDdot t + (t / 4) • uDddot t)
      grad alpha t0 hConvex hGradient hMin ht0pos hvData.1 hvData.2 hveq hAlpha with
      ⟨C, hC, hvRate⟩
    rcases togesV_u_bigO_of_auxiliary_bigO f u uDot
      (fun t => u t + (t / 4) • uDot t) grad t0 C hConvex hGradient hMin ht0pos hu
      (by intro t; rfl) hC hvRate with ⟨D, hD, huRate⟩
    refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro t ht
    constructor
    · exact (hvRate t ht).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt (pow_pos (lt_of_lt_of_le ht0pos ht) 3)))
    · exact (huRate t ht).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt (pow_pos (lt_of_lt_of_le ht0pos ht) 3)))
  · intro hAlpha
    rcases hAuxiliaryStrict hAlpha with ⟨vInfinity, hvLittle, hvWeak, hvMin⟩
    rcases hMin with ⟨z, hz⟩
    have hzGlobal : ∀ x : H, f z ≤ f x := by
      simpa [IsMinOn, IsMinFilter] using hz
    have hsInf : sInf (Set.range f) = f z := by
      apply le_antisymm
      · apply csInf_le
        · exact ⟨f z, fun y hy => by
            rcases hy with ⟨x, rfl⟩
            exact hzGlobal x⟩
        · exact ⟨z, rfl⟩
      · apply le_csInf
        · exact ⟨f z, ⟨z, rfl⟩⟩
        · intro y hy
          rcases hy with ⟨x, rfl⟩
          exact hzGlobal x
    let v : ℝ → H := fun t => u t + (t / 4) • uDot t
    let vDot : ℝ → H := fun t => (5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t
    let vDdot : ℝ → H := fun t => (3 / 2 : ℝ) • uDdot t + (t / 4) • uDddot t
    have hv : ∀ t, t0 ≤ t → HasDerivAt v (vDot t) t := by
      intro t ht
      simpa [v, vDot] using hvData.1 t ht
    have hvDot : ∀ t, t0 ≤ t → HasDerivAt vDot (vDdot t) t := by
      intro t ht
      simpa [vDot, vDdot] using hvData.2 t ht
    have hEq : ∀ t, t0 ≤ t → vDdot t + ((alpha + 1) / t) • vDot t +
        (t / 4) • grad (v t) = 0 := by
      intro t ht
      simpa [v, vDot, vDdot] using hveq t ht
    have hAuxLittle : Asymptotics.IsLittleO atTop
        (fun t : ℝ => f (v t) - sInf (Set.range f)) (fun t => 1 / t ^ 3) := by
      simpa [v] using hvLittle
    have hAuxWeak : Tendsto (fun t => toWeakSpace ℝ H (v t)) atTop
        (nhds (toWeakSpace ℝ H vInfinity)) := by
      simpa [v] using hvWeak
    refine ⟨vInfinity, hAuxLittle, ?_, ?_, ?_⟩
    · exact togesV_u_littleO_of_auxiliary_littleO f u uDot v grad t0 hConvex hGradient
        ⟨z, hz⟩ ht0pos hu (by intro t; rfl) hAuxLittle
    · let w : ℝ → ℝ := fun s => 4 * s ^ 3
      have hw_nonneg : ∀ s ≥ t0, 0 ≤ w s := by
        intro s hs
        dsimp [w]
        have hspos : 0 < s := lt_of_lt_of_le ht0pos hs
        positivity
      have hw_integrable : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b →
          IntervalIntegrable w volume a b := by
        intro a b ha hab
        apply ContinuousOn.intervalIntegrable_of_Icc hab
        fun_prop
      have hwv_integrable : ∀ ⦃a b⦄, t0 ≤ a → a ≤ b →
          IntervalIntegrable (fun s => w s • v s) volume a b := by
        intro a b ha hab
        apply ContinuousOn.intervalIntegrable_of_Icc hab
        apply ContinuousOn.smul
        · fun_prop
        · intro s hs
          exact (hv s (le_trans ha hs.1)).continuousAt.continuousWithinAt
      have hWformula : ∀ t, t0 ≤ t → ∫ s in t0..t, w s = t ^ 4 - t0 ^ 4 := by
        intro t ht
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun r : ℝ => r ^ 4) (f' := w)
        · intro s hs
          dsimp [w]
          convert hasDerivAt_pow 4 s using 1
        · exact hw_integrable (le_refl t0) ht
      have hW : Tendsto (fun t => ∫ s in t0..t, w s) atTop atTop := by
        refine Tendsto.congr' ?_ (tendsto_atTop_add_const_right atTop (-t0 ^ 4)
          (tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)))
        filter_upwards [eventually_ge_atTop t0] with t ht
        simpa [sub_eq_add_neg] using (hWformula t ht).symm
      have hAvgWeak := togesV_weak_weighted_cesaro_convergence_local v vInfinity w t0
        hAuxWeak hw_nonneg hw_integrable hwv_integrable hW
      apply (weakConvergence_iff_forall_tendsto_inner_right _ vInfinity).2
      intro x
      have hAvgCoord :=
        (weakConvergence_iff_forall_tendsto_inner_right _ vInfinity).1 hAvgWeak x
      let A : ℝ → H := fun t => (∫ s in t0..t, w s)⁻¹ • ∫ s in t0..t, w s • v s
      have hVInt : ∀ t, t0 ≤ t → ∫ s in t0..t, w s • v s =
          t ^ 4 • u t - t0 ^ 4 • u t0 := by
        intro t ht
        change ∫ s in t0..t, ((4 : ℝ) * s ^ 3) •
          (u s + (s / 4) • uDot s) = t ^ 4 • u t - t0 ^ 4 • u t0
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun r => r ^ 4 • u r)
          (f' := fun s => ((4 : ℝ) * s ^ 3) • (u s + (s / 4) • uDot s))
          (by
            intro s hs
            rw [Set.uIcc_of_le ht] at hs
            exact togesV_power_four_hasDerivAt u uDot t0 hu s hs.1)
          (by simpa [w, v] using hwv_integrable (le_refl t0) ht)
      have hBary : ∀ᶠ t in atTop, u t = (t0 ^ 4 / t ^ 4) • u t0 +
          ((t ^ 4 - t0 ^ 4) / t ^ 4) • A t := by
        filter_upwards [eventually_gt_atTop (max t0 1)] with t ht
        have ht0 : t0 < t := lt_of_le_of_lt (le_max_left _ _) ht
        have htone : 1 < t := lt_of_le_of_lt (le_max_right t0 1) ht
        have htpos : 0 < t := by linarith
        have htne : t ^ 4 ≠ 0 := ne_of_gt (by positivity)
        have hDpos : 0 < t ^ 4 - t0 ^ 4 := by
          have hpow : t0 ^ 4 < t ^ 4 := pow_lt_pow_left₀ ht0 ht0pos.le (by norm_num)
          linarith
        have hDne : t ^ 4 - t0 ^ 4 ≠ 0 := ne_of_gt hDpos
        rw [show A t = (t ^ 4 - t0 ^ 4)⁻¹ •
            (t ^ 4 • u t - t0 ^ 4 • u t0) by simp [A, hWformula t ht0.le, hVInt t ht0.le]]
        have hcoefU : ((t ^ 4 - t0 ^ 4) / t ^ 4) * (t ^ 4 - t0 ^ 4)⁻¹ * t ^ 4 = 1 := by
          field_simp
        have hcoef0 : t0 ^ 4 / t ^ 4 -
            ((t ^ 4 - t0 ^ 4) / t ^ 4) * (t ^ 4 - t0 ^ 4)⁻¹ * t0 ^ 4 = 0 := by
          field_simp
          ring
        symm
        calc
          (t0 ^ 4 / t ^ 4) • u t0 + ((t ^ 4 - t0 ^ 4) / t ^ 4) •
              ((t ^ 4 - t0 ^ 4)⁻¹ • (t ^ 4 • u t - t0 ^ 4 • u t0)) =
              (t0 ^ 4 / t ^ 4 - ((t ^ 4 - t0 ^ 4) / t ^ 4) *
                (t ^ 4 - t0 ^ 4)⁻¹ * t0 ^ 4) • u t0 +
                (((t ^ 4 - t0 ^ 4) / t ^ 4) * (t ^ 4 - t0 ^ 4)⁻¹ * t ^ 4) • u t := by module
          _ = u t := by rw [hcoef0, hcoefU]; simp
      have hInv : Tendsto (fun t : ℝ => (t ^ 4)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0))
      have hFirst : Tendsto (fun t : ℝ => t0 ^ 4 / t ^ 4) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hInv :
          Tendsto (fun t : ℝ => t0 ^ 4 * (t ^ 4)⁻¹) atTop (nhds (t0 ^ 4 * 0)))
      have hSecond : Tendsto (fun t : ℝ => (t ^ 4 - t0 ^ 4) / t ^ 4) atTop (nhds 1) := by
        have hEq : (fun t : ℝ => (t ^ 4 - t0 ^ 4) / t ^ 4) =ᶠ[atTop]
            fun t => 1 - t0 ^ 4 / t ^ 4 := by
          filter_upwards [eventually_gt_atTop 0] with t ht
          field_simp [ne_of_gt (pow_pos ht 4)]
        refine Tendsto.congr' hEq.symm ?_
        simpa using tendsto_const_nhds.sub hFirst
      have hCoord : Tendsto (fun t => inner ℝ (A t) x) atTop
          (nhds (inner ℝ vInfinity x)) := by
        simpa [A] using hAvgCoord
      have hRhs : Tendsto (fun t : ℝ => inner ℝ ((t0 ^ 4 / t ^ 4) • u t0 +
          ((t ^ 4 - t0 ^ 4) / t ^ 4) • A t) x) atTop (nhds (inner ℝ vInfinity x)) := by
        simp only [inner_add_left, real_inner_smul_left]
        simpa using (hFirst.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => inner ℝ (u t0) x) atTop _)).add
          (hSecond.mul hCoord)
      refine Tendsto.congr' ?_ hRhs
      filter_upwards [hBary] with t ht
      rw [ht]
    · simpa [hsInf] using hvMin
