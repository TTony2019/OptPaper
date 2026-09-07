import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_2

open MeasureTheory

/- EXTERNAL DEPENDENCY: Theorem 2.1 of Attouch, Chbani, and Riahi
   Source: Attouch H, Chbani Z, Riahi H. Fast convex optimization via a third-order in time evolution equation. Optimization. 2022;71(5):1275-1304.
   Status: proof not available — provide referenced paper MD to fill.
   To resolve: place the referenced paper in todo/ and re-run the pipeline.
-/

/-- A classical solution of the third-order TOGES equation on its positive time domain.
    This local predicate corrects the malformed imported `IsTOGES`, whose leading
    term repeats the acceleration instead of using the third derivative. -/
private def IsClassicalTOGES {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (alpha t0 : ℝ) : Prop :=
  0 < t0 ∧
  (∀ t, t0 ≤ t → HasDerivAt u (uDot t) t) ∧
  (∀ t, t0 ≤ t → HasDerivAt uDot (uDdot t) t) ∧
  (∀ t, t0 ≤ t → HasDerivAt uDdot (uDddot t) t) ∧
  ∀ t, t0 ≤ t →
    uDddot t + ((3 * alpha + 5) / (2 * t)) • uDdot t +
      ((3 * alpha - 1) / t ^ 2) • uDot t + grad (u t + t • uDot t) = 0

private theorem sInf_range_eq_value_of_global_min {H : Type*} (f : H → ℝ) (z : H)
    (hz : ∀ x, f z ≤ f x) : sInf (Set.range f) = f z := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨f z, ?_⟩
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hz x
    · exact ⟨z, rfl⟩
  · refine le_csInf ?_ ?_
    · exact ⟨f z, ⟨z, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hz x

/-- First-order lower support inequality for a differentiable convex objective. -/
private theorem convex_gradient_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (grad : H → H)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGrad : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x) (x y : H) :
    f x - f y ≤ inner ℝ (grad x) (x - y) := by
  let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y x
  have hline : HasDerivAt line (x - y) 1 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - y)).add_const y using 1
    all_goals simp
  have hphi : ConvexOn ℝ Set.univ (f ∘ line) := by
    simpa [line] using hConvex.comp_affineMap (AffineMap.lineMap y x)
  have hderiv : HasDerivAt (f ∘ line) (inner ℝ (grad x) (x - y)) 1 := by
    have hGradLine : HasFDerivAt f (innerSL ℝ (grad x)) (line 1) := by
      simpa [line] using hGrad x
    simpa [innerSL_apply_apply] using hGradLine.comp_hasDerivAt 1 hline
  have hslope := hphi.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
    (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hderiv
  simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using hslope

/-- The standard TOGES change of variables and its first two derivatives. -/
private theorem toges_change_of_variables_hasDerivAt {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (alpha t0 : ℝ)
    (hTrajectory : IsClassicalTOGES u uDot uDdot uDddot grad alpha t0) :
    let v : ℝ → H := fun t => u t + t • uDot t
    let vDot : ℝ → H := fun t => 2 • uDot t + t • uDdot t
    (∀ t, t0 ≤ t → HasDerivAt v (vDot t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt vDot (3 • uDdot t + t • uDddot t) t) := by
  dsimp
  rcases hTrajectory with ⟨_, hu, huDot, huDdot, _⟩
  constructor
  · intro t ht
    have htu := hu t ht
    have htudot := huDot t ht
    have htid : HasDerivAt (fun s : ℝ => s) 1 t := by
      simpa only [id] using hasDerivAt_id t
    convert htu.add (htid.smul htudot) using 1;
      module
  · intro t ht
    have htudot := huDot t ht
    have htuddot := huDdot t ht
    have htid : HasDerivAt (fun s : ℝ => s) 1 t := by
      simpa only [id] using hasDerivAt_id t
    convert (htudot.const_smul 2).add (htid.smul htuddot) using 1;
      module

/-- Under the TOGES equation, `u + t u'` satisfies the rescaled AVD equation. -/
private theorem toges_change_of_variables_equation {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (alpha t0 : ℝ)
    (hTrajectory : IsClassicalTOGES u uDot uDdot uDddot grad alpha t0) :
    ∀ t, t0 ≤ t →
      let v : ℝ → H := fun s => u s + s • uDot s
      let vDot : ℝ → H := fun s => 2 • uDot s + s • uDdot s
      let vDdot : ℝ → H := fun s => 3 • uDdot s + s • uDddot s
      vDdot t + ((3 * alpha - 1) / (2 * t)) • vDot t + t • grad (v t) = 0 := by
  intro t ht
  dsimp
  rcases hTrajectory with ⟨ht0, _, _, _, hEq⟩
  have htpos : 0 < t := lt_of_lt_of_le ht0 ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hscaled := congrArg (fun q : H => t • q) (hEq t ht)
  have ht_acc : t * ((3 * alpha + 5) / (2 * t)) = (3 * alpha + 5) / 2 := by
    field_simp [htne]
  have ht_vel : t * ((3 * alpha - 1) / t ^ 2) = (3 * alpha - 1) / t := by
    field_simp [htne]
  have hcoeff : 3 + ((3 * alpha - 1) / 2) = (3 * alpha + 5) / 2 := by ring
  have hcross : ((3 * alpha - 1) / (2 * t)) * t = (3 * alpha - 1) / 2 := by
    field_simp [htne]
  have hvelcross : ((3 * alpha - 1) / (2 * t)) * 2 = (3 * alpha - 1) / t := by
    field_simp [htne]
  simp only [smul_zero, smul_add, smul_smul] at hscaled
  rw [ht_acc, ht_vel] at hscaled
  rw [← Nat.cast_smul_eq_nsmul ℝ 3, ← Nat.cast_smul_eq_nsmul ℝ 2]
  change (3 : ℝ) • uDdot t + t • uDddot t +
    ((3 * alpha - 1) / (2 * t)) • ((2 : ℝ) • uDot t + t • uDdot t) +
      t • grad (u t + t • uDot t) = 0
  simp only [smul_add, smul_smul]
  rw [hvelcross, hcross]
  calc
    _ = t • uDddot t + (3 + (3 * alpha - 1) / 2) • uDdot t +
        ((3 * alpha - 1) / t) • uDot t + t • grad (u t + t • uDot t) := by
      module
    _ = 0 := by simpa [hcoeff] using hscaled

/-- Derivative of the rescaled TOGES momentum.  Keeping the three trajectories
    explicit here is important: it lets the product-rule witness be rewritten
    before the change-of-variables definitions are unfolded. -/
private theorem toges_momentum_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (v vDot vDdot : ℝ → H) (grad : H → H)
    (alpha s : ℝ) (z : H) (hv : HasDerivAt v (vDot s) s)
    (hvDot : HasDerivAt vDot (vDdot s) s) (hspos : 0 < s)
    (heq : vDdot s + ((3 * alpha - 1) / (2 * s)) • vDot s +
      s • grad (v s) = 0) :
    HasDerivAt
      (fun r => ((3 / 2) * (alpha - 1)) • (v r - z) + r • vDot r)
      (-s ^ 2 • grad (v s)) s := by
  let a : ℝ := (3 / 2) * (alpha - 1)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hraw := ((hv.sub_const z).const_smul a).add
    ((hasDerivAt_id s).smul hvDot)
  have hcoef : s * ((3 * alpha - 1) / (2 * s)) = (3 * alpha - 1) / 2 := by
    field_simp [hsne]
  have hscaled := congrArg (fun q : H => s • q) heq
  simp only [smul_zero, smul_add, smul_smul] at hscaled
  rw [hcoef] at hscaled
  have hscaled' : s • vDdot s + ((3 * alpha - 1) / 2) • vDot s +
      s ^ 2 • grad (v s) = 0 := by
    simpa only [pow_two] using hscaled
  have hsvDdot : s • vDdot s = -((3 * alpha - 1) / 2) • vDot s -
      s ^ 2 • grad (v s) := by
    apply (eq_sub_iff_add_eq).2
    rw [neg_smul]
    apply (eq_neg_iff_add_eq_zero).2
    simpa only [add_assoc, add_left_comm, add_comm] using hscaled'
  have hcancel : a + 1 - (3 * alpha - 1) / 2 = 0 := by
    dsimp [a]
    ring
  have hraw_eq : a • vDot s + (s • vDdot s + (1 : ℝ) • vDot s) =
      -s ^ 2 • grad (v s) := by
    rw [hsvDdot]
    module
  simpa only [a, id] using hraw.congr_deriv hraw_eq

/-- Derivative certificate for the Lyapunov energy of the transformed TOGES
    trajectory. -/
private theorem toges_energy_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (grad : H → H)
    (v vDot vDdot : ℝ → H) (alpha s : ℝ) (z : H)
    (hGrad : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hv : HasDerivAt v (vDot s) s)
    (hvDot : HasDerivAt vDot (vDdot s) s) (hspos : 0 < s)
    (heq : vDdot s + ((3 * alpha - 1) / (2 * s)) • vDot s +
      s • grad (v s) = 0) :
    HasDerivAt
      (fun r => r ^ 3 * (f (v r) - f z) +
        (1 / 2) * ‖((3 / 2) * (alpha - 1)) • (v r - z) + r • vDot r‖ ^ 2)
      (s ^ 2 * (3 * (f (v s) - f z) -
        ((3 / 2) * (alpha - 1)) * inner ℝ (grad (v s)) (v s - z))) s := by
  let a : ℝ := (3 / 2) * (alpha - 1)
  let w : ℝ → H := fun r => a • (v r - z) + r • vDot r
  have hF : HasDerivAt (fun r => f (v r) - f z)
      (inner ℝ (grad (v s)) (vDot s)) s := by
    simpa [innerSL_apply_apply] using ((hGrad (v s)).comp_hasDerivAt s hv).sub_const (f z)
  have hw : HasDerivAt w (-s ^ 2 • grad (v s)) s := by
    simpa [w, a] using toges_momentum_hasDerivAt v vDot vDdot grad alpha s z hv hvDot hspos heq
  have hraw := ((hasDerivAt_pow 3 s).mul hF).add (hw.norm_sq.const_mul (1 / 2 : ℝ))
  have hderiv_eq :
      3 * s ^ 2 * (f (v s) - f z) + s ^ 3 * inner ℝ (grad (v s)) (vDot s) +
        (1 / 2) * (2 * inner ℝ (w s) (-s ^ 2 • grad (v s))) =
      s ^ 2 * (3 * (f (v s) - f z) - a * inner ℝ (grad (v s)) (v s - z)) := by
    rw [show w s = a • (v s - z) + s • vDot s by rfl]
    rw [inner_add_left]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (grad (v s)) (vDot s),
      real_inner_comm (v s - z) (grad (v s))]
    dsimp [a]
    ring
  simpa [w, a, pow_succ] using hraw.congr_deriv hderiv_eq

/-- Derivative certificate for the identity `t * u t` used in the barycentric
    representation of a TOGES trajectory. -/
private theorem toges_t_mul_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (u uDot : ℝ → H) (t0 : ℝ)
    (hu : ∀ s, t0 ≤ s → HasDerivAt u (uDot s) s) :
    ∀ s, t0 ≤ s → HasDerivAt (fun r => r • u r) (u s + s • uDot s) s := by
  intro s hs
  convert (hasDerivAt_id s).smul (hu s hs) using 1; simp [id] ; module

/-- Jensen's inequality in the form needed for the TOGES barycentric estimate. -/
private theorem integral_jensen_for_f {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (grad : H → H)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (a b : ℝ) (g : ℝ → H) (hab : a < b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : IntervalIntegrable (fun s => f (g s)) volume a b) :
    f ((b - a)⁻¹ • ∫ s in a..b, g s) ≤
      (b - a)⁻¹ * ∫ s in a..b, f (g s) := by
  let m : H := (b - a)⁻¹ • ∫ s in a..b, g s
  have hlen_pos : 0 < b - a := sub_pos.mpr hab
  have hlen_ne : b - a ≠ 0 := ne_of_gt hlen_pos
  have hab_le : a ≤ b := hab.le
  have hgI : IntegrableOn g (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp hg
  have hfgI : IntegrableOn (fun s => f (g s)) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp hfg
  have hIoc_ne_top : volume (Set.Ioc a b) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hconstH : IntegrableOn (fun _ : ℝ => m) (Set.Ioc a b) volume :=
    integrableOn_const (hs := hIoc_ne_top)
  have hsubI : IntegrableOn (fun s => g s - m) (Set.Ioc a b) volume :=
    hgI.sub hconstH
  have hinnerI : IntegrableOn (fun s => inner ℝ (grad m) (g s - m))
      (Set.Ioc a b) volume := hsubI.const_inner (grad m)
  have hconstR : IntegrableOn (fun _ : ℝ => f m) (Set.Ioc a b) volume :=
    integrableOn_const (hs := hIoc_ne_top)
  have hleftI : IntegrableOn (fun s => f m + inner ℝ (grad m) (g s - m))
      (Set.Ioc a b) volume := hconstR.add hinnerI
  have hpoint : ∀ s : ℝ, f m + inner ℝ (grad m) (g s - m) ≤ f (g s) := by
    intro s
    have hsupport := convex_gradient_le f grad hConvex hGradient m (g s)
    rw [show m - g s = -(g s - m) by module, inner_neg_right] at hsupport
    linarith
  have hmono : ∫ s in Set.Ioc a b, f m + inner ℝ (grad m) (g s - m) ≤
      ∫ s in Set.Ioc a b, f (g s) := integral_mono hleftI hfgI hpoint
  have hsub_integral : ∫ s in Set.Ioc a b, g s - m =
      (∫ s in Set.Ioc a b, g s) - ∫ _ in Set.Ioc a b, m := integral_sub hgI hconstH
  have hinner_integral : ∫ s in Set.Ioc a b, inner ℝ (grad m) (g s - m) =
      inner ℝ (grad m) (∫ s in Set.Ioc a b, g s - m) := integral_inner hsubI (grad m)
  have hconstR_integral : ∫ _ in Set.Ioc a b, f m = (b - a) * f m := by
    rw [← intervalIntegral.integral_of_le hab_le, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hconstH_integral : ∫ _ in Set.Ioc a b, m = (b - a) • m := by
    rw [← intervalIntegral.integral_of_le hab_le, intervalIntegral.integral_const]
  have hleft_calc : ∫ s in Set.Ioc a b, f m + inner ℝ (grad m) (g s - m) =
      (b - a) * f m + inner ℝ (grad m)
        ((∫ s in Set.Ioc a b, g s) - (b - a) • m) := by
    rw [integral_add hconstR hinnerI, hinner_integral, hsub_integral,
      hconstR_integral, hconstH_integral]
  have hrem : inner ℝ (grad m) ((∫ s in Set.Ioc a b, g s) - (b - a) • m) = 0 := by
    dsimp [m]
    rw [← intervalIntegral.integral_of_le hab_le, smul_smul]
    simp [mul_inv_cancel₀ hlen_ne]
  have hraw : (b - a) * f m ≤ ∫ s in Set.Ioc a b, f (g s) := by
    rw [hleft_calc, hrem, add_zero] at hmono
    exact hmono
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hlen_pos.le)
  rw [← intervalIntegral.integral_of_le hab_le] at hscaled
  have hfinal : f m ≤ (b - a)⁻¹ * ∫ s in a..b, f (g s) := by
    convert hscaled using 1; field_simp [hlen_ne]
  simpa [m] using hfinal

theorem attouch_chbani_riahi_toges_rate {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (alpha t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x : H, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hMin : ∃ z, IsMinOn f Set.univ z)
    (hTrajectory : IsClassicalTOGES u uDot uDdot uDddot grad alpha t0)
    (hAlpha : 3 ≤ alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ≥ t0,
      f (u t + t • uDot t) - sInf (Set.range f) ≤ C / t ^ 3 ∧
      f (u t) - sInf (Set.range f) ≤
        (t0 * (f (u t0) - sInf (Set.range f)) + C / (2 * t0 ^ 2)) / t := by
  rcases hMin with ⟨z, hz⟩
  have hz_global : ∀ x : H, f z ≤ f x := by
    simpa [IsMinOn, IsMinFilter] using hz
  have hsInf : sInf (Set.range f) = f z := sInf_range_eq_value_of_global_min f z hz_global
  rcases hTrajectory with ⟨ht0pos, hu, huDot, huDdot, hEq⟩
  have hTrajectory' : IsClassicalTOGES u uDot uDdot uDddot grad alpha t0 :=
    ⟨ht0pos, hu, huDot, huDdot, hEq⟩
  let v : ℝ → H := fun s => u s + s • uDot s
  let vDot : ℝ → H := fun s => 2 • uDot s + s • uDdot s
  let vDdot : ℝ → H := fun s => 3 • uDdot s + s • uDddot s
  let a : ℝ := (3 / 2) * (alpha - 1)
  let E : ℝ → ℝ := fun s => s ^ 3 * (f (v s) - f z) +
    (1 / 2) * ‖a • (v s - z) + s • vDot s‖ ^ 2
  have hv : ∀ s, t0 ≤ s → HasDerivAt v (vDot s) s := by
    intro s hs
    simpa [v, vDot] using (toges_change_of_variables_hasDerivAt u uDot uDdot uDddot grad alpha t0 hTrajectory').1 s hs
  have hvDot : ∀ s, t0 ≤ s → HasDerivAt vDot (vDdot s) s := by
    intro s hs
    simpa [vDot, vDdot] using (toges_change_of_variables_hasDerivAt u uDot uDdot uDddot grad alpha t0 hTrajectory').2 s hs
  have hveq : ∀ s, t0 ≤ s →
      vDdot s + ((3 * alpha - 1) / (2 * s)) • vDot s + s • grad (v s) = 0 := by
    intro s hs
    simpa [v, vDot, vDdot] using
      toges_change_of_variables_equation u uDot uDdot uDddot grad alpha t0 hTrajectory' s hs
  have ha_ge_three : 3 ≤ a := by
    dsimp [a]
    nlinarith
  have hEderiv : ∀ s, t0 ≤ s → HasDerivAt E
      (s ^ 2 * (3 * (f (v s) - f z) - a * inner ℝ (grad (v s)) (v s - z))) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ht0pos hs
    simpa [E, a] using toges_energy_hasDerivAt f grad v vDot vDdot alpha s z hGradient
      (hv s hs) (hvDot s hs) hspos (hveq s hs)
  have hEderiv_nonpos : ∀ s, t0 ≤ s → deriv E s ≤ 0 := by
    intro s hs
    have hFnonneg : 0 ≤ f (v s) - f z := sub_nonneg.mpr (hz_global (v s))
    have hsupport := convex_gradient_le f grad hConvex hGradient (v s) z
    have hinner_nonneg : 0 ≤ inner ℝ (grad (v s)) (v s - z) := le_trans hFnonneg hsupport
    have hbracket : 3 * (f (v s) - f z) - a * inner ℝ (grad (v s)) (v s - z) ≤ 0 := by
      nlinarith
    rw [(hEderiv s hs).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hbracket
  have hEcont : ContinuousOn E (Set.Ici t0) := by
    intro s hs
    exact (hEderiv s hs).continuousAt.continuousWithinAt
  have hEdiff : DifferentiableOn ℝ E (interior (Set.Ici t0)) := by
    rw [interior_Ici]
    intro s hs
    have hs' : t0 < s := by simpa using hs
    exact (hEderiv s hs'.le).differentiableAt.differentiableWithinAt
  have hEanti : AntitoneOn E (Set.Ici t0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici t0) hEcont hEdiff (by
      intro s hs
      have hs' : t0 < s := by simpa using hs
      exact hEderiv_nonpos s hs'.le)
  have hE_nonneg : 0 ≤ E t0 := by
    have hF : 0 ≤ f (v t0) - f z := sub_nonneg.mpr (hz_global (v t0))
    have hfirst : 0 ≤ t0 ^ 3 * (f (v t0) - f z) :=
      mul_nonneg (by positivity) hF
    have hsecond : 0 ≤ (1 / 2 : ℝ) * ‖a • (v t0 - z) + t0 • vDot t0‖ ^ 2 := by positivity
    exact add_nonneg hfirst hsecond
  let C : ℝ := E t0 + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith
  have hfirst_rate : ∀ t, t0 ≤ t → f (v t) - f z ≤ C / t ^ 3 := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
    have hEbound : E t ≤ E t0 := hEanti (by simp) ht ht
    have hE_lt_C : E t < C := by
      dsimp [C]
      linarith
    have hkin_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖a • (v t - z) + t • vDot t‖ ^ 2 := by positivity
    have hmul : t ^ 3 * (f (v t) - f z) ≤ C := by
      dsimp [E] at hE_lt_C
      linarith
    exact (le_div_iff₀ (by positivity : 0 < t ^ 3)).2 (by simpa [mul_comm] using hmul)
  refine ⟨C, hCpos, ?_⟩
  intro t ht
  constructor
  · simpa [v, hsInf] using hfirst_rate t ht
  · rw [hsInf]
    by_cases hteq : t = t0
    · subst t
      have hnonneg : 0 ≤ C / (2 * t0 ^ 2) := by positivity
      have ht0ne : t0 ≠ 0 := ne_of_gt ht0pos
      apply (le_div_iff₀ ht0pos).2
      field_simp [ht0ne]
      nlinarith
    · have htstrict : t0 < t := lt_of_le_of_ne ht (Ne.symm hteq)
      have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ht0pos ht)
      have hlenne : t - t0 ≠ 0 := ne_of_gt (sub_pos.mpr htstrict)
      have hvCont : ContinuousOn v (Set.uIcc t0 t) := by
        intro s hs
        rw [Set.uIcc_of_le ht] at hs
        have hs' : t0 ≤ s := hs.1
        exact (hv s hs').continuousAt.continuousWithinAt
      have hfVCont : ContinuousOn (fun s => f (v s)) (Set.uIcc t0 t) := by
        intro s hs
        rw [Set.uIcc_of_le ht] at hs
        have hs' : t0 ≤ s := hs.1
        exact ((hGradient (v s)).comp_hasDerivAt s (hv s hs')).continuousAt.continuousWithinAt
      have hvInt : IntervalIntegrable v volume t0 t := hvCont.intervalIntegrable
      have hfVInt : IntervalIntegrable (fun s => f (v s)) volume t0 t := hfVCont.intervalIntegrable
      have hu_integral : ∫ s in t0..t, v s = t • u t - t0 • u t0 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s hs => toges_t_mul_hasDerivAt u uDot t0 hu s (by
            rw [Set.uIcc_of_le ht] at hs
            exact hs.1)) hvInt]
      have hu_repr : u t = (t0 / t) • u t0 + ((t - t0) / t) •
          ((t - t0)⁻¹ • ∫ s in t0..t, v s) := by
        have hmul_repr : t • u t = t0 • u t0 + (t - t0) •
            ((t - t0)⁻¹ • ∫ s in t0..t, v s) := by
          simp only [smul_smul, mul_inv_cancel₀ hlenne, one_smul]
          rw [hu_integral]
          module
        have hinv_repr := congrArg (fun q : H => t⁻¹ • q) hmul_repr
        change t⁻¹ • (t • u t) = t⁻¹ •
          (t0 • u t0 + (t - t0) • ((t - t0)⁻¹ • ∫ s in t0..t, v s)) at hinv_repr
        rw [smul_add, smul_smul, smul_smul, smul_smul,
          inv_mul_cancel₀ htne, one_smul] at hinv_repr
        simpa [div_eq_mul_inv, mul_comm] using hinv_repr
      have hwt0 : 0 ≤ t0 / t := div_nonneg ht0pos.le (lt_of_lt_of_le ht0pos ht).le
      have hwt : 0 ≤ (t - t0) / t := div_nonneg (sub_nonneg.mpr ht) (lt_of_lt_of_le ht0pos ht).le
      have hw_sum : t0 / t + (t - t0) / t = 1 := by
        field_simp [htne]
        ring
      have hconv_bound : f (u t) ≤ (t0 / t) * f (u t0) + ((t - t0) / t) *
          f ((t - t0)⁻¹ • ∫ s in t0..t, v s) := by
        rw [hu_repr]
        simpa [smul_eq_mul] using hConvex.2 (show u t0 ∈ Set.univ by simp)
          (show (t - t0)⁻¹ • ∫ s in t0..t, v s ∈ Set.univ by simp) hwt0 hwt hw_sum
      have hJensen := integral_jensen_for_f f grad hConvex hGradient t0 t v htstrict hvInt hfVInt
      have hJscaled := mul_le_mul_of_nonneg_left hJensen hwt
      have hconstInt : IntervalIntegrable (fun _ : ℝ => f z) volume t0 t := intervalIntegrable_const
      have hFInt : IntervalIntegrable (fun s => f (v s) - f z) volume t0 t := hfVInt.sub hconstInt
      have hsubInt : ∫ s in t0..t, (f (v s) - f z) =
          (∫ s in t0..t, f (v s)) - (t - t0) * f z := by
        rw [intervalIntegral.integral_sub hfVInt hconstInt, intervalIntegral.integral_const]
        ring
      have hJscaled' : ((t - t0) / t) * f ((t - t0)⁻¹ • ∫ s in t0..t, v s) ≤
          (1 / t) * ∫ s in t0..t, f (v s) := by
        calc
          _ ≤ ((t - t0) / t) * ((t - t0)⁻¹ * ∫ s in t0..t, f (v s)) := hJscaled
          _ = _ := by field_simp [htne, hlenne]
      have hpre : f (u t) - f z ≤ (t0 / t) * (f (u t0) - f z) +
          (1 / t) * ∫ s in t0..t, (f (v s) - f z) := by
        rw [hsubInt]
        have hconv_split : f (u t) ≤ t0 * f (u t0) / t +
            ((t - t0) * f ((t - t0)⁻¹ • ∫ s in t0..t, v s)) / t := by
          convert hconv_bound using 1; ring
        have hJsplit : ((t - t0) * f ((t - t0)⁻¹ • ∫ s in t0..t, v s)) / t ≤
            (∫ s in t0..t, f (v s)) / t := by
          convert hJscaled' using 1 <;> ring
        have hcomb : f (u t) ≤ (t0 * f (u t0) + ∫ s in t0..t, f (v s)) / t := by
          calc
            f (u t) ≤ t0 * f (u t0) / t +
                ((t - t0) * f ((t - t0)⁻¹ • ∫ s in t0..t, v s)) / t := hconv_split
            _ ≤ t0 * f (u t0) / t + (∫ s in t0..t, f (v s)) / t :=
              by simpa [add_comm] using add_le_add_right hJsplit (t0 * f (u t0) / t)
            _ = _ := by ring
        calc
          f (u t) - f z ≤ (t0 * f (u t0) + ∫ s in t0..t, f (v s)) / t - f z :=
            sub_le_sub_right hcomb _
          _ = _ := by field_simp [htne]; ring
      let G : ℝ → ℝ := fun s => (-C / 2) * (s ^ 2)⁻¹
      have hGderiv : ∀ s ∈ Set.uIcc t0 t, HasDerivAt G (C / s ^ 3) s := by
        intro s hs
        rw [Set.uIcc_of_le ht] at hs
        have hspos : 0 < s := lt_of_lt_of_le ht0pos hs.1
        have hsne : s ≠ 0 := ne_of_gt hspos
        have hsqne : s ^ 2 ≠ 0 := pow_ne_zero 2 hsne
        have hraw : HasDerivAt (fun r : ℝ => (-C / 2) * (r ^ 2)⁻¹)
            ((-C / 2) * (-(2 * s) / (s ^ 2) ^ 2)) s := by
          convert (hasDerivAt_const s (-C / 2)).mul
            (((hasDerivAt_id s).pow 2).inv hsqne) using 1;
            simp [id]
        dsimp [G]
        convert hraw using 1; field_simp [hsne]
      have hRateCont : ContinuousOn (fun s : ℝ => C / s ^ 3) (Set.uIcc t0 t) := by
        intro s hs
        rw [Set.uIcc_of_le ht] at hs
        have hspos : 0 < s := lt_of_lt_of_le ht0pos hs.1
        have hsne : s ≠ 0 := ne_of_gt hspos
        exact (continuousAt_const.div (continuousAt_id.pow 3)
          (pow_ne_zero 3 hsne)).continuousWithinAt
      have hRateInt : IntervalIntegrable (fun s : ℝ => C / s ^ 3) volume t0 t :=
        hRateCont.intervalIntegrable
      have hGint : ∫ s in t0..t, C / s ^ 3 = G t - G t0 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hRateInt]
      have hmonoInt : ∫ s in t0..t, (f (v s) - f z) ≤ ∫ s in t0..t, C / s ^ 3 := by
        exact intervalIntegral.integral_mono_on ht hFInt hRateInt
          (fun s hs => hfirst_rate s hs.1)
      have htail_nonneg : 0 ≤ C / (2 * t ^ 2) := by positivity
      have hIntBound : ∫ s in t0..t, (f (v s) - f z) ≤ C / (2 * t0 ^ 2) := by
        calc
          _ ≤ ∫ s in t0..t, C / s ^ 3 := hmonoInt
          _ = G t - G t0 := hGint
          _ ≤ C / (2 * t0 ^ 2) := by
            dsimp [G]
            have ht_term : (-C / 2) * (t ^ 2)⁻¹ = -(C / (2 * t ^ 2)) := by
              field_simp [htne]
            have ht0ne : t0 ≠ 0 := ne_of_gt ht0pos
            have ht0_term : (-C / 2) * (t0 ^ 2)⁻¹ = -(C / (2 * t0 ^ 2)) := by
              field_simp [ht0ne]
            rw [ht_term, ht0_term]
            linarith
      have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
      have hscaledInt := mul_le_mul_of_nonneg_left hIntBound
        (show 0 ≤ 1 / t by positivity)
      calc
        f (u t) - f z ≤ (t0 / t) * (f (u t0) - f z) +
            (1 / t) * ∫ s in t0..t, (f (v s) - f z) := hpre
        _ ≤ (t0 / t) * (f (u t0) - f z) + (1 / t) * (C / (2 * t0 ^ 2)) :=
          by simpa [add_comm] using
            add_le_add_left hscaledInt ((t0 / t) * (f (u t0) - f z))
        _ = (t0 * (f (u t0) - f z) + C / (2 * t0 ^ 2)) / t := by
          field_simp [htne]
