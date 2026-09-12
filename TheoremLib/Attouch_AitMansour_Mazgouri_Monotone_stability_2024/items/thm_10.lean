import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_10
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_thm_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_8
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_thm_6

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set
open MeasureTheory Filter Function IsUnifLocDoublingMeasure
open scoped Topology

-- The Volterra map `Γ` (in its centered, derivative-free form) and the
-- approximate solution set `S^ε(μ)` are defined in `items/def_10.lean`, where
-- they carry the paper's Definition 7.5; they are used here via the import.

/-- An approximate fixed point of the centered Volterra map is close to an
exact fixed point on every short interval on which the map is contractive. -/
theorem pathSupNorm_le_of_centeredIntegralMap_residual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H]
    (A : H → H) (u₀ v₀ : H) (x y : ℝ → H) (α γ T ε : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hT : 0 < T)
    (hcoco : CocoerciveOn α Set.univ (fun z : Set.univ => A z))
    (hxcont : ContinuousOn x (Set.Icc (0 : ℝ) T))
    (hycont : ContinuousOn y (Set.Icc (0 : ℝ) T))
    (hfixed : ∀ t ∈ Set.Icc (0 : ℝ) T,
      centeredIntegralMap A γ u₀ v₀ x t = x t)
    (hres : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖y t - centeredIntegralMap A γ u₀ v₀ y t‖ ≤ ε)
    (hγT : γ * T + T ^ 2 / α < 1) :
    pathSupNorm T (fun t => y t - x t) ≤
      (ε * α) / (α - α * γ * T - T ^ 2) := by
  let d : ℝ → H := fun s => y s - x s
  let D : ℝ := pathSupNorm T d
  have hdcont : ContinuousOn d (Set.Icc (0 : ℝ) T) := hycont.sub hxcont
  have hDnonneg : 0 ≤ D := pathSupNorm_nonneg_of_continuousOn hT.le hdcont
  have hd_le (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) : ‖d s‖ ≤ D :=
    norm_le_pathSupNorm_of_continuousOn hdcont hs
  have hL (a b : H) : ‖A a - A b‖ ≤ α⁻¹ * ‖a - b‖ := by
    have h := (cocoercive_implies_lipschitz A α hcoco).dist_le_mul a b
    simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
  have hmapDiff (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      centeredIntegralMap A γ u₀ v₀ y t - centeredIntegralMap A γ u₀ v₀ x t =
        -γ • (∫ s in (0 : ℝ)..t, d s) +
          ∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s)) := by
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun _ hs =>
      ⟨hs.1, hs.2.trans ht.2⟩
    have hyII : IntervalIntegrable (fun s => y s - u₀) volume 0 t :=
      ((hycont.mono hsub).sub continuousOn_const).intervalIntegrable_of_Icc ht.1
    have hxII : IntervalIntegrable (fun s => x s - u₀) volume 0 t :=
      ((hxcont.mono hsub).sub continuousOn_const).intervalIntegrable_of_Icc ht.1
    have hAcontY : ContinuousOn (fun s => A (y s)) (Set.Icc (0 : ℝ) t) :=
      (cocoercive_implies_lipschitz A α hcoco).continuous.continuousOn.comp
        (hycont.mono hsub) (mapsTo_univ _ _)
    have hAcontX : ContinuousOn (fun s => A (x s)) (Set.Icc (0 : ℝ) t) :=
      (cocoercive_implies_lipschitz A α hcoco).continuous.continuousOn.comp
        (hxcont.mono hsub) (mapsTo_univ _ _)
    have hAYII : IntervalIntegrable (fun s => A (y s)) volume 0 t :=
      hAcontY.intervalIntegrable_of_Icc ht.1
    have hAXII : IntervalIntegrable (fun s => A (x s)) volume 0 t :=
      hAcontX.intervalIntegrable_of_Icc ht.1
    have hkernelYII : IntervalIntegrable (fun s => (s - t) • A (y s)) volume 0 t :=
      hAYII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    have hkernelXII : IntervalIntegrable (fun s => (s - t) • A (x s)) volume 0 t :=
      hAXII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    have hposSub :
        (∫ s in (0 : ℝ)..t, d s) =
          (∫ s in (0 : ℝ)..t, y s - u₀) - ∫ s in (0 : ℝ)..t, x s - u₀ := by
      rw [← intervalIntegral.integral_sub hyII hxII]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [d]
      module
    have hopSub :
        (∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s))) =
          (∫ s in (0 : ℝ)..t, (s - t) • A (y s)) -
            ∫ s in (0 : ℝ)..t, (s - t) • A (x s) := by
      rw [← intervalIntegral.integral_sub hkernelYII hkernelXII]
      apply intervalIntegral.integral_congr
      intro s _
      module
    unfold centeredIntegralMap
    rw [hposSub, hopSub]
    module
  have hmapBound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      ‖centeredIntegralMap A γ u₀ v₀ y t - centeredIntegralMap A γ u₀ v₀ x t‖ ≤
        γ * T * D + T ^ 2 * (α⁻¹ * D) := by
    have hdamp : ‖γ • (∫ s in (0 : ℝ)..t, d s)‖ ≤ γ * T * D := by
      have hint : ‖∫ s in (0 : ℝ)..t, d s‖ ≤ D * t := by
        have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
          (C := D) (f := d) (a := (0 : ℝ)) (b := t) (fun s hs => by
            apply hd_le s
            have hsu := Set.uIoc_subset_uIcc hs
            rw [Set.uIcc_of_le ht.1] at hsu
            exact ⟨hsu.1, hsu.2.trans ht.2⟩)
        simpa [abs_of_nonneg ht.1] using hbound
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      calc
        γ * ‖∫ s in (0 : ℝ)..t, d s‖ ≤ γ * (D * t) :=
          mul_le_mul_of_nonneg_left hint hγ.le
        _ ≤ γ * (D * T) := by
          apply mul_le_mul_of_nonneg_left _ hγ.le
          exact mul_le_mul_of_nonneg_left ht.2 hDnonneg
        _ = γ * T * D := by ring
    have hopInt :
        ‖∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s))‖ ≤
          T ^ 2 * (α⁻¹ * D) := by
      have hcoeff : 0 ≤ α⁻¹ * D := mul_nonneg (inv_nonneg.mpr hα.le) hDnonneg
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := T * (α⁻¹ * D))
        (f := fun s => (s - t) • (A (y s) - A (x s)))
        (a := (0 : ℝ)) (b := t) (fun s hs => by
          have hsu := Set.uIoc_subset_uIcc hs
          rw [Set.uIcc_of_le ht.1] at hsu
          have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hsu.1, hsu.2.trans ht.2⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hsu.2)]
          exact mul_le_mul (by linarith [hsu.1, ht.2])
            ((hL (y s) (x s)).trans
              (mul_le_mul_of_nonneg_left (hd_le s hsT) (inv_nonneg.mpr hα.le)))
            (norm_nonneg _) hT.le)
      have hbound' :
          ‖∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s))‖ ≤
            (T * (α⁻¹ * D)) * t := by
        simpa [abs_of_nonneg ht.1] using hbound
      calc
        ‖∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s))‖ ≤
            (T * (α⁻¹ * D)) * t := hbound'
        _ ≤ (T * (α⁻¹ * D)) * T :=
          mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hT.le hcoeff)
        _ = T ^ 2 * (α⁻¹ * D) := by ring
    rw [hmapDiff t ht]
    calc
      ‖-γ • (∫ s in (0 : ℝ)..t, d s) +
          ∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s))‖ ≤
          ‖γ • (∫ s in (0 : ℝ)..t, d s)‖ +
            ‖∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s))‖ := by
        simpa only [neg_smul, norm_neg] using
          norm_add_le (-γ • (∫ s in (0 : ℝ)..t, d s))
            (∫ s in (0 : ℝ)..t, (s - t) • (A (y s) - A (x s)))
      _ ≤ γ * T * D + T ^ 2 * (α⁻¹ * D) := add_le_add hdamp hopInt
  have hdPoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      ‖d t‖ ≤ ε + γ * T * D + T ^ 2 * (α⁻¹ * D) := by
    have heq : d t =
        (y t - centeredIntegralMap A γ u₀ v₀ y t) +
          (centeredIntegralMap A γ u₀ v₀ y t -
            centeredIntegralMap A γ u₀ v₀ x t) := by
      rw [hfixed t ht]
      dsimp [d]
      module
    rw [heq]
    calc
      ‖(y t - centeredIntegralMap A γ u₀ v₀ y t) +
          (centeredIntegralMap A γ u₀ v₀ y t -
            centeredIntegralMap A γ u₀ v₀ x t)‖ ≤
          ‖y t - centeredIntegralMap A γ u₀ v₀ y t‖ +
            ‖centeredIntegralMap A γ u₀ v₀ y t -
              centeredIntegralMap A γ u₀ v₀ x t‖ := norm_add_le _ _
      _ ≤ ε + (γ * T * D + T ^ 2 * (α⁻¹ * D)) :=
        add_le_add (hres t ht) (hmapBound t ht)
      _ = ε + γ * T * D + T ^ 2 * (α⁻¹ * D) := by ring
  have hDbound : D ≤ ε + γ * T * D + T ^ 2 * (α⁻¹ * D) :=
    pathSupNorm_le_of_forall hT.le hdPoint
  have hdenom : 0 < α - α * γ * T - T ^ 2 := by
    have hcore : α * γ * T + T ^ 2 < α := by
      calc
        α * γ * T + T ^ 2 = α * (γ * T + T ^ 2 / α) := by
          field_simp [hα.ne']
        _ < α * 1 := mul_lt_mul_of_pos_left hγT hα
        _ = α := by ring
    nlinarith
  have hscaled : (α - α * γ * T - T ^ 2) * D ≤ α * ε := by
    have hclean : α * D ≤ α * ε + α * γ * T * D + T ^ 2 * D := by
      calc
        α * D ≤ α * (ε + γ * T * D + T ^ 2 * (α⁻¹ * D)) :=
          mul_le_mul_of_nonneg_left hDbound hα.le
        _ = α * ε + α * γ * T * D + T ^ 2 * D := by
          field_simp [hα.ne']
    nlinarith
  change D ≤ _
  apply (le_div_iff₀ hdenom).mpr
  simpa [mul_comm] using hscaled

/-! ### Remark 7.7: the Painlevé–Kuratowski convergence of `S^ε(μ)`

The two inputs of the convergence statement are proved here as standalone
lemmas: the centered Volterra map `Γ` is Lipschitz for the sup norm with the
constant `γT + T²/α` appearing in Theorem 7.1, and its fixed points are
unique — the paper's `Fix(Γ) = {x_μ}`. -/

/-- The sup norm of a difference of paths is the supremum of the pointwise
  norms of the differences (definitional unfolding). -/
theorem pathSupNorm_sub_eq_sSup {H : Type*} [NormedAddCommGroup H] {T : ℝ}
    (x y : ℝ → H) :
    pathSupNorm T (fun t => x t - y t) =
      sSup {d : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) T, d = ‖x t - y t‖} := rfl

/-- The centered Volterra map `Γ` is Lipschitz for the sup norm with the
  constant `γT + T²/α` of Theorem 7.1: the damping term contributes `γT` and
  the cocoercive nonlinearity `T²/α`, exactly as in the paper's computation. -/
theorem centeredIntegralMap_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : H → H) (γ : ℝ) (u₀ v₀ : H) (α T : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hT : 0 < T)
    (hcoco : CocoerciveOn α Set.univ (fun z : Set.univ => A z))
    {x y : ℝ → H} (hx : ContinuousOn x (Set.Icc (0 : ℝ) T))
    (hy : ContinuousOn y (Set.Icc (0 : ℝ) T)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖centeredIntegralMap A γ u₀ v₀ x t - centeredIntegralMap A γ u₀ v₀ y t‖ ≤
        (γ * T + T ^ 2 / α) * pathSupNorm T (fun s => x s - y s) := by
  intro t ht
  set δ : ℝ := pathSupNorm T (fun s => x s - y s)
  have hδ0 : 0 ≤ δ := pathSupNorm_nonneg_of_continuousOn hT.le (hx.sub hy)
  have hpt (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) : ‖x s - y s‖ ≤ δ :=
    norm_le_pathSupNorm_of_continuousOn (hx.sub hy) hs
  have hd : ContinuousOn (fun s => x s - y s) (Set.Icc (0 : ℝ) T) := hx.sub hy
  have hAlip : LipschitzWith (Real.toNNReal (1 / α)) A :=
    cocoercive_implies_lipschitz A α hcoco
  have hAxy : ContinuousOn (fun s => A (x s) - A (y s)) (Set.Icc (0 : ℝ) T) :=
    (hAlip.continuous.continuousOn.comp hx (mapsTo_univ _ _)).sub
      (hAlip.continuous.continuousOn.comp hy (mapsTo_univ _ _))
  have ht0 : 0 ≤ t := ht.1
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc_right ht.2
  have hIIx : IntervalIntegrable (fun s => x s - u₀) volume 0 t :=
    ((hx.mono hsub).sub continuousOn_const).intervalIntegrable_of_Icc ht0
  have hIIy : IntervalIntegrable (fun s => y s - u₀) volume 0 t :=
    ((hy.mono hsub).sub continuousOn_const).intervalIntegrable_of_Icc ht0
  have hIIA : IntervalIntegrable (fun s => (s - t) • A (x s)) volume 0 t :=
    ((hAlip.continuous.continuousOn.comp hx (mapsTo_univ _ _)).mono hsub)
      |>.intervalIntegrable_of_Icc ht0
      |>.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
  have hIIB : IntervalIntegrable (fun s => (s - t) • A (y s)) volume 0 t :=
    ((hAlip.continuous.continuousOn.comp hy (mapsTo_univ _ _)).mono hsub)
      |>.intervalIntegrable_of_Icc ht0
      |>.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
  have hII2 : IntervalIntegrable (fun s => (s - t) • (A (x s) - A (y s))) volume 0 t :=
    (hAxy.mono hsub).intervalIntegrable_of_Icc ht0
      |>.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
  have e1 : (∫ s in (0 : ℝ)..t, (x s - u₀)) - ∫ s in (0 : ℝ)..t, (y s - u₀) =
      ∫ s in (0 : ℝ)..t, (x s - y s) := by
    rw [← intervalIntegral.integral_sub hIIx hIIy]
    exact intervalIntegral.integral_congr fun s _ => by abel
  have e2 : (∫ s in (0 : ℝ)..t, (s - t) • A (x s)) -
      ∫ s in (0 : ℝ)..t, (s - t) • A (y s) =
      ∫ s in (0 : ℝ)..t, (s - t) • (A (x s) - A (y s)) := by
    rw [← intervalIntegral.integral_sub hIIA hIIB]
    exact intervalIntegral.integral_congr fun s _ => by rw [smul_sub]
  have hstep : centeredIntegralMap A γ u₀ v₀ x t - centeredIntegralMap A γ u₀ v₀ y t =
      -γ • (∫ s in (0 : ℝ)..t, (x s - y s)) +
        ∫ s in (0 : ℝ)..t, (s - t) • (A (x s) - A (y s)) := by
    simp only [centeredIntegralMap]
    conv_lhs =>
      rw [show (u₀ + t • v₀ - γ • (∫ s in (0:ℝ)..t, (x s - u₀)) +
            ∫ s in (0:ℝ)..t, (s - t) • A (x s)) -
          (u₀ + t • v₀ - γ • (∫ s in (0:ℝ)..t, (y s - u₀)) +
            ∫ s in (0:ℝ)..t, (s - t) • A (y s)) =
          -γ • ((∫ s in (0:ℝ)..t, (x s - u₀)) - ∫ s in (0:ℝ)..t, (y s - u₀)) +
            ((∫ s in (0:ℝ)..t, (s - t) • A (x s)) -
              ∫ s in (0:ℝ)..t, (s - t) • A (y s)) from by module]
    rw [e1, e2]
  have hdamp : ‖γ • (∫ s in (0 : ℝ)..t, (x s - y s))‖ ≤ γ * T * δ := by
    have hnorm : ‖∫ s in (0 : ℝ)..t, (x s - y s)‖ ≤ δ * t := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := δ) (f := fun s => x s - y s) (a := (0 : ℝ)) (b := t)
        (fun s hs => by
          have hs' : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
          rw [Set.uIcc_of_le ht0] at hs'
          exact hpt s ⟨hs'.1, le_trans hs'.2 ht.2⟩)
      simpa [abs_of_nonneg ht0] using hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    calc
      γ * ‖∫ s in (0 : ℝ)..t, (x s - y s)‖ ≤ γ * (δ * t) :=
        mul_le_mul_of_nonneg_left hnorm hγ
      _ ≤ γ * (δ * T) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hδ0) hγ
      _ = γ * T * δ := by ring
  have hop : ‖∫ s in (0 : ℝ)..t, (s - t) • (A (x s) - A (y s))‖ ≤ T ^ 2 / α * δ := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := T * (δ / α)) (f := fun s => (s - t) • (A (x s) - A (y s)))
      (a := (0 : ℝ)) (b := t) (fun s hs => by
        have hs' : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
        rw [Set.uIcc_of_le ht0] at hs'
        have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs'.1, le_trans hs'.2 ht.2⟩
        have hlip : ‖A (x s) - A (y s)‖ ≤ α⁻¹ * ‖x s - y s‖ := by
          have h := (cocoercive_implies_lipschitz A α hcoco).dist_le_mul (x s) (y s)
          simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)]
            using h
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hs'.2), neg_sub]
        have h1 : t - s ≤ T := by linarith [hs'.1, ht.2]
        have h2 : ‖A (x s) - A (y s)‖ ≤ α⁻¹ * δ :=
          hlip.trans (mul_le_mul_of_nonneg_left (hpt s hsT) (inv_nonneg.mpr hα.le))
        calc
          (t - s) * ‖A (x s) - A (y s)‖ ≤ (t - s) * (α⁻¹ * δ) :=
            mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hs'.2)
          _ ≤ T * (α⁻¹ * δ) := by
            refine mul_le_mul_of_nonneg_right h1 ?_
            positivity
          _ = T * (δ / α) := by ring)
    have hb' : ‖∫ s in (0 : ℝ)..t, (s - t) • (A (x s) - A (y s))‖ ≤
        (T * (δ / α)) * t := by
      simpa [abs_of_nonneg ht0] using hb
    calc
      ‖∫ s in (0 : ℝ)..t, (s - t) • (A (x s) - A (y s))‖ ≤ (T * (δ / α)) * t := hb'
      _ ≤ (T * (δ / α)) * T := by
        refine mul_le_mul_of_nonneg_left ht.2 ?_
        positivity
      _ = T ^ 2 / α * δ := by ring
  rw [hstep]
  refine (norm_add_le _ _).trans ?_
  have hcombined : γ * T * δ + T ^ 2 / α * δ = (γ * T + T ^ 2 / α) * δ := by ring
  calc
    ‖-γ • (∫ s in (0 : ℝ)..t, (x s - y s))‖ +
        ‖∫ s in (0 : ℝ)..t, (s - t) • (A (x s) - A (y s))‖ ≤
        γ * T * δ + T ^ 2 / α * δ := by
      simpa only [neg_smul, norm_neg] using add_le_add hdamp hop
    _ = (γ * T + T ^ 2 / α) * δ := hcombined

/-- The fixed points of the centered Volterra map `Γ` on continuous paths are
  unique — the paper's `Fix(Γ) = {x_μ}` of Theorem 7.1, recovered here as the
  contraction estimate `γT + T²/α < 1`. -/
theorem centeredIntegralMap_fixed_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : H → H) (γ : ℝ) (u₀ v₀ : H) (α T : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hT : 0 < T)
    (hcoco : CocoerciveOn α Set.univ (fun z : Set.univ => A z))
    (hcontract : γ * T + T ^ 2 / α < 1)
    {x y : ℝ → H} (hx : ContinuousOn x (Set.Icc (0 : ℝ) T))
    (hy : ContinuousOn y (Set.Icc (0 : ℝ) T))
    (hxfix : ∀ t ∈ Set.Icc (0 : ℝ) T,
      centeredIntegralMap A γ u₀ v₀ x t = x t)
    (hyfix : ∀ t ∈ Set.Icc (0 : ℝ) T,
      centeredIntegralMap A γ u₀ v₀ y t = y t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  have hlip := centeredIntegralMap_lipschitz A γ u₀ v₀ α T hα hγ hT hcoco hx hy
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖x t - y t‖ ≤ (γ * T + T ^ 2 / α) * pathSupNorm T (fun s => x s - y s) := by
    intro t ht
    calc
      ‖x t - y t‖ = ‖centeredIntegralMap A γ u₀ v₀ x t -
          centeredIntegralMap A γ u₀ v₀ y t‖ := by rw [hxfix t ht, hyfix t ht]
      _ ≤ (γ * T + T ^ 2 / α) * pathSupNorm T (fun s => x s - y s) := hlip t ht
  have hD : pathSupNorm T (fun s => x s - y s) ≤
      (γ * T + T ^ 2 / α) * pathSupNorm T (fun s => x s - y s) :=
    pathSupNorm_le_of_forall hT.le hpoint
  have hD0 : 0 ≤ pathSupNorm T (fun s => x s - y s) :=
    pathSupNorm_nonneg_of_continuousOn hT.le (hx.sub hy)
  have hfac : 0 < 1 - (γ * T + T ^ 2 / α) := by linarith
  have hDz : pathSupNorm T (fun s => x s - y s) = 0 := by nlinarith
  intro t ht
  have hle := norm_le_pathSupNorm_of_continuousOn (hx.sub hy) ht
  rw [hDz] at hle
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

-- `approxSolutions` (= the paper's `S^ε(μ)`, Definition 7.5) is defined in
-- `items/def_10.lean` and imported here.

/-- A strong solution of `S(A,u₀,v₀)` is a fixed point of the centered
  Volterra map `Γ` on `[0,T]` — the `{x_μ} ⊆ Fix(Γ)` half of the paper's
  `Fix(Γ) = {x_μ}` of Theorem 7.1 (uniqueness is
  `centeredIntegralMap_fixed_unique`).  This is what turns the pointwise
  residual defining `S^ε(μ)` into an estimate against the exact solution. -/
theorem centeredIntegralMap_eq_of_solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedSpace ℝ H]
    (A : H → H) (x dx ddx : ℝ → H) (u₀ v₀ : H) (α γ : ℝ)
    (hcoco : CocoerciveOn α Set.univ (fun z : Set.univ => A z))
    (hsol : ext_def_2 A γ u₀ v₀ x dx ddx) :
    ∀ t : ℝ, 0 ≤ t → centeredIntegralMap A γ u₀ v₀ x t = x t := by
  intro t ht
  have hcenter := centered_solution_integral_identity A x dx ddx u₀ v₀ α γ t hcoco hsol ht
  unfold centeredIntegralMap
  calc
    (u₀ + t • v₀ - γ • (∫ s in (0 : ℝ)..t, x s - u₀)) +
        ∫ s in (0 : ℝ)..t, (s - t) • A (x s) =
        u₀ + ((t • v₀ - γ • (∫ s in (0 : ℝ)..t, x s - u₀)) +
          ∫ s in (0 : ℝ)..t, (s - t) • A (x s)) := by module
    _ = u₀ + (x t - u₀) := by rw [hcenter]
    _ = x t := by module

/-- The first field of `def_3` gives continuity of the trajectory on `[0,T]`. -/
theorem continuousOn_of_solution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : H → H} {γ : ℝ} {u₀ v₀ : H} {x dx ddx : ℝ → H} {T : ℝ} (hT : 0 < T)
    (hsol : def_3 A γ u₀ v₀ x dx ddx) : ContinuousOn x (Set.Icc (0 : ℝ) T) :=
  (((hsol.1 T hT).1).continuousOn).mono Set.Icc_subset_uIcc

/-- Theorem 7.8: Assume the conditions of Theorem 7.1. For each μ, let x_μ be
  the unique strong global solution of S(A_μ,u₀^μ,v₀^μ). For all ε>0 and
  all μ,μ′, S^ε(μ) and S^ε(μ′) are nonempty and the Hausdorff estimate (29)
  holds:
  h(S^ε(μ),S^ε(μ′)) ≤ εα/(α−αγT−T²)+α/(α−αγT−T²)(‖u₀^μ−u₀^{μ′}‖+T‖v₀^μ−v₀^{μ′}‖+T²θ₁‖μ−μ′‖^{θ₂}).
  When ε→0, S^ε(μ) converges to {x_μ} in the sup norm. -/
theorem thm_10 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (θ₁ θ₂ : ℝ) (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
      ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hγT : γ * T + T ^ 2 / α < 1) :
    let denom := α - α * γ * T - T ^ 2
    let Sε (μ : M) (ε : ℝ) : Set (ℝ → H) := approxSolutions A γ u₀ v₀ T ε μ
    let bound (μ μ' : M) : ℝ :=
      (α / denom) * (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂)
    -- denom is strictly positive (follows from hγT)
    0 < denom ∧
    -- (i) S^ε(μ) nonempty for all ε>0, and the Hausdorff estimate (29)
    (∀ ε > 0, ∀ μ ∈ V, ∀ μ' ∈ V,
      (Sε μ ε).Nonempty ∧ (Sε μ' ε).Nonempty ∧
      -- h(S^ε(μ),S^ε(μ′)) ≤ bound, expressed as mutual excess inequalities
      (∀ y ∈ Sε μ ε, ∃ y' ∈ Sε μ' ε,
        pathSupNorm T (fun t => y t - y' t) ≤ (ε * α) / denom + bound μ μ') ∧
      (∀ y' ∈ Sε μ' ε, ∃ y ∈ Sε μ ε,
        pathSupNorm T (fun t => y t - y' t) ≤ (ε * α) / denom + bound μ μ')) ∧
    -- (ii) As ε→0, S^ε(μ) converges to x_μ in the sup norm
    (∀ μ ∈ V, ∀ η > 0, ∃ ε > 0, ∀ y : ℝ → H, y ∈ Sε μ ε →
      pathSupNorm T (fun t => y t - x μ t) < η) := by
  dsimp
  have hcore : α * γ * T + T ^ 2 < α := by
    calc
      α * γ * T + T ^ 2 = α * (γ * T + T ^ 2 / α) := by
        field_simp [hα.ne']
      _ < α * 1 := mul_lt_mul_of_pos_left hγT hα
      _ = α := by ring
  have hdenom : 0 < α - α * γ * T - T ^ 2 := by
    nlinarith
  have hxcont (μ : M) (hμ : μ ∈ V) :
      ContinuousOn (x μ) (Set.Icc (0 : ℝ) T) :=
    continuousOn_of_solution hT (hsol μ hμ).2
  have hxzero (μ : M) (hμ : μ ∈ V) : x μ 0 = u₀ μ :=
    (hsol μ hμ).2.2.1
  have hfixed (μ : M) (hμ : μ ∈ V) (t : ℝ)
      (ht : t ∈ Set.Icc (0 : ℝ) T) :
      centeredIntegralMap (A μ) γ (u₀ μ) (v₀ μ) (x μ) t = x μ t :=
    centeredIntegralMap_eq_of_solution (A μ) (x μ) (dx μ) (ddx μ) (u₀ μ) (v₀ μ) α γ
      (hcoco μ hμ) (hsol μ hμ) t ht.1
  have hexactMem (ε : ℝ) (hε : 0 ≤ ε) (μ : M) (hμ : μ ∈ V) :
      ContinuousOn (x μ) (Set.Icc (0 : ℝ) T) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ‖x μ t - centeredIntegralMap (A μ) γ (u₀ μ) (v₀ μ) (x μ) t‖ ≤ ε := by
    refine ⟨hxcont μ hμ, ?_⟩
    intro t ht
    rw [hfixed μ hμ t ht, sub_self, norm_zero]
    exact hε
  have happBound (ε : ℝ) (μ : M) (hμ : μ ∈ V) (y : ℝ → H)
      (hy : ContinuousOn y (Set.Icc (0 : ℝ) T) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ‖y t - centeredIntegralMap (A μ) γ (u₀ μ) (v₀ μ) y t‖ ≤ ε) :
      pathSupNorm T (fun t => y t - x μ t) ≤
        (ε * α) / (α - α * γ * T - T ^ 2) := by
    exact pathSupNorm_le_of_centeredIntegralMap_residual
      (A μ) (u₀ μ) (v₀ μ) (x μ) y α γ T ε hα (hsol μ hμ).1 hT
      (hcoco μ hμ) (hxcont μ hμ) hy.1 (hfixed μ hμ) hy.2 hγT
  have hcross := thm_8 V A x dx ddx u₀ v₀ α γ T hα hT hcoco hsol θ₁ θ₂ hC₂ hγT
  refine ⟨hdenom, ?_, ?_⟩
  · intro ε hε μ hμ μ' hμ'
    have hxmem := hexactMem ε hε.le μ hμ
    have hxmem' := hexactMem ε hε.le μ' hμ'
    refine ⟨⟨x μ, hxmem⟩, ⟨x μ', hxmem'⟩, ?_, ?_⟩
    · intro y hy
      refine ⟨x μ', hxmem', ?_⟩
      have happ := happBound ε μ hμ y hy
      have hparamBound := hcross μ hμ μ' hμ'
      have hyxcont : ContinuousOn (fun t => y t - x μ t) (Set.Icc (0 : ℝ) T) :=
        hy.1.sub (hxcont μ hμ)
      have hxxcont : ContinuousOn (fun t => x μ t - x μ' t) (Set.Icc (0 : ℝ) T) :=
        (hxcont μ hμ).sub (hxcont μ' hμ')
      apply pathSupNorm_le_of_forall hT.le
      intro t ht
      have heq : y t - x μ' t = (y t - x μ t) + (x μ t - x μ' t) := by module
      rw [heq]
      calc
        ‖(y t - x μ t) + (x μ t - x μ' t)‖ ≤
            ‖y t - x μ t‖ + ‖x μ t - x μ' t‖ := norm_add_le _ _
        _ ≤ pathSupNorm T (fun s => y s - x μ s) +
            pathSupNorm T (fun s => x μ s - x μ' s) := by
          exact add_le_add
            (norm_le_pathSupNorm_of_continuousOn hyxcont ht)
            (norm_le_pathSupNorm_of_continuousOn hxxcont ht)
        _ ≤ (ε * α) / (α - α * γ * T - T ^ 2) +
            α / (α - α * γ * T - T ^ 2) *
              (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ +
                T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂) := add_le_add happ hparamBound
    · intro y' hy'
      refine ⟨x μ, hxmem, ?_⟩
      have happ := happBound ε μ' hμ' y' hy'
      have hparamBound := hcross μ hμ μ' hμ'
      have hxxcont : ContinuousOn (fun t => x μ t - x μ' t) (Set.Icc (0 : ℝ) T) :=
        (hxcont μ hμ).sub (hxcont μ' hμ')
      have hyxcont : ContinuousOn (fun t => y' t - x μ' t) (Set.Icc (0 : ℝ) T) :=
        hy'.1.sub (hxcont μ' hμ')
      apply pathSupNorm_le_of_forall hT.le
      intro t ht
      have heq : x μ t - y' t = (x μ t - x μ' t) - (y' t - x μ' t) := by module
      rw [heq]
      calc
        ‖(x μ t - x μ' t) - (y' t - x μ' t)‖ ≤
            ‖x μ t - x μ' t‖ + ‖y' t - x μ' t‖ := norm_sub_le _ _
        _ ≤ pathSupNorm T (fun s => x μ s - x μ' s) +
            pathSupNorm T (fun s => y' s - x μ' s) := by
          exact add_le_add
            (norm_le_pathSupNorm_of_continuousOn hxxcont ht)
            (norm_le_pathSupNorm_of_continuousOn hyxcont ht)
        _ ≤ α / (α - α * γ * T - T ^ 2) *
              (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ +
                T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂) +
            (ε * α) / (α - α * γ * T - T ^ 2) :=
          add_le_add hparamBound happ
        _ = (ε * α) / (α - α * γ * T - T ^ 2) +
            α / (α - α * γ * T - T ^ 2) *
              (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ +
                T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂) := add_comm _ _
  · intro μ hμ η hη
    let ε : ℝ := (η / 2) * ((α - α * γ * T - T ^ 2) / α)
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have happ := happBound ε μ hμ y hy
    have hhalf : (ε * α) / (α - α * γ * T - T ^ 2) = η / 2 := by
      dsimp [ε]
      calc
        ((η / 2 * ((α - α * γ * T - T ^ 2) / α)) * α) /
            (α - α * γ * T - T ^ 2) =
            ((η / 2) * (α - α * γ * T - T ^ 2)) /
              (α - α * γ * T - T ^ 2) := by
                rw [mul_assoc, div_mul_cancel₀ _ hα.ne']
        _ = η / 2 := mul_div_cancel_right₀ _ hdenom.ne'
    rw [hhalf] at happ
    linarith

/-! ### Remark 7.7: Painlevé–Kuratowski convergence of `S^ε(μ)`

The paper reads off from [4, Proposition 4(g)] (see `ext_thm_6`) that the set
`S^ε(μ)` of `ε`-approximate solutions converges to `{x_μ}` in the
Painlevé–Kuratowski sense as `ε → 0`: every sequence of approximate solutions
with `ε → 0` converges pointwise to the exact solution, and conversely the
exact solution is approached by approximate solutions.  Both directions are
proved here, the first with the quantitative rate `εα/(α-αγT-T²)` inherited
from the residual estimate. -/

/-- Every `ε`-approximate solution of `S(A_μ,u₀^μ,v₀^μ)` is within
  `εα/(α - αγT - T²)` of the exact solution `x_μ` in the sup norm — the
  residual estimate of Theorem 7.1's proof, now read as a statement about the
  approximate solution set `S^ε(μ)` of Definition 7.5. -/
theorem approxSolutions_pathSupNorm_le {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T ε : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun z : Set.univ => A μ z))
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hγT : γ * T + T ^ 2 / α < 1) {μ : M} (hμ : μ ∈ V) {y : ℝ → H}
    (hy : y ∈ approxSolutions A γ u₀ v₀ T ε μ) :
    pathSupNorm T (fun t => y t - x μ t) ≤ (ε * α) / (α - α * γ * T - T ^ 2) := by
  have hy' : ContinuousOn y (Set.Icc (0 : ℝ) T) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖y t - centeredIntegralMap (A μ) γ (u₀ μ) (v₀ μ) y t‖ ≤ ε := hy
  obtain ⟨hycont, hyres⟩ := hy'
  exact pathSupNorm_le_of_centeredIntegralMap_residual (A μ) (u₀ μ) (v₀ μ) (x μ) y
    α γ T ε hα hγ hT (hcoco μ hμ) (continuousOn_of_solution hT (hsol μ hμ).2) hycont
    (fun t ht => centeredIntegralMap_eq_of_solution (A μ) (x μ) (dx μ) (ddx μ) (u₀ μ) (v₀ μ)
      α γ (hcoco μ hμ) (hsol μ hμ) t ht.1)
    hyres hγT

/-- Remark 7.7 / [4, Proposition 4(g)]: Painlevé–Kuratowski convergence of the
  approximate solution set `S^ε(μ)` to the exact solution `x_μ` as `ε → 0`,
  under the conditions of Theorem 7.1.

  * every sequence `y_n ∈ S^{ε_n}(μ)` with `ε_n → 0` (and `ε_n > 0`) converges
    to `x_μ` pointwise on `[0,T]` — indeed uniformly, in the sup norm, with
    rate `ε_n α/(α-αγT-T²)`;
  * conversely, for every `η > 0` there is `ε > 0` such that every
    `S^{ε'}(μ)` with `0 < ε' < ε` contains a path within `η` of `x_μ` — the
    exact solution itself is an `ε`-approximate solution for every `ε ≥ 0`,
    so the exact solution is approached by approximate ones.

  Pointwise convergence is the form stated in the paper; the sup-norm (hence
  uniform) form is what the estimates actually give. -/
theorem approxSolutions_painleve_kuratowski {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun z : Set.univ => A μ z))
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hγT : γ * T + T ^ 2 / α < 1) :
    (∀ μ ∈ V, ∀ (εseq : ℕ → ℝ) (yseq : ℕ → ℝ → H), (∀ n, 0 < εseq n) →
        Tendsto εseq atTop (nhds 0) →
        (∀ n, yseq n ∈ approxSolutions A γ u₀ v₀ T (εseq n) μ) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => yseq n t) atTop (nhds (x μ t))) ∧
          Tendsto (fun n => pathSupNorm T (fun t => yseq n t - x μ t)) atTop (nhds 0)) ∧
      (∀ μ ∈ V, ∀ η > 0, ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε,
        ∃ y ∈ approxSolutions A γ u₀ v₀ T ε' μ,
          pathSupNorm T (fun t => y t - x μ t) < η) := by
  have hxcont (μ : M) (hμ : μ ∈ V) : ContinuousOn (x μ) (Set.Icc (0 : ℝ) T) :=
    continuousOn_of_solution hT (hsol μ hμ).2
  have hbound (μ : M) (hμ : μ ∈ V) (ε : ℝ) {y : ℝ → H}
      (hy : y ∈ approxSolutions A γ u₀ v₀ T ε μ) :
      pathSupNorm T (fun t => y t - x μ t) ≤ (ε * α) / (α - α * γ * T - T ^ 2) :=
    approxSolutions_pathSupNorm_le V A x dx ddx u₀ v₀ α γ T ε hα (hsol μ hμ).1 hT hcoco hsol
      hγT hμ hy
  constructor
  · intro μ hμ εseq yseq _ hlim hyseq
    have hsup (n : ℕ) : pathSupNorm T (fun t => yseq n t - x μ t) ≤
        (εseq n * α) / (α - α * γ * T - T ^ 2) := hbound μ hμ _ (hyseq n)
    have hcont (n : ℕ) : ContinuousOn (fun t => yseq n t - x μ t) (Set.Icc (0 : ℝ) T) :=
      (hyseq n).1.sub (hxcont μ hμ)
    have hlim' : Tendsto (fun n => (εseq n * α) / (α - α * γ * T - T ^ 2))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n => εseq n * α) atTop (nhds 0) := by
        simpa using hlim.mul_const α
      simpa using h1.div_const (α - α * γ * T - T ^ 2)
    refine ⟨?_, ?_⟩
    · intro t ht
      refine tendsto_iff_dist_tendsto_zero.mpr ?_
      have hb (n : ℕ) :
          dist (yseq n t) (x μ t) ≤ (εseq n * α) / (α - α * γ * T - T ^ 2) := by
        rw [dist_eq_norm]
        exact (norm_le_pathSupNorm_of_continuousOn (hcont n) ht).trans (hsup n)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
        (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall hb)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
        (Eventually.of_forall fun n => pathSupNorm_nonneg_of_continuousOn hT.le (hcont n))
        (Eventually.of_forall hsup)
  · intro μ hμ η hη
    refine ⟨η, hη, ?_⟩
    intro ε' hε'
    refine ⟨x μ, ?_, ?_⟩
    · refine ⟨hxcont μ hμ, ?_⟩
      intro t ht
      have hfix := centeredIntegralMap_eq_of_solution (A μ) (x μ) (dx μ) (ddx μ)
        (u₀ μ) (v₀ μ) α γ (hcoco μ hμ) (hsol μ hμ) t ht.1
      rw [hfix, sub_self, norm_zero]
      exact hε'.1.le
    · have hzero : pathSupNorm T (fun t => x μ t - x μ t) ≤ η / 2 :=
        pathSupNorm_le_of_forall hT.le fun t _ => by rw [sub_self, norm_zero]; positivity
      linarith

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
