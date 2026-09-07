import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_def_1

open MeasureTheory

/-- Integral Jensen inequality for a convex differentiable objective. -/
theorem integral_jensen_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (F : ConvexDifferentiableObjective H) (a b : ℝ) (g : ℝ → H)
    (hab : a < b) (hg : IntervalIntegrable g volume a b)
    (hFg : IntervalIntegrable (F.f ∘ g) volume a b) :
    F.f ((b - a)⁻¹ • ∫ s in a..b, g s) ≤
      (b - a)⁻¹ * ∫ s in a..b, F.f (g s) := by
  let m : H := (b - a)⁻¹ • ∫ s in a..b, g s
  have hlen_pos : 0 < b - a := sub_pos.mpr hab
  have hlen_ne : b - a ≠ 0 := ne_of_gt hlen_pos
  have hab_le : a ≤ b := hab.le
  have hgI : IntegrableOn g (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp hg
  have hFgI : IntegrableOn (F.f ∘ g) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp hFg
  have hIoc_ne_top : volume (Set.Ioc a b) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hconstH : IntegrableOn (fun _ : ℝ => m) (Set.Ioc a b) volume :=
    integrableOn_const (hs := hIoc_ne_top)
  have hsubI : IntegrableOn (fun s => g s - m) (Set.Ioc a b) volume := hgI.sub hconstH
  have hinnerI : IntegrableOn (fun s => inner ℝ (gradient F.f m) (g s - m)) (Set.Ioc a b) volume :=
    (hsubI.const_inner (gradient F.f m))
  have hconstR : IntegrableOn (fun _ : ℝ => F.f m) (Set.Ioc a b) volume :=
    integrableOn_const (hs := hIoc_ne_top)
  have hleftI : IntegrableOn (fun s => F.f m + inner ℝ (gradient F.f m) (g s - m))
      (Set.Ioc a b) volume := hconstR.add hinnerI
  have hpoint : ∀ s : ℝ, F.f m + inner ℝ (gradient F.f m) (g s - m) ≤ F.f (g s) := by
    intro s
    exact F.firstOrder m (g s)
  have hmono : ∫ s in Set.Ioc a b, F.f m + inner ℝ (gradient F.f m) (g s - m) ≤
      ∫ s in Set.Ioc a b, F.f (g s) :=
    integral_mono hleftI hFgI hpoint
  have hsub_integral : ∫ s in Set.Ioc a b, g s - m =
      (∫ s in Set.Ioc a b, g s) - ∫ _ in Set.Ioc a b, m :=
    integral_sub hgI hconstH
  have hinner_integral : ∫ s in Set.Ioc a b, inner ℝ (gradient F.f m) (g s - m) =
      inner ℝ (gradient F.f m) (∫ s in Set.Ioc a b, g s - m) :=
    integral_inner hsubI (gradient F.f m)
  have hconstR_integral : ∫ _ in Set.Ioc a b, F.f m = (b - a) * F.f m := by
    rw [← intervalIntegral.integral_of_le hab_le, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hconstH_integral : ∫ _ in Set.Ioc a b, m = (b - a) • m := by
    rw [← intervalIntegral.integral_of_le hab_le, intervalIntegral.integral_const]
  have hleft_calc : ∫ s in Set.Ioc a b, F.f m + inner ℝ (gradient F.f m) (g s - m) =
      (b - a) * F.f m +
        inner ℝ (gradient F.f m) ((∫ s in Set.Ioc a b, g s) - (b - a) • m) := by
    rw [integral_add hconstR hinnerI, hinner_integral, hsub_integral,
      hconstR_integral, hconstH_integral]
  have hrem : inner ℝ (gradient F.f m) ((∫ s in Set.Ioc a b, g s) - (b - a) • m) = 0 := by
    dsimp [m]
    rw [← intervalIntegral.integral_of_le hab_le]
    rw [smul_smul]
    simp [mul_inv_cancel₀ hlen_ne]
  have hraw : (b - a) * F.f m ≤ ∫ s in Set.Ioc a b, F.f (g s) := by
    rw [hleft_calc, hrem, add_zero] at hmono
    exact hmono
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hlen_pos.le)
  rw [← intervalIntegral.integral_of_le hab_le] at hscaled
  have hfinal : F.f m ≤ (b - a)⁻¹ * ∫ s in a..b, F.f (g s) := by
    convert hscaled using 1
    all_goals field_simp [hlen_ne]
  simpa [m] using hfinal
