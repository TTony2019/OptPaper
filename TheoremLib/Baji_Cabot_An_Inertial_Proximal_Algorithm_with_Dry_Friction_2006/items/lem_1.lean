import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_5
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_1
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_4
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_prop_1

/-!
# Lemma 2.1
Let $A: H \Rightarrow H$ be a monotone operator such that $\operatorname{dom} A = H$
and $0 \in A(0)$. The function $\Phi_A$ defined by (3) satisfies:
(i) $\forall x \in H$, $\Phi_A(x) \geqslant \sigma_{A(0)}(x) \geqslant 0$.
(ii) $0 \in \operatorname{int}(A(0)) \Rightarrow \exists \alpha > 0$,
$\forall x \in H$, $\Phi_A(x) \geqslant \alpha |x|$.
-/
open SetValuedOperator
open Set
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- Lemma 2.1: properties of the function Φ_A. -/
theorem lem_2_1 (A : SetValuedOperator H H) (h_mono : IsMonotone A) (_h_dom : A.dom = Set.univ)
    (h_zero : (0 : H) ∈ A (0 : H)) :
    (∀ x,
      PhiA A x ≥ supportFunction (A (0 : H)) x ∧
        supportFunction (A (0 : H)) x ≥ 0) ∧
    ((0 : H) ∈ interior (A (0 : H)) →
      ∃ (α : ℝ), α > 0 ∧ ∀ x, PhiA A x ≥ ((α * ‖x‖ : ℝ) : EReal)) := by
  have hPhi_ge_support : ∀ x, supportFunction (A (0 : H)) x ≤ PhiA A x := by
    intro x
    rw [PhiA, supportFunction]
    refine sSup_le ?_
    rintro _ ⟨z, hz, rfl⟩
    refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    have hle : inner ℝ z x ≤ inner ℝ y x := by
      simpa [inner_sub_left, sub_zero] using h_mono y hy z hz
    exact EReal.coe_le_coe hle
  have hSupport_nonneg : ∀ x, (0 : EReal) ≤ supportFunction (A (0 : H)) x := by
    intro x
    rw [supportFunction]
    exact le_sSup ⟨0, h_zero, by simp⟩
  constructor
  · intro x
    exact ⟨hPhi_ge_support x, hSupport_nonneg x⟩
  · intro h_int
    rcases (Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h_int)) with
      ⟨ε, hε_pos, hε_subset⟩
    let α : ℝ := ε / 2
    have hα_pos : 0 < α := by positivity
    have hα_lt_ε : α < ε := by
      dsimp [α]
      linarith
    refine ⟨α, hα_pos, ?_⟩
    intro x
    have hsupp_lower : ((α * ‖x‖ : ℝ) : EReal) ≤ supportFunction (A (0 : H)) x := by
      by_cases hx : x = 0
      · subst x
        simpa using hSupport_nonneg (0 : H)
      · have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let z : H := (α / ‖x‖) • x
        have hz_norm : ‖z‖ = α := by
          dsimp [z]
          rw [norm_smul]
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (le_of_lt hα_pos) (le_of_lt hxnorm_pos))]
          field_simp [ne_of_gt hxnorm_pos]
        have hz_ball : z ∈ Metric.ball (0 : H) ε := by
          simpa [Metric.mem_ball, dist_zero_right, hz_norm] using hα_lt_ε
        have hinner_z : inner ℝ z x = α * ‖x‖ := by
          dsimp [z]
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
          field_simp [ne_of_gt hxnorm_pos]
        rw [supportFunction]
        have hle_sup : ((inner ℝ z x : ℝ) : EReal) ≤
            sSup ((fun z : H => (inner ℝ z x : EReal)) '' A (0 : H)) := by
          exact le_sSup ⟨z, hε_subset hz_ball, rfl⟩
        simpa [hinner_z] using hle_sup
    exact le_trans hsupp_lower (hPhi_ge_support x)
