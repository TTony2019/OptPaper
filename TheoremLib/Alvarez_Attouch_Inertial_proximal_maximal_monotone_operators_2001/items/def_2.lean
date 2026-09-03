import Mathlib.Tactic
import Foundation.SetValued.Resolvent
import Foundation.SetValued.Minty
import Foundation.SetValued.Resolvent
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_1

/-! The resolvent is the canonical inverse of `I + lambda A`. -/

recall SetValuedOperator.resolvent

/-! Positive scalar multiples preserve maximal monotonicity; supplied
canonically by Foundation. -/
recall SetValuedOperator.positive_scaled_maximal_monotone

namespace AlvarezAttouch2001

open SetValuedOperator
open scoped Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem identityAddScaled_existsUnique_of_maximal_monotone
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    {lambda : ℝ} (hlambda : 0 < lambda) (u : H) :
    ∃! z : H, u ∈ A.identityAddScaled lambda z := by
  rcases minty_surjective_of_maximal_monotone
      (T := fun z : H => lambda • A z) (SetValuedOperator.positive_scaled_maximal_monotone hA hlambda) u with
    ⟨z, b, hb, hub⟩
  rcases hb with ⟨a, ha, rfl⟩
  refine ⟨z, ⟨a, ha, hub.symm⟩, ?_⟩
  intro w hw
  rcases hw with ⟨c, hc, huw⟩
  have hdiff : z - w = (-lambda) • (a - c) := by
    calc
      z - w = (z + lambda • a) - (w + lambda • c) + (-lambda) • (a - c) := by module
      _ = u - u + (-lambda) • (a - c) := by rw [← hub, ← huw]
      _ = (-lambda) • (a - c) := by module
  have hmono : 0 ≤ inner ℝ (a - c) (z - w) := hA.1 a ha c hc
  have hsq : ‖z - w‖ ^ 2 = (-lambda) * inner ℝ (a - c) (z - w) := by
    calc
      ‖z - w‖ ^ 2 = inner ℝ (z - w) (z - w) := by simp
      _ = inner ℝ ((-lambda) • (a - c)) (z - w) := by rw [← hdiff]
      _ = (-lambda) * inner ℝ (a - c) (z - w) := by rw [real_inner_smul_left]
  have hsq_nonpos : ‖z - w‖ ^ 2 ≤ 0 := by
    rw [hsq]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda.le) hmono
  have hnorm : ‖z - w‖ = 0 := by nlinarith [sq_nonneg ‖z - w‖]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

omit [CompleteSpace H] in
theorem resolvent_selection_lipschitz
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    {lambda : ℝ} (hlambda : 0 < lambda) (J : H → H)
    (hJ : ∀ u : H, J u ∈ J[(lambda • A)] u) : LipschitzWith 1 J := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro u v
  have hu : u ∈ A.identityAddScaled lambda (J u) := by
    exact (mem_resolvent_smul_iff A lambda u (J u)).mp (hJ u)
  have hv : v ∈ A.identityAddScaled lambda (J v) := by
    exact (mem_resolvent_smul_iff A lambda v (J v)).mp (hJ v)
  rcases hu with ⟨a, ha, hua⟩
  rcases hv with ⟨b, hb, hvb⟩
  have hdiff : u - v = (J u - J v) + lambda • (a - b) := by
    calc
      u - v = (J u + lambda • a) - v := congrArg (· - v) hua.symm
      _ = (J u + lambda • a) - (J v + lambda • b) := congrArg ((J u + lambda • a) - ·) hvb.symm
      _ = (J u - J v) + (lambda • a - lambda • b) := by abel
      _ = (J u - J v) + lambda • (a - b) := by rw [smul_sub]
  have hfirm : ‖J u - J v‖ ^ 2 ≤ inner ℝ (J u - J v) (u - v) := by
    rw [hdiff, inner_add_right, real_inner_smul_right]
    have hmono : 0 ≤ inner ℝ (J u - J v) (a - b) := by
      have h := hA.1 a ha b hb
      rwa [real_inner_comm] at h
    have hself : inner ℝ (J u - J v) (J u - J v) = ‖J u - J v‖ ^ 2 := by simp
    rw [hself]
    nlinarith [mul_nonneg hlambda.le hmono]
  have hcauchy : inner ℝ (J u - J v) (u - v) ≤ ‖J u - J v‖ * ‖u - v‖ :=
    real_inner_le_norm _ _
  have hsq_le : ‖J u - J v‖ ^ 2 ≤ ‖J u - J v‖ * ‖u - v‖ := hfirm.trans hcauchy
  have hnorm : ‖J u - J v‖ ≤ ‖u - v‖ := by
    by_cases hzero : ‖J u - J v‖ = 0
    · rw [hzero]
      exact norm_nonneg _
    · have hpos : 0 < ‖J u - J v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  simpa [dist_eq_norm, mul_comm] using hnorm

/-- A positive resolvent of a maximal monotone operator is everywhere uniquely defined,
nonexpansive, and has precisely the zeros of the operator as fixed points. -/
theorem resolvent_of_maximal_monotone
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∀ u : H, ∃! z : H, u ∈ A.identityAddScaled lambda z) ∧
      ∃ J : H → H, (∀ u : H, J u ∈ J[(lambda • A)] u) ∧
        LipschitzWith 1 J ∧ ∀ z : H, J z = z ↔ 0 ∈ A z := by
  classical
  have hunique : ∀ u : H, ∃! z : H, u ∈ A.identityAddScaled lambda z :=
    fun u => identityAddScaled_existsUnique_of_maximal_monotone A hA hlambda u
  let J : H → H := fun u => Classical.choose (hunique u)
  have hJ_identity : ∀ u : H, u ∈ A.identityAddScaled lambda (J u) := by
    intro u
    exact (Classical.choose_spec (hunique u)).1
  have hJ : ∀ u : H, J u ∈ J[(lambda • A)] u := by
    intro u
    exact (mem_resolvent_smul_iff A lambda u (J u)).mpr (hJ_identity u)
  refine ⟨hunique, J, hJ, resolvent_selection_lipschitz A hA hlambda J hJ, ?_⟩
  intro z
  constructor
  · intro hfix
    rcases hJ_identity z with ⟨a, ha, hza⟩
    have hscaled : lambda • a = 0 := by
      rw [hfix] at hza ha
      apply add_left_cancel (a := z)
      simpa using hza.symm
    have ha_zero : a = 0 := (smul_eq_zero.mp hscaled).resolve_left hlambda.ne'
    simpa [hfix, ha_zero] using ha
  · intro hzero
    have hz : z ∈ A.identityAddScaled lambda z := ⟨0, hzero, by simp⟩
    exact (hunique z).unique (hJ_identity z) hz

end AlvarezAttouch2001
