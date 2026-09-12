import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_4
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.ext_def_1
import Foundation.SetValued.Resolvent
import Foundation.FixedPoint.Nonexpansive

/-! Forward--backward splitting lemma of López--Martín-Márquez--Wang--Xu. -/

open SetValuedOperator
open scoped Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A single-valued realization of `J_(r B) ∘ (I - r A)`. -/
def IsForwardBackwardSelection (A : H → H) (B : SetValuedOperator H H) (r : ℝ)
    (T : H → H) : Prop :=
  ∀ x, T x ∈ J[(r • B)] (x - r • A x)

/-- A positive-parameter resolvent of a monotone operator is single-valued. -/
theorem resolvent_unique_of_monotone {B : SetValuedOperator H H} (hB : B.IsMonotone)
    {r : ℝ} (hr : 0 < r) {y u v : H}
    (hu : u ∈ J[(r • B)] y) (hv : v ∈ J[(r • B)] y) : u = v := by
  rw [mem_resolvent_smul_iff] at hu hv
  dsimp [SetValuedOperator.identityAddScaled] at hu hv
  rcases hu with ⟨bu, hbu, hyu⟩
  rcases hv with ⟨bv, hbv, hyv⟩
  have huv : u - v = r • (bv - bu) := by
    calc
      u - v = (u + r • bu) - r • bu - ((v + r • bv) - r • bv) := by abel
      _ = (y - r • bu) - (y - r • bv) := by rw [hyu, hyv]
      _ = r • (bv - bu) := by rw [smul_sub]; abel
  have hmono : 0 ≤ inner ℝ (bu - bv) (u - v) := hB bu hbu bv hbv
  rw [huv, real_inner_smul_right] at hmono
  have hinner : inner ℝ (bu - bv) (bv - bu) = -‖bu - bv‖ ^ 2 := by
    have hneg : bv - bu = -(bu - bv) := by abel
    rw [hneg, inner_neg_right]
    simp
  rw [hinner] at hmono
  have hsq : ‖bu - bv‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg (‖bu - bv‖)]
  have hbeq : bu = bv := by
    have hnorm : ‖bu - bv‖ = 0 := by
      nlinarith [norm_nonneg (bu - bv)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact sub_eq_zero.mp (by simpa [hbeq] using huv)

theorem forward_backward_fixedPoints_and_residual_bound (A : H → H) (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (alpha : ℝ)
    (hA : CocoerciveOn alpha Set.univ (fun x : Set.univ ↦ A x))
    (r s : ℝ) (hs : 0 < s) (hsr : s ≤ r) (Tr Ts : H → H)
    (hTr : IsForwardBackwardSelection A B r Tr) (hTs : IsForwardBackwardSelection A B s Ts) :
    Function.fixedPoints Tr = operatorSumZeroSet A B ∧
      ∀ x, ‖x - Ts x‖ ≤ 2 * ‖x - Tr x‖ := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  constructor
  · apply Set.Subset.antisymm
    · intro x hx
      have hfix : Tr x = x := hx
      have hres := hTr x
      rw [mem_resolvent_smul_iff] at hres
      dsimp [SetValuedOperator.identityAddScaled] at hres
      rcases hres with ⟨b, hb, heq⟩
      rw [hfix] at heq
      have hb' : b = -A x := by
        have hscaled : r • b = r • (-A x) := by
          calc
            r • b = (x + r • b) - x := by abel
            _ = (x - r • A x) - x := by rw [heq]
            _ = r • (-A x) := by rw [smul_neg]; abel
        apply sub_eq_zero.mp
        apply (smul_eq_zero.mp ?_).resolve_left hr.ne'
        rw [smul_sub]
        exact sub_eq_zero.mpr hscaled
      rw [operatorSumZeroSet, SetValuedOperator.mem_zeros_iff]
      refine ⟨b, by simpa [hfix] using hb, ?_⟩
      rw [hb']
      abel
    · intro x hx
      rw [operatorSumZeroSet, SetValuedOperator.mem_zeros_iff] at hx
      rcases hx with ⟨b, hb, hzero⟩
      have hbneg : b = -A x := by
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hzero.symm)
      have hxres : x ∈ J[(r • B)] (x - r • A x) := by
        rw [mem_resolvent_smul_iff]
        dsimp [SetValuedOperator.identityAddScaled]
        refine ⟨b, hb, ?_⟩
        rw [hbneg, smul_neg]
        abel
      exact _root_.resolvent_unique_of_monotone hB.1 hr (hTr x) hxres
  · intro x
    have hpr := hTr x
    have hqs := hTs x
    rw [mem_resolvent_smul_iff] at hpr hqs
    dsimp [SetValuedOperator.identityAddScaled] at hpr hqs
    rcases hpr with ⟨bp, hbp, hpeq⟩
    rcases hqs with ⟨bq, hbq, hqeq⟩
    let a : H := x - Ts x
    let b : H := x - Tr x
    have hrbp : r • bp = b - r • A x := by
      dsimp [b]
      calc
        r • bp = (Tr x + r • bp) - Tr x := by abel
        _ = (x - r • A x) - Tr x := by rw [hpeq]
        _ = x - Tr x - r • A x := by abel
    have hsbq : s • bq = a - s • A x := by
      dsimp [a]
      calc
        s • bq = (Ts x + s • bq) - Ts x := by abel
        _ = (x - s • A x) - Ts x := by rw [hqeq]
        _ = x - Ts x - s • A x := by abel
    have hpq : Tr x - Ts x = a - b := by
      dsimp [a, b]
      abel
    have hscaled : (r * s) • (bp - bq) = s • b - r • a := by
      calc
        (r * s) • (bp - bq) = s • (r • bp) - r • (s • bq) := by module
        _ = s • (b - r • A x) - r • (a - s • A x) := by rw [hrbp, hsbq]
        _ = s • b - r • a := by module
    have hmono : 0 ≤ inner ℝ (bp - bq) (Tr x - Ts x) := hB.1 bp hbp bq hbq
    have hmul : 0 ≤ (r * s) * inner ℝ (bp - bq) (Tr x - Ts x) :=
      mul_nonneg (mul_nonneg (le_of_lt hr) (le_of_lt hs)) hmono
    have hid : (r * s) * inner ℝ (bp - bq) (Tr x - Ts x) =
        (r + s) * inner ℝ a b - s * ‖b‖ ^ 2 - r * ‖a‖ ^ 2 := by
      rw [← real_inner_smul_left, hscaled, hpq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      rw [real_inner_comm b a]
      ring
    have hquad : r * ‖a‖ ^ 2 + s * ‖b‖ ^ 2 ≤ (r + s) * inner ℝ a b := by
      rw [hid] at hmul
      linarith
    have hcs : inner ℝ a b ≤ ‖a‖ * ‖b‖ := real_inner_le_norm a b
    have hrs : r + s ≤ 2 * r := by linarith
    have hbound : r * ‖a‖ ^ 2 ≤ 2 * r * ‖a‖ * ‖b‖ := by
      have hleft : r * ‖a‖ ^ 2 ≤ (r + s) * inner ℝ a b := by
        nlinarith [mul_nonneg (le_of_lt hs) (sq_nonneg ‖b‖)]
      have hright : (r + s) * inner ℝ a b ≤ 2 * r * ‖a‖ * ‖b‖ := by
        have hcoef : 0 ≤ r + s := by linarith
        have hprod : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hcs' := mul_le_mul_of_nonneg_left hcs hcoef
        have hrs' := mul_le_mul_of_nonneg_right hrs hprod
        nlinarith
      exact hleft.trans hright
    by_cases ha : ‖a‖ = 0
    · rw [ha]
      positivity
    · have hapos : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha)
      have hfac : 0 < r * ‖a‖ := mul_pos hr hapos
      have hmul : (r * ‖a‖) * ‖a‖ ≤ (r * ‖a‖) * (2 * ‖b‖) := by
       calc
        (r * ‖a‖) * ‖a‖ = r * ‖a‖ ^ 2 := by ring
        _ ≤ 2 * r * ‖a‖ * ‖b‖ := hbound
        _ = (r * ‖a‖) * (2 * ‖b‖) := by ring
      exact le_of_mul_le_mul_left hmul hfac
