import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_1
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_4
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.ext_def_1
import Foundation.SetValued.Resolvent
import Foundation.FixedPoint.Nonexpansive

/-! Nonexpansiveness of the forward--backward operator (López et al.). -/

open SetValuedOperator
open scoped Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem forward_backward_nonexpansive_and_fixedPoints (A : H → H) (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (alpha eps : ℝ) (heps : 0 < eps) (hepsAlpha : eps ≤ 2 * alpha)
    (hA : CocoerciveOn alpha Set.univ (fun x : Set.univ ↦ A x)) (T : H → H)
    (hT : ∀ x, T x ∈ J[(eps • B)] (x - eps • A x)) :
    LipschitzWith 1 T ∧ Function.fixedPoints T = operatorSumZeroSet A B := by
  have resolvent_mem_iff_exists_graph_witness {a p : H} :
      p ∈ J[(eps • B)] a ↔ ∃ b ∈ B p, a = p + eps • b := by
    rw [mem_resolvent_smul_iff]
    dsimp [SetValuedOperator.identityAddScaled]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  have resolvent_nonexpansive {a b p q : H}
      (hp : p ∈ J[(eps • B)] a) (hq : q ∈ J[(eps • B)] b) :
      ‖p - q‖ ≤ ‖a - b‖ := by
    rcases resolvent_mem_iff_exists_graph_witness.mp hp with ⟨u, hu, hpa⟩
    rcases resolvent_mem_iff_exists_graph_witness.mp hq with ⟨v, hv, hqb⟩
    have hab : a - b = (p - q) + eps • (u - v) := by
      rw [hpa, hqb, smul_sub]
      abel
    have hfirm : ‖p - q‖ ^ 2 ≤ inner ℝ (p - q) (a - b) := by
      rw [hab, inner_add_right, real_inner_smul_right]
      have hmono : 0 ≤ inner ℝ (p - q) (u - v) := by
        simpa [real_inner_comm] using hB.1 u hu v hv
      simp only [real_inner_self_eq_norm_sq]
      nlinarith [mul_nonneg heps.le hmono]
    have hcauchy : inner ℝ (p - q) (a - b) ≤ ‖p - q‖ * ‖a - b‖ :=
      real_inner_le_norm _ _
    have hsq : ‖p - q‖ ^ 2 ≤ ‖p - q‖ * ‖a - b‖ := hfirm.trans hcauchy
    by_cases hzero : ‖p - q‖ = 0
    · simp [hzero]
    · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  have forward_nonexpansive (x y : H) :
      ‖(x - eps • A x) - (y - eps • A y)‖ ≤ ‖x - y‖ := by
    have hvec : (x - eps • A x) - (y - eps • A y) =
        (x - y) - eps • (A x - A y) := by
      module
    have hsquare : ‖(x - eps • A x) - (y - eps • A y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [hvec, norm_sub_sq_real]
      simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg heps.le]
      nlinarith [hA.ineq ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩,
        mul_nonneg heps.le (sub_nonneg.mpr hepsAlpha),
        sq_nonneg ‖A x - A y‖]
    nlinarith [norm_nonneg ((x - eps • A x) - (y - eps • A y)), norm_nonneg (x - y)]
  have hLip : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [dist_eq_norm] using
      (resolvent_nonexpansive (hT x) (hT y)).trans (forward_nonexpansive x y)
  refine ⟨hLip, ?_⟩
  ext x
  constructor
  · intro hx
    have hfix : T x = x := by
      simpa [Function.mem_fixedPoints, Function.IsFixedPt] using hx
    rcases resolvent_mem_iff_exists_graph_witness.mp (hT x) with ⟨b, hb, heq⟩
    have hbneg : b = -A x := by
      have heq' : x - eps • A x = x + eps • b := by simpa [hfix] using heq
      have hsmul : eps • b = eps • (-A x) := by
        calc
          eps • b = (x + eps • b) - x := by abel
          _ = (x - eps • A x) - x := by rw [← heq']
          _ = eps • (-A x) := by module
      exact smul_right_injective H heps.ne' (by simpa using hsmul)
    change (0 : H) ∈ operatorSum A B x
    refine ⟨-A x, ?_, by simp⟩
    simpa [hfix, hbneg] using hb
  · intro hx
    change (0 : H) ∈ operatorSum A B x at hx
    rcases hx with ⟨b, hb, hsum⟩
    have hbneg : b = -A x := by
      apply eq_neg_of_add_eq_zero_right
      simpa using hsum.symm
    have hself : x ∈ J[(eps • B)] (x - eps • A x) := by
      apply resolvent_mem_iff_exists_graph_witness.mpr
      refine ⟨b, hb, ?_⟩
      rw [hbneg]
      module
    have htx : T x = x := by
      have : ‖T x - x‖ = 0 := by simpa using resolvent_nonexpansive (hT x) hself
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    simpa [Function.mem_fixedPoints, Function.IsFixedPt] using htx
