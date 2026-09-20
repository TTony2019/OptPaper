import Foundation.SetValued.Resolvent
import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.thm_1
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_2
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_4
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.ext_def_1
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.ext_lem_2
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.ext_thm_1
import Foundation.SetValued.Minty

/-! Corollary 3.3: the inertial proximal-point specialization. -/

open Filter SetValuedOperator
open scoped Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The resolvent of a maximal monotone operator is Fejér monotone with
respect to its zeros.  This is the `A = 0` part of the calculation used in
Theorem 3.2. -/
private theorem proximal_fejer_sq (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (alg : InertialForwardBackward (fun _ : H ↦ 0) B)
    (n : ℕ) (hn : 1 ≤ n) (u : H) (hu : u ∈ B.zeros) :
    ‖alg.z n - u‖ ^ 2 ≤ ‖alg.y n - u‖ ^ 2 := by
  let r := alg.stepSize n
  have hr : 0 < r := by simpa [r] using alg.stepSize_pos n hn
  have hru : u ∈ ((r : ℝ) • B).resolvent u := by
    rw [SetValuedOperator.mem_resolvent_smul_iff]
    dsimp [SetValuedOperator.identityAddScaled]
    refine ⟨0, hu, ?_⟩
    simp
  have hrz : alg.z n ∈ ((r : ℝ) • B).resolvent (alg.y n) := by
    simpa [r] using alg.resolvent_step n hn
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hrz hru
  dsimp [SetValuedOperator.identityAddScaled] at hrz hru
  rcases hrz with ⟨bz, hbz, heqz⟩
  rcases hru with ⟨bu, hbu, hequ⟩
  have hdiff : alg.y n - u = (alg.z n - u) + r • (bz - bu) := by
    calc
      alg.y n - u = (alg.z n + r • bz) - (u + r • bu) := by rw [heqz, hequ]
      _ = (alg.z n - u) + r • (bz - bu) := by rw [smul_sub]; abel
  have hmono : 0 ≤ inner ℝ (alg.z n - u) (bz - bu) := by
    simpa [real_inner_comm] using hB.1 bz hbz bu hbu
  have hfirm : ‖alg.z n - u‖ ^ 2 ≤ inner ℝ (alg.z n - u) (alg.y n - u) := by
    rw [hdiff, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg hr.le hmono]
  have hcs : inner ℝ (alg.z n - u) (alg.y n - u) ≤
      ‖alg.z n - u‖ * ‖alg.y n - u‖ := real_inner_le_norm _ _
  have hnorm : ‖alg.z n - u‖ ≤ ‖alg.y n - u‖ := by
    by_cases hz : ‖alg.z n - u‖ = 0
    · simp [hz]
    · have hzpos : 0 < ‖alg.z n - u‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith [hfirm.trans hcs]
  nlinarith [norm_nonneg (alg.z n - u), norm_nonneg (alg.y n - u)]

private theorem zeros_subset_inertialForwardBackwardC_proximal
    (B : SetValuedOperator H H) (hB : B.IsMaximalMonotone)
    (alg : InertialForwardBackward (fun _ : H ↦ 0) B) (n : ℕ) (hn : 1 ≤ n) :
    B.zeros ⊆ inertialForwardBackwardC alg.x alg.z alg.inertia n := by
  intro u hu
  have hfejer := proximal_fejer_sq B hB alg n hn u hu
  have hy : alg.y n - u =
      (alg.x n - u) - alg.inertia n • (alg.x (n - 1) - alg.x n) := by
    rw [alg.inertial_step n hn]
    module
  have hsq : ‖alg.y n - u‖ ^ 2 = ‖alg.x n - u‖ ^ 2 -
      2 * alg.inertia n * inner ℝ (alg.x n - u) (alg.x (n - 1) - alg.x n) +
        alg.inertia n ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2 := by
    rw [hy, norm_sub_sq_real]
    simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    nlinarith [sq_abs (alg.inertia n)]
  simpa [inertialForwardBackwardC, Nat.ne_of_gt hn, hsq] using hfejer

private theorem zero_cocoerciveOn (β : ℝ) (hβ : 0 < β) :
    CocoerciveOn β Set.univ (fun _ : Set.univ ↦ (0 : H)) := by
  refine ⟨hβ, fun x y => ?_⟩
  simp

/-- The half-space `Qₙ` is closed and convex. -/
private theorem inertialForwardBackwardQ_isClosed_convex_proximal
    (x : ℕ → H) (x0 : H) (n : ℕ) :
    IsClosed (inertialForwardBackwardQ x x0 n) ∧
      Convex ℝ (inertialForwardBackwardQ x x0 n) := by
  let d : H := x0 - x n
  let b : ℝ := inner ℝ (x n) d
  have hset : inertialForwardBackwardQ x x0 n = {u | inner ℝ d u ≤ b} := by
    ext u
    simp only [inertialForwardBackwardQ, Set.mem_setOf_eq]
    dsimp [d, b]
    rw [inner_sub_left, real_inner_comm d u]
    constructor <;> intro hu <;> linarith
  rw [hset]
  constructor
  · exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  · simpa [Set.preimage, innerSL_apply_apply] using
      (convex_Iic b).is_linear_preimage (innerSL ℝ d).isLinear

/-- The proximal constraint `Cₙ` is a closed convex squared-distance half-space. -/
private theorem inertialForwardBackwardC_isClosed_convex_proximal
    (B : SetValuedOperator H H) (alg : InertialForwardBackward (fun _ : H ↦ 0) B) (n : ℕ) :
    IsClosed (inertialForwardBackwardC alg.x alg.z alg.inertia n) ∧
      Convex ℝ (inertialForwardBackwardC alg.x alg.z alg.inertia n) := by
  by_cases hn : n = 0
  · subst n
    change IsClosed (Set.univ : Set H) ∧ Convex ℝ (Set.univ : Set H)
    exact ⟨isClosed_univ, convex_univ⟩
  let t : ℝ := alg.inertia n
  let d : H := alg.x (n - 1) - alg.x n
  let a : ℝ := -2 * t * inner ℝ (alg.x n) d + t ^ 2 * ‖d‖ ^ 2
  have hconstraint := squared_distance_constraint_isClosed_convex
    (C := Set.univ) isClosed_univ convex_univ (alg.x n) (alg.z n) ((2 * t) • d) a
  have hset : {v ∈ (Set.univ : Set H) |
      ‖alg.z n - v‖ ^ 2 ≤ ‖alg.x n - v‖ ^ 2 + inner ℝ ((2 * t) • d) v + a} =
      inertialForwardBackwardC alg.x alg.z alg.inertia n := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, inertialForwardBackwardC, hn]
    dsimp [t, d, a]
    simp only [real_inner_smul_right, inner_sub_left, real_inner_comm]
    ring_nf
  rw [hset] at hconstraint
  exact hconstraint

/-- The defining inertial constraint is controlled by a bound on the
inertial coefficient. -/
private theorem inertial_residual_sq_le_of_abs_inertia
    {a M : ℝ} {r v w : H} (hM : |a| ≤ M)
    (h : ‖r‖ ^ 2 ≤ ‖v‖ ^ 2 - 2 * a * inner ℝ v w + a ^ 2 * ‖w‖ ^ 2) :
    ‖r‖ ^ 2 ≤ ‖v‖ ^ 2 + 2 * M * ‖v‖ * ‖w‖ + M ^ 2 * ‖w‖ ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) hM
  have hcross : -2 * a * inner ℝ v w ≤ 2 * M * ‖v‖ * ‖w‖ := by
    have haux : -a * inner ℝ v w ≤ |a| * |inner ℝ v w| := by
      calc
        -a * inner ℝ v w = -(a * inner ℝ v w) := by ring
        _ ≤ |a * inner ℝ v w| := neg_le_abs _
        _ = |a| * |inner ℝ v w| := abs_mul _ _
    have haux' : -2 * a * inner ℝ v w ≤ 2 * (|a| * |inner ℝ v w|) := by
      nlinarith
    have hprod : |a| * |inner ℝ v w| ≤ M * (‖v‖ * ‖w‖) := by
      calc
        |a| * |inner ℝ v w| ≤ M * |inner ℝ v w| :=
          mul_le_mul_of_nonneg_right hM (abs_nonneg _)
        _ ≤ M * (‖v‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hM0
    calc
      -2 * a * inner ℝ v w ≤ 2 * (|a| * |inner ℝ v w|) := haux'
      _ ≤ 2 * (M * (‖v‖ * ‖w‖)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 2 * M * ‖v‖ * ‖w‖ := by ring
  have ha2 : a ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hM0).mpr hM
  have hlast : a ^ 2 * ‖w‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
  nlinarith

private theorem positive_scale_maximal_monotone {A : SetValuedOperator H H}
    (hA : SetValuedOperator.IsMaximalMonotone A) {c : ℝ} (hc : 0 < c) :
    SetValuedOperator.IsMaximalMonotone (fun x : H ↦ c • A x) := by
  let S : SetValuedOperator H H := fun x : H => c • A x
  have hS_mono : SetValuedOperator.IsMonotone S := by
    intro x y u hu v hv
    dsimp [S] at hu hv
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨b, hb, rfl⟩
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg hc.le (hA.1 a ha b hb)
  refine ⟨hS_mono, ?_⟩
  intro B hB_mono hsubset p hp
  rcases p with ⟨x, u⟩
  change u ∈ B x at hp
  let C : SetValuedOperator H H := fun z : H => c⁻¹ • B z
  have hC_mono : SetValuedOperator.IsMonotone C := by
    intro x y a ha b hb
    dsimp [C] at ha hb
    rcases ha with ⟨u, hu, rfl⟩
    rcases hb with ⟨v, hv, rfl⟩
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg (inv_pos.mpr hc).le (hB_mono u hu v hv)
  have hA_subset_C : A.graph ⊆ C.graph := by
    intro p hpA
    rcases p with ⟨z, a⟩
    change a ∈ A z at hpA
    change a ∈ C z
    dsimp [C]
    refine ⟨c • a, ?_, ?_⟩
    · exact (SetValuedOperator.mem_graph_iff B z (c • a)).mp
        (hsubset ((SetValuedOperator.mem_graph_iff S z (c • a)).mpr ⟨a, hpA, rfl⟩))
    · simp [smul_smul, inv_mul_cancel₀ hc.ne']
  have hC_subset_A : C.graph ⊆ A.graph := hA.2 C hC_mono hA_subset_C
  change u ∈ S x
  dsimp [S]
  refine ⟨c⁻¹ • u, ?_, ?_⟩
  · exact (SetValuedOperator.mem_graph_iff A x (c⁻¹ • u)).mp
      (hC_subset_A ((SetValuedOperator.mem_graph_iff C x (c⁻¹ • u)).mpr
        ⟨u, hp, rfl⟩))
  · simp [smul_smul, mul_inv_cancel₀ hc.ne']

private theorem positive_resolvent_nonempty (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) {r : ℝ} (hr : 0 < r) (y : H) :
    ∃ z, z ∈ ((r : ℝ) • B).resolvent y := by
  rcases minty_surjective_of_maximal_monotone
      (T := fun x : H => r • B x) (positive_scale_maximal_monotone hB hr) y with
    ⟨z, u, hu, hy⟩
  rcases hu with ⟨b, hb, rfl⟩
  refine ⟨z, ?_⟩
  rw [SetValuedOperator.mem_resolvent_smul_iff]
  dsimp [SetValuedOperator.identityAddScaled]
  exact ⟨b, hb, hy.symm⟩

private theorem zeros_isChebyshev (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (hZeros : B.zeros.Nonempty) :
    IsChebyshev B.zeros := by
  have hone : (0 : ℝ) < 1 := by norm_num
  let T : H → H := fun x => Classical.choose
    (positive_resolvent_nonempty B hB hone x)
  have hT : ∀ x, T x ∈ J[((1 : ℝ) • B)] (x - (1 : ℝ) • (0 : H)) := by
    intro x
    simpa only [smul_zero, sub_zero] using
      (Classical.choose_spec (positive_resolvent_nonempty B hB hone x))
  have hT_properties := forward_backward_nonexpansive_and_fixedPoints
    (fun _ : H => 0) B hB 1 1 (by norm_num) (by norm_num)
    (zero_cocoerciveOn 1 (by norm_num)) T hT
  have hzero : operatorSumZeroSet (fun _ : H => 0) B = B.zeros := by
    ext x
    simp [operatorSumZeroSet, operatorSum]
  have hT_fix_closed_convex :
      IsClosed (Function.fixedPoints T) ∧ Convex ℝ (Function.fixedPoints T) := by
    simpa [fixedPointSetOn] using
      (isClosed_and_convex_fixedPointSet_of_nonexpansiveOn
        (D := Set.univ) Set.univ_nonempty isClosed_univ convex_univ
          hT_properties.1.lipschitzOnWith)
  exact isChebyshev_of_nonempty_isClosed_convex hZeros
    (hT_properties.2.trans hzero ▸ hT_fix_closed_convex.1)
    (hT_properties.2.trans hzero ▸ hT_fix_closed_convex.2)

theorem inertial_proximal_point_strong_convergence (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (hZeros : B.zeros.Nonempty)
    (alg : InertialForwardBackward (fun _ : H ↦ 0) B)
    (hInertiaBounded : Bornology.IsBounded (Set.range alg.inertia))
    (hLowerStepBound : 0 < liminf alg.stepSize atTop) :
    Tendsto alg.x atTop
      (nhds (projectionPoint B.zeros (zeros_isChebyshev B hB hZeros) alg.x0)) := by
  classical
  have hZerosChebyshev : IsChebyshev B.zeros := zeros_isChebyshev B hB hZeros
  have hInitialZerosQ : B.zeros ⊆ inertialForwardBackwardQ alg.x alg.x0 1 := by
    intro u _
    simp [inertialForwardBackwardQ, alg.initial_one_eq_x0]
  have hbase : B.zeros ⊆ inertialForwardBackwardC alg.x alg.z alg.inertia 1 ∩
      inertialForwardBackwardQ alg.x alg.x0 1 := by
    intro u hu
    exact ⟨zeros_subset_inertialForwardBackwardC_proximal B hB alg 1 (by omega) hu,
      hInitialZerosQ hu⟩
  have hCQ_closed_convex : ∀ n : ℕ,
      IsClosed (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n) ∧
      Convex ℝ (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n) := by
    intro n
    rcases inertialForwardBackwardC_isClosed_convex_proximal B alg n with ⟨hCclosed, hCconvex⟩
    rcases inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n with ⟨hQclosed, hQconvex⟩
    exact ⟨hCclosed.inter hQclosed, hCconvex.inter hQconvex⟩
  have hfeasible : ∀ n : ℕ, 1 ≤ n → B.zeros ⊆
      inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ n hn ih =>
      intro u hu
      have huCQ := ih hu
      have hne : (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
          inertialForwardBackwardQ alg.x alg.x0 n).Nonempty := ⟨u, huCQ⟩
      have hvariational :=
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex hne
          (hCQ_closed_convex n).1 (hCQ_closed_convex n).2).mp
          (eq_projectionPoint_of_isBestApproximation _
            (isChebyshev_of_nonempty_isClosed_convex hne (hCQ_closed_convex n).1
              (hCQ_closed_convex n).2)
            ((mem_setValuedProjector_iff).mp (alg.projection_step n)))
      refine ⟨zeros_subset_inertialForwardBackwardC_proximal B hB alg (n + 1) (by omega) hu, ?_⟩
      simpa [inertialForwardBackwardQ] using hvariational.2 u huCQ
  have hx_next_mem_CQ : ∀ n : ℕ, 1 ≤ n → alg.x (n + 1) ∈
      inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n hn
    obtain ⟨u, hu⟩ := hZeros
    have hne : (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n).Nonempty := ⟨u, hfeasible n hn hu⟩
    exact (mem_setValuedProjector_iff.mp (alg.projection_step n)).1
  have hx_mem_Q : ∀ n : ℕ, alg.x n ∈ inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n
    simp [inertialForwardBackwardQ]
  have hx_is_projection_Q : ∀ n : ℕ, alg.x n =
      projectionPoint (inertialForwardBackwardQ alg.x alg.x0 n)
        (isChebyshev_of_nonempty_isClosed_convex ⟨alg.x n, hx_mem_Q n⟩
          (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
          (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2) alg.x0 := by
    intro n
    apply (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2).mpr
    constructor
    · exact hx_mem_Q n
    · intro v hv
      simpa [inertialForwardBackwardQ] using hv
  let p : H := projectionPoint B.zeros hZerosChebyshev alg.x0
  let d : ℕ → ℝ := fun n => ‖alg.x n - alg.x0‖
  have hpZeros : p ∈ B.zeros := projectionPoint_mem _ hZerosChebyshev _
  have hpQ : ∀ n : ℕ, p ∈ inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [inertialForwardBackwardQ, alg.initial_zero]
    · exact (hfeasible n (Nat.one_le_iff_ne_zero.mpr hn) hpZeros).2
  have hdist_le : ∀ n : ℕ, d n ≤ ‖p - alg.x0‖ := by
    intro n
    have hpyth := metric_projection_pythagorean
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2
      alg.x0 p (hpQ n)
    rw [← hx_is_projection_Q n, norm_sub_rev alg.x0 (alg.x n)] at hpyth
    rw [norm_sub_rev alg.x0 p] at hpyth
    dsimp [d]
    nlinarith [sq_nonneg ‖p - alg.x n‖, norm_nonneg (alg.x n - alg.x0),
      norm_nonneg (p - alg.x0)]
  have hstep_sq : ∀ n : ℕ, 1 ≤ n →
      ‖alg.x (n + 1) - alg.x n‖ ^ 2 + d n ^ 2 ≤ d (n + 1) ^ 2 := by
    intro n hn
    have hpyth := metric_projection_pythagorean
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2
      alg.x0 (alg.x (n + 1)) (hx_next_mem_CQ n hn).2
    rw [← hx_is_projection_Q n, norm_sub_rev alg.x0 (alg.x n),
      norm_sub_rev alg.x0 (alg.x (n + 1))] at hpyth
    simpa [d, norm_sub_rev] using hpyth
  have hmono : Monotone d := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [d]
      rw [alg.initial_zero]
      simp
    · have hs := hstep_sq n (Nat.one_le_iff_ne_zero.mpr hn)
      nlinarith [sq_nonneg ‖alg.x (n + 1) - alg.x n‖,
        norm_nonneg (alg.x n - alg.x0), norm_nonneg (alg.x (n + 1) - alg.x0)]
  have hdbdd : BddAbove (Set.range d) := by
    refine ⟨‖p - alg.x0‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hdist_le n
  have hd : Tendsto d atTop (nhds (⨆ n, d n)) :=
    tendsto_atTop_ciSup hmono hdbdd
  have hx_bounded : Bornology.IsBounded (Set.range alg.x) :=
    bounded_range_of_convergent_distance_to_point ⟨_, hd⟩
  have hd_shift : Tendsto (fun n => d (n + 1)) atTop (nhds (⨆ n, d n)) := by
    simpa using hd.comp (tendsto_add_atTop_nat 1)
  have hdiff_zero : Tendsto (fun n => d (n + 1) ^ 2 - d n ^ 2) atTop (nhds 0) := by
    simpa using (hd_shift.pow 2).sub (hd.pow 2)
  have hinc_sq_zero : Tendsto (fun n => ‖alg.x (n + 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.x (n + 1) - alg.x n‖ ^ 2)
      (g := fun n => d (n + 1) ^ 2 - d n ^ 2) ?_ ?_ hdiff_zero
    · filter_upwards with n
      exact sq_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hs := hstep_sq n hn
      nlinarith
  have hinc_zero : Tendsto (fun n => ‖alg.x (n + 1) - alg.x n‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hinc_sq_zero
    convert hsqrt using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le.mp hInertiaBounded)
  have hM_nonneg : 0 ≤ M := by
    have := hM (alg.inertia 1) (Set.mem_range_self 1)
    exact le_trans (norm_nonneg _) this
  have hinc_prev_zero : Tendsto (fun n => ‖alg.x n - alg.x (n - 1)‖) atTop (nhds 0) := by
    apply (hinc_zero.comp (tendsto_sub_atTop_nat 1)).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    change ‖alg.x ((n - 1) + 1) - alg.x (n - 1)‖ = ‖alg.x n - alg.x (n - 1)‖
    rw [Nat.sub_add_cancel hn]
  have hyx_zero : Tendsto (fun n => ‖alg.y n - alg.x n‖) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.y n - alg.x n‖)
      (g := fun n => M * ‖alg.x n - alg.x (n - 1)‖) ?_ ?_ ?_
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [alg.inertial_step n hn]
      have hvec : (alg.x n + alg.inertia n • (alg.x n - alg.x (n - 1))) - alg.x n =
          alg.inertia n • (alg.x n - alg.x (n - 1)) := by abel
      rw [hvec, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mem_range_self _)) (norm_nonneg _)
    · simpa using hinc_prev_zero.const_mul M
  have hinc_rev_zero : Tendsto (fun n => ‖alg.x n - alg.x (n + 1)‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using hinc_zero
  have hzxnext_sq_zero : Tendsto (fun n => ‖alg.z n - alg.x (n + 1)‖ ^ 2)
      atTop (nhds 0) := by
    have hzxnext_sq_le : ∀ n : ℕ, 1 ≤ n →
        ‖alg.z n - alg.x (n + 1)‖ ^ 2 ≤
          ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
            2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
              M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2 := by
      intro n hn
      apply inertial_residual_sq_le_of_abs_inertia
        (by simpa [Real.norm_eq_abs] using hM (alg.inertia n) (Set.mem_range_self n))
      simpa [inertialForwardBackwardC, Nat.ne_of_gt hn] using (hx_next_mem_CQ n hn).1
    have hcross_zero : Tendsto (fun n =>
        2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖)
        atTop (nhds 0) := by
      have hraw : Tendsto (fun n =>
          2 * M * ‖alg.x (n + 1) - alg.x n‖ * ‖alg.x n - alg.x (n - 1)‖)
          atTop (nhds 0) := by
        simpa using ((hinc_zero.const_mul (2 * M)).mul hinc_prev_zero)
      refine hraw.congr' ?_
      filter_upwards with n
      rw [norm_sub_rev (alg.x n) (alg.x (n + 1)), norm_sub_rev (alg.x n) (alg.x (n - 1))]
    have hlast_zero : Tendsto (fun n =>
        M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
      have hraw : Tendsto (fun n => M ^ 2 * ‖alg.x n - alg.x (n - 1)‖ ^ 2)
          atTop (nhds 0) := by
        simpa using (hinc_prev_zero.pow 2).const_mul (M ^ 2)
      refine hraw.congr' ?_
      filter_upwards with n
      rw [norm_sub_rev]
    have hrhs_zero : Tendsto (fun n =>
        ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
          2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
            M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
      have hraw : Tendsto (fun n =>
          ‖alg.x (n + 1) - alg.x n‖ ^ 2 +
            2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
              M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
        simpa [add_assoc] using ((hinc_zero.pow 2).add hcross_zero).add hlast_zero
      refine hraw.congr' ?_
      filter_upwards with n
      rw [norm_sub_rev (alg.x n) (alg.x (n + 1))]
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.x (n + 1)‖ ^ 2)
      (g := fun n => ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
        2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
          M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) ?_ ?_ hrhs_zero
    · filter_upwards with n
      exact sq_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hzxnext_sq_le n hn
  have hzxnext_zero : Tendsto (fun n => ‖alg.z n - alg.x (n + 1)‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hzxnext_sq_zero
    convert hsqrt using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  have hzy_zero : Tendsto (fun n => ‖alg.z n - alg.y n‖) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.y n‖)
      (g := fun n => ‖alg.z n - alg.x (n + 1)‖ +
        ‖alg.x (n + 1) - alg.x n‖ + ‖alg.x n - alg.y n‖) ?_ ?_ ?_
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      calc
        ‖alg.z n - alg.y n‖ ≤ ‖alg.z n - alg.x (n + 1)‖ +
            ‖alg.x (n + 1) - alg.y n‖ := by
              simpa [norm_sub_rev] using
                (norm_sub_le (alg.z n - alg.x (n + 1)) (alg.y n - alg.x (n + 1)))
        _ ≤ ‖alg.z n - alg.x (n + 1)‖ +
            (‖alg.x (n + 1) - alg.x n‖ + ‖alg.x n - alg.y n‖) := by
              gcongr
              simpa [norm_sub_rev] using
                (norm_sub_le (alg.x (n + 1) - alg.x n) (alg.y n - alg.x n))
        _ = _ := by ring
    · simpa [norm_sub_rev] using ((hzxnext_zero.add hinc_zero).add hyx_zero)
  let eps : ℝ := (liminf alg.stepSize atTop) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith [hLowerStepBound]
  have hEventually : ∀ᶠ n in atTop, eps ≤ alg.stepSize n := by
    filter_upwards [Filter.eventually_lt_of_lt_liminf (u := alg.stepSize) (b := eps) (by
      change (liminf alg.stepSize atTop) / 2 < liminf alg.stepSize atTop
      linarith [hLowerStepBound])
      (isBoundedUnder_of_eventually_ge (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact (alg.stepSize_pos n hn).le))] with n hn
    exact hn.le
  let T : H → H := fun x => Classical.choose (positive_resolvent_nonempty B hB heps x)
  have hT : ∀ x, T x ∈ ((eps : ℝ) • B).resolvent x := by
    intro x
    exact Classical.choose_spec (positive_resolvent_nonempty B hB heps x)
  let R : ℕ → H → H := fun n x => if hn : 1 ≤ n then
    if x = alg.y n then alg.z n else Classical.choose
      (positive_resolvent_nonempty B hB (alg.stepSize_pos n hn) x)
    else T x
  have hR : ∀ n, 1 ≤ n → ∀ x, R n x ∈ ((alg.stepSize n : ℝ) • B).resolvent x := by
    intro n hn x
    by_cases hx : x = alg.y n
    · subst x
      simpa [R, hn] using alg.resolvent_step n hn
    · simpa [R, hn, hx] using Classical.choose_spec
        (positive_resolvent_nonempty B hB (alg.stepSize_pos n hn) x)
  have hT_y_zero : Tendsto (fun n => ‖alg.y n - T (alg.y n)‖) atTop (nhds 0) := by
    have hupper_zero : Tendsto (fun n => 2 * ‖alg.y n - alg.z n‖) atTop (nhds 0) := by
      simpa [norm_sub_rev] using hzy_zero.const_mul 2
    refine squeeze_zero' (f := fun n => ‖alg.y n - T (alg.y n)‖)
      (g := fun n => 2 * ‖alg.y n - alg.z n‖) ?_ ?_ hupper_zero
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards [hEventually, eventually_ge_atTop 1] with n hstep hn
      have hbound := forward_backward_fixedPoints_and_residual_bound
        (fun _ : H => 0) B hB eps (zero_cocoerciveOn eps heps)
        (alg.stepSize n) eps heps hstep (R n) T
        (by intro x; simpa [R, hn] using hR n hn x) (by intro x; simpa using hT x)
      simpa [R, hn, norm_sub_rev] using hbound.2 (alg.y n)
  have hT_nonexp : LipschitzWith 1 T :=
    (forward_backward_nonexpansive_and_fixedPoints (fun _ : H => 0) B hB
      (eps / 2) eps (by linarith [heps]) (by linarith) (zero_cocoerciveOn (eps / 2) (by linarith [heps]))
      T (by intro x; simpa using hT x)).1
  have hT_fix : Function.fixedPoints T = B.zeros := by
    have hraw := (forward_backward_nonexpansive_and_fixedPoints (fun _ : H => 0) B hB
        (eps / 2) eps (by linarith [heps]) (by linarith)
        (zero_cocoerciveOn (eps / 2) (by linarith [heps])) T
        (by intro x; simpa using hT x)).2
    have hzero : operatorSumZeroSet (fun _ : H => 0) B = B.zeros := by
      ext x
      simp [operatorSumZeroSet, operatorSum]
    exact hraw.trans hzero
  have hresidual_norm : Tendsto (fun n => ‖alg.x n - T (alg.x n)‖) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 2 * ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.y n)‖)
        atTop (nhds 0) := by
      simpa [norm_sub_rev] using (hyx_zero.const_mul 2).add hT_y_zero
    refine squeeze_zero' (f := fun n => ‖alg.x n - T (alg.x n)‖)
      (g := fun n => 2 * ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.y n)‖) ?_ ?_ hupper
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      calc
        ‖alg.x n - T (alg.x n)‖ ≤ ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.x n)‖ := by
          rw [← sub_add_sub_cancel (alg.x n) (alg.y n) (T (alg.x n))]
          exact norm_add_le _ _
        _ ≤ ‖alg.x n - alg.y n‖ +
            (‖alg.y n - T (alg.y n)‖ + ‖T (alg.y n) - T (alg.x n)‖) := by
          gcongr
          rw [← sub_add_sub_cancel (alg.y n) (T (alg.y n)) (T (alg.x n))]
          exact norm_add_le _ _
        _ ≤ ‖alg.x n - alg.y n‖ +
            (‖alg.y n - T (alg.y n)‖ + ‖alg.y n - alg.x n‖) := by
          gcongr
          simpa using hT_nonexp.norm_sub_le (alg.y n) (alg.x n)
        _ = 2 * ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.y n)‖ := by
          rw [norm_sub_rev (alg.y n) (alg.x n)]
          ring
  have hresidual : Tendsto (fun n => alg.x n - T (alg.x n)) atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hresidual_norm
  have hclusterZeros : ∀ w : H,
      IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H w) →
        w ∈ B.zeros := by
    intro w hw
    rcases hw with ⟨phi, hphi, hweak⟩
    have hresidual_phi : Tendsto (fun k => alg.x (phi k) - T (alg.x (phi k))) atTop (nhds 0) :=
      hresidual.comp hphi.tendsto_atTop
    have hweak_closed : IsSeqClosed ((toWeakSpace ℝ H) '' (Set.univ : Set H)) :=
      ((isClosed_iff_weak_image_isClosed_of_convex convex_univ).mp isClosed_univ).isSeqClosed
    have hT_lipschitz : LipschitzOnWith 1 T (Set.univ : Set H) := by
      apply isNonexpansiveOn_restrict_iff_lipschitzOnWith_one.mp
      intro a ha b hb
      simpa using hT_nonexp.norm_sub_le a b
    have hdem := browder_demiclosedness_principle hweak_closed hT_lipschitz
      (fun _ => Set.mem_univ _) hweak hresidual_phi
    have hwfixed : w ∈ fixedPointSetOn (Set.univ : Set H) T := by
      rw [mem_fixedPointSetOn_iff]
      refine ⟨mem_of_tendsto_weakly_of_isClosed_convex isClosed_univ convex_univ
        (fun _ => Set.mem_univ _) hweak, ?_⟩
      exact (sub_eq_zero.mp (hdem.trans rfl)).symm
    rw [mem_fixedPointSetOn_iff] at hwfixed
    have hwfixed' : w ∈ Function.fixedPoints T := hwfixed.2
    rw [hT_fix] at hwfixed'
    exact hwfixed'
  have hclusterEq : ∀ w : H,
      IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H w) → w = p := by
    intro w hw
    rcases hw with ⟨phi, hphi, hweak_phi⟩
    have hwZeros : w ∈ B.zeros := hclusterZeros w ⟨phi, hphi, hweak_phi⟩
    have hinner_raw :=
      (weakConvergence_iff_forall_tendsto_inner_right (fun k => alg.x (phi k)) w).1
        hweak_phi (w - alg.x0)
    have hinner : Tendsto (fun k => inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0))
        atTop (nhds (‖w - alg.x0‖ ^ 2)) := by
      have hsub := hinner_raw.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 (w - alg.x0)) atTop
          (nhds (inner ℝ alg.x0 (w - alg.x0))))
      convert hsub using 1
      · ext k
        rw [inner_sub_left]
      · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have hbound : ∀ k, inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0) ≤
        ‖p - alg.x0‖ * ‖w - alg.x0‖ := by
      intro k
      calc
        inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0) ≤
            ‖alg.x (phi k) - alg.x0‖ * ‖w - alg.x0‖ := real_inner_le_norm _ _
        _ ≤ ‖p - alg.x0‖ * ‖w - alg.x0‖ :=
          mul_le_mul_of_nonneg_right (hdist_le (phi k)) (norm_nonneg _)
    have hsq_le : ‖w - alg.x0‖ ^ 2 ≤ ‖p - alg.x0‖ * ‖w - alg.x0‖ :=
      le_of_tendsto hinner (Filter.Eventually.of_forall hbound)
    have hw_le : ‖w - alg.x0‖ ≤ ‖p - alg.x0‖ := by
      by_cases hwzero : ‖w - alg.x0‖ = 0
      · rw [hwzero]
        exact norm_nonneg _
      · have hwpos : 0 < ‖w - alg.x0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwzero)
        nlinarith
    have hpbest := projectionPoint_isBestApproximation B.zeros hZerosChebyshev alg.x0
    have hp_le : ‖p - alg.x0‖ ≤ ‖w - alg.x0‖ := by
      have hinf := Metric.infDist_le_dist_of_mem (x := alg.x0) hwZeros
      have hpinf : dist alg.x0 p = Metric.infDist alg.x0 B.zeros := hpbest.2
      simpa [dist_eq_norm, norm_sub_rev] using hpinf.trans_le hinf
    have hdist_eq : ‖w - alg.x0‖ = ‖p - alg.x0‖ := le_antisymm hw_le hp_le
    apply eq_projectionPoint_of_isBestApproximation B.zeros hZerosChebyshev
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
    refine ⟨hwZeros, ?_⟩
    calc
      dist alg.x0 w = ‖w - alg.x0‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ = ‖p - alg.x0‖ := hdist_eq
      _ = dist alg.x0 p := by rw [dist_eq_norm, norm_sub_rev]
      _ = Metric.infDist alg.x0 B.zeros := hpbest.2
  have hweak : Tendsto (fun n => toWeakSpace ℝ H (alg.x n)) atTop
      (nhds (toWeakSpace ℝ H p)) := by
    have huniq : ∀ y z : H,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H z) → y = z := by
      intro y z hy hz
      calc
        y = p := hclusterEq y hy
        _ = z := (hclusterEq z hz).symm
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint alg.x).2
        ⟨hx_bounded, huniq⟩ with ⟨w, hw⟩
    have hwcluster : IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n))
        (toWeakSpace ℝ H w) := ⟨id, strictMono_id, by simpa using hw⟩
    have hwp : w = p := hclusterEq w hwcluster
    simpa [hwp] using hw
  have hL_le : (⨆ n, d n) ≤ ‖p - alg.x0‖ :=
    le_of_tendsto hd (Filter.Eventually.of_forall hdist_le)
  have hinner_raw :=
    (weakConvergence_iff_forall_tendsto_inner_right alg.x p).1 hweak (p - alg.x0)
  have hinner : Tendsto (fun n => inner ℝ (alg.x n - alg.x0) (p - alg.x0)) atTop
      (nhds (‖p - alg.x0‖ ^ 2)) := by
    have hsub := hinner_raw.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 (p - alg.x0)) atTop
        (nhds (inner ℝ alg.x0 (p - alg.x0))))
    convert hsub using 1
    · ext n
      rw [inner_sub_left]
    · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hupper : Tendsto (fun n => d n * ‖p - alg.x0‖) atTop
      (nhds ((⨆ n, d n) * ‖p - alg.x0‖)) := hd.mul tendsto_const_nhds
  have hsq_le : ‖p - alg.x0‖ ^ 2 ≤ (⨆ n, d n) * ‖p - alg.x0‖ := by
    apply le_of_tendsto_of_tendsto hinner hupper
    filter_upwards with n
    calc
      inner ℝ (alg.x n - alg.x0) (p - alg.x0) ≤
          ‖alg.x n - alg.x0‖ * ‖p - alg.x0‖ := real_inner_le_norm _ _
      _ = d n * ‖p - alg.x0‖ := rfl
  have hp_le_L : ‖p - alg.x0‖ ≤ (⨆ n, d n) := by
    by_cases hpzero : ‖p - alg.x0‖ = 0
    · rw [hpzero]
      calc 0 = d 0 := by simp [d, alg.initial_zero]
           _ ≤ ⨆ n, d n := le_ciSup hdbdd 0
    · have hppos : 0 < ‖p - alg.x0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpzero)
      nlinarith
  have hL : (⨆ n, d n) = ‖p - alg.x0‖ := le_antisymm hL_le hp_le_L
  have hnorm : Tendsto (fun n => ‖alg.x n - alg.x0‖) atTop (nhds ‖p - alg.x0‖) := by
    simpa [d, hL] using hd
  have hweak_sub : Tendsto (fun n => toWeakSpace ℝ H (alg.x n - alg.x0)) atTop
      (nhds (toWeakSpace ℝ H (p - alg.x0))) := by
    apply (weakConvergence_iff_forall_tendsto_inner_right
      (fun n => alg.x n - alg.x0) (p - alg.x0)).2
    intro u
    have hraw := (weakConvergence_iff_forall_tendsto_inner_right alg.x p).1 hweak u
    have hsub := hraw.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 u) atTop (nhds (inner ℝ alg.x0 u)))
    simpa [inner_sub_left] using hsub
  have hstrong_sub : Tendsto (fun n => alg.x n - alg.x0) atTop (nhds (p - alg.x0)) :=
    (tendsto_iff_tendsto_weakly_and_tendsto_norm (fun n => alg.x n - alg.x0)
      (p - alg.x0)).2 ⟨hweak_sub, hnorm⟩
  simpa only [sub_add_cancel] using hstrong_sub.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => alg.x0) atTop (nhds alg.x0))
