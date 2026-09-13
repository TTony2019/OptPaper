import Mathlib
import Foundation.Hilbert.WeakConvergence
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_thm_2
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_thm_3
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.lem_2

open Filter
open scoped Pointwise

namespace LorenzPock

/-! The elementary metric polarization identity used in the energy estimate. -/
private theorem weighted_polarization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (P : H →L[ℝ] H)
    (hP : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v)) (a b c : H) :
    inner ℝ (P (a - b)) (a - c) = (1 / 2 : ℝ) *
      (inner ℝ (P (a - b)) (a - b) + inner ℝ (P (a - c)) (a - c) -
        inner ℝ (P (b - c)) (b - c)) := by
  have hac : a - c = (a - b) + (b - c) := by abel
  rw [hac, map_add, inner_add_left, inner_add_right]
  have hcross : inner ℝ (P (a - b)) (b - c) = inner ℝ (P (b - c)) (a - b) := by
    calc
      inner ℝ (P (a - b)) (b - c) = inner ℝ (a - b) (P (b - c)) := hP _ _
      _ = inner ℝ (P (b - c)) (a - b) := real_inner_comm _ _
  rw [hcross]
  rw [inner_add_right]
  ring

/-- A point of the zero set of `A + B` supplies the graph value used in
the monotonicity estimate. -/
theorem neg_apply_mem_of_solution_set {H : Type*} [AddCommGroup H]
    (A : SetValuedOperator H H) (B : H → H) (S : Set H)
    (hsolution : S = {z | ∃ a ∈ A z, a + B z = 0}) {z : H} (hz : z ∈ S) :
    -B z ∈ A z := by
  rw [hsolution] at hz
  rcases hz with ⟨a, ha, hzero⟩
  have haeq : a = -B z := eq_neg_iff_add_eq_zero.mpr hzero
  rw [← haeq]
  exact ha

/-- Expanding the quadratic energy for the shifted metric `M - (t / 2)L`. -/
theorem shifted_metric_quadratic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M L : H →L[ℝ] H) (t : ℝ) (u : H) :
    (1 / 2 : ℝ) * inner ℝ ((M - (t / 2) • L) u) u =
      (1 / 2 : ℝ) * inner ℝ (M u) u - (t / 2) *
        ((1 / 2 : ℝ) * inner ℝ (L u) u) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- The completed-square Young estimate associated with mutually inverse
positive metrics. -/
private theorem metric_young_from_two_sided_inverse {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (L Linv : H →L[ℝ] H)
    (hLself : ∀ u v, inner ℝ (L u) v = inner ℝ u (L v))
    (hLpos : ∀ u, u ≠ 0 → 0 < inner ℝ (L u) u)
    (hLcomp : L.comp Linv = ContinuousLinearMap.id ℝ H) (p r : H) :
    - inner ℝ (Linv p) p - (1 / 4 : ℝ) * inner ℝ (L r) r ≤ inner ℝ p r := by
  have hcomp : L (Linv p) = p := by
    have := DFunLike.congr_fun hLcomp p
    simpa using this
  have hnonneg : 0 ≤ inner ℝ (L (r + (2 : ℝ) • Linv p)) (r + (2 : ℝ) • Linv p) := by
    by_cases hzero : r + (2 : ℝ) • Linv p = 0
    · simp [hzero]
    · exact le_of_lt (hLpos _ hzero)
  have hcross : inner ℝ (L r) (Linv p) = inner ℝ p r := by
    calc
      inner ℝ (L r) (Linv p) = inner ℝ r (L (Linv p)) := hLself _ _
      _ = inner ℝ p r := by rw [hcomp, real_inner_comm]
  rw [map_add, map_smul, inner_add_left, inner_add_right] at hnonneg
  simp only [inner_smul_left, inner_smul_right] at hnonneg
  simp only [starRingEnd_apply, star_trivial] at hnonneg
  rw [inner_add_right] at hnonneg
  simp only [inner_smul_right] at hnonneg
  rw [hcross, hcomp] at hnonneg
  have hsym : inner ℝ p (Linv p) = inner ℝ (Linv p) p := real_inner_comm _ _
  rw [hsym] at hnonneg
  nlinarith

/-- The one-step forward--backward estimate in the metric
`M - (ell / 2) L`.  This is the vector part of the Lyapunov calculation and
is kept public because the same estimate is used by the later specializations
of the inertial forward--backward scheme. -/
theorem forward_backward_shifted_energy_step {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (M L Linv : H →L[ℝ] H)
    (ell : ℝ) (u w r p : H)
    (hM : ∀ a b, inner ℝ (M a) b = inner ℝ a (M b))
    (hL : ∀ a b, inner ℝ (L a) b = inner ℝ a (L b))
    (hLpos : ∀ a, a ≠ 0 → 0 < inner ℝ (L a) a)
    (hcomp : L.comp Linv = ContinuousLinearMap.id ℝ H) (hell : 0 ≤ ell)
    (hur : u = w + r)
    (hgraph : 0 ≤ inner ℝ (M (-r) - ell • p) u)
    (hcoco : inner ℝ (Linv p) p ≤ inner ℝ p w) :
    (1 / 2 : ℝ) * inner ℝ (M u) u - (1 / 2 : ℝ) * inner ℝ (M w) w ≤
      -(1 / 2 : ℝ) * inner ℝ ((M - (ell / 2) • L) r) r := by
  have hyoung := metric_young_from_two_sided_inverse L Linv hL hLpos hcomp p r
  have hpwr : -(1 / 4 : ℝ) * inner ℝ (L r) r ≤ inner ℝ p w + inner ℝ p r := by
    linarith
  have hpu : -(ell / 4 : ℝ) * inner ℝ (L r) r ≤ ell * inner ℝ p u := by
    rw [hur, inner_add_right]
    convert mul_le_mul_of_nonneg_left hpwr hell using 1 <;> ring
  have hgraph' : inner ℝ (M r) u + ell * inner ℝ p u ≤ 0 := by
    rw [map_neg, inner_sub_left, inner_neg_left, inner_smul_left] at hgraph
    simp only [starRingEnd_apply, star_trivial] at hgraph
    linarith
  have hMr : inner ℝ (M r) u ≤ (ell / 4 : ℝ) * inner ℝ (L r) r := by
    linarith
  have hpol := weighted_polarization M hM u w 0
  have hr : r = u - w := by rw [hur]; abel
  rw [hr] at hMr
  rw [hr]
  simp only [sub_zero] at hpol
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
  nlinarith [hpol]

/-- A stable inertial recurrence with a vanishing forcing term has vanishing
increments. -/
private theorem inertial_increment_tendsto_zero_of_residual {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d r : ℕ → H) (a : ℕ → ℝ) (abar : ℝ)
    (hrec : ∀ k, d (k + 1) = r k + a k • d k)
    (ha : ∀ k, 0 ≤ a k ∧ a k ≤ abar) (habar : abar < 1)
    (hbounded : ∃ C : ℝ, ∀ k, ‖d k‖ ≤ C)
    (hr : Tendsto r Filter.atTop (nhds 0)) :
    Tendsto d Filter.atTop (nhds 0) := by
  rcases hbounded with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have habar_nonneg : 0 ≤ abar := le_trans (ha 0).1 (ha 0).2
  have hstep (k : ℕ) : ‖d (k + 1)‖ ≤ ‖r k‖ + abar * ‖d k‖ := by
    rw [hrec k]
    calc
      ‖r k + a k • d k‖ ≤ ‖r k‖ + ‖a k • d k‖ := norm_add_le _ _
      _ = ‖r k‖ + |a k| * ‖d k‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖r k‖ + a k * ‖d k‖ := by rw [abs_of_nonneg (ha k).1]
      _ ≤ ‖r k‖ + abar * ‖d k‖ := by
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_right (ha k).2 (norm_nonneg (d k))) ‖r k‖
  refine Metric.tendsto_nhds.mpr (fun ε hε => ?_)
  have hone : 0 < 1 - abar := by linarith
  have hη : 0 < ε * (1 - abar) / 2 := by positivity
  rcases Filter.mem_atTop_sets.mp
      (Metric.tendsto_nhds.mp hr.norm (ε * (1 - abar) / 2) hη) with ⟨N, hN⟩
  have hpow : Tendsto (fun k : ℕ ↦ abar ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one habar_nonneg habar
  have hhalf : 0 < ε / 2 := by linarith
  rcases Filter.mem_atTop_sets.mp
      (Metric.tendsto_nhds.mp (hpow.mul_const C) (ε / 2) hhalf) with ⟨K, hK⟩
  refine Filter.mem_atTop_sets.mpr ⟨N + K, fun n hn => ?_⟩
  let m := n - N
  have hn_eq : n = N + m := by dsimp [m]; omega
  have hmK : K ≤ m := by dsimp [m]; omega
  have htail : ∀ i : ℕ, ‖r (N + i)‖ < ε * (1 - abar) / 2 := by
    intro i
    have := hN (N + i) (by omega)
    simpa [Real.dist_eq, abs_of_nonneg] using this
  have hbound : ∀ i : ℕ, ‖d (N + i)‖ ≤ ε / 2 + abar ^ i * C := by
    intro i
    induction i with
    | zero =>
        simp
        nlinarith [hC N]
    | succ i ih =>
        have hs := hstep (N + i)
        have hrsmall := htail i
        rw [pow_succ]
        have hmul := mul_le_mul_of_nonneg_left ih habar_nonneg
        have hs' : ‖d (N + (i + 1))‖ ≤ ‖r (N + i)‖ + abar * ‖d (N + i)‖ := by
          simpa [Nat.add_assoc] using hs
        clear hs
        nlinarith
  have hpow_le : abar ^ m ≤ abar ^ K :=
    pow_le_pow_of_le_one habar_nonneg (le_of_lt habar) hmK
  have hKval := hK (K) (le_refl K)
  have hKval' : abar ^ K * C < ε / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg habar_nonneg, abs_of_nonneg hC_nonneg] using hKval
  have hdm : ‖d n‖ < ε := by
    rw [hn_eq]
    have hm := hbound m
    nlinarith
  simpa [dist_zero_right] using hdm

/-- A weakly convergent subsequence has the same weak limit after one forward
shift when the successive differences vanish strongly. -/
private theorem weak_shift_of_increment_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : ℕ → H} {ν : ℕ → ℕ} {z : H}
    (hν : StrictMono ν)
    (hx : Tendsto (fun j ↦ toWeakSpace ℝ H (x (ν j))) Filter.atTop
      (nhds (toWeakSpace ℝ H z)))
    (hd : Tendsto (fun k ↦ x (k + 1) - x k) Filter.atTop (nhds 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ H (x (ν j + 1))) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  have hd_subseq : Tendsto (fun j ↦ x (ν j + 1) - x (ν j)) Filter.atTop (nhds 0) := by
    simpa using hd.comp hν.tendsto_atTop
  have hd_weak : Tendsto
      (fun j ↦ toWeakSpace ℝ H (x (ν j + 1) - x (ν j))) Filter.atTop
      (nhds (toWeakSpace ℝ H 0)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto 0).comp hd_subseq
  have hadd := hx.add hd_weak
  simpa [add_comm, toWeakSpaceCLM_eq_toWeakSpace] using hadd

/-- A nonnegative real sequence tends to zero as soon as its squares do. -/
private theorem norm_tendsto_zero_of_sq_tendsto_zero (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n)
    (hsq : Tendsto (fun n ↦ q n ^ 2) Filter.atTop (nhds 0)) :
    Tendsto q Filter.atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (q n ^ 2)) Filter.atTop
      (nhds (Real.sqrt 0)) := hsq.sqrt
  have heq : (fun n ↦ Real.sqrt (q n ^ 2)) = q := by
    funext n
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hq n)]
  simpa [heq] using hsqrt

/-- Difference of two squared distances in a self-adjoint metric.  Keeping this
small algebraic fact separate makes the weighted Opial argument below robust. -/
private theorem weighted_energy_difference {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : H →L[ℝ] H)
    (hM : ∀ u v, inner ℝ (M u) v = inner ℝ u (M v)) (x y z : H) :
    (1 / 2 : ℝ) * inner ℝ (M (x - y)) (x - y) -
        (1 / 2 : ℝ) * inner ℝ (M (x - z)) (x - z) =
      - inner ℝ x (M (y - z)) +
        (1 / 2 : ℝ) * (inner ℝ (M y) y - inner ℝ (M z) z) := by
  simp only [map_sub, inner_sub_left, inner_sub_right]
  have hxy : inner ℝ (M x) y = inner ℝ x (M y) := hM _ _
  have hxz : inner ℝ (M x) z = inner ℝ x (M z) := hM _ _
  have hyx : inner ℝ (M y) x = inner ℝ x (M y) := by
    exact real_inner_comm _ _
  have hzx : inner ℝ (M z) x = inner ℝ x (M z) := by
    exact real_inner_comm _ _
  rw [hxy, hxz, hyx, hzx]
  ring

/-! ## Theorem 1

Under positive-definite metrics and the inertial summability condition, the iteration
(10) converges weakly to a zero of `A + B`.

The hypothesis set is aligned with the paper's Theorem 1 as follows.

* `hmaxA`, `hmaxB`, `hsolution`, `hS_nonempty` : the paper's "`A, B : X ⇉ X` maximally
  monotone" together with the definition `S = (A + B)⁻¹(0)`.  The paper's proof opens with
  "Denote by `x^*` a zero of `A + B`", so non-emptiness of `S` is implicit there; the
  conclusion of the theorem asserts convergence *to a solution*, so it cannot be dropped.
  `hmaxB` is a paper hypothesis that the proof below does not consume (the argument only
  needs `B` maximal monotone through `hsummax`), and `hLinv` records the paper's use of
  `L⁻¹`; both are kept so that the statement matches the paper, and are flagged by
  `linter.unusedVariables` accordingly.
* `hcocoercive` : equation (9), in the paper's own form — the second argument is
  restricted to the solution set `S` (see `def_1.IsCocoerciveWithInverseMetric`).
* `hB_lipschitz` : the paper states after (9) that "the operator `B` is `1/l` co-coercive
  and hence `l`-Lipschitz".  With (9) restricted to `y ∈ S` this Lipschitz property does
  *not* follow from (9) alone, and the proof below needs it at `(x^{k+1}, y^k)`, neither of
  which is known to lie in `S`; it is therefore taken as an explicit hypothesis.  Every
  application in §3 supplies it from `∇Q`, `∇P^*` being Lipschitz.
* `hmetric` is condition (i) (`S_k = M - (λ_k/2)L` positive definite for all `k`).
* `hsummable` is condition (ii).
* `hM_coercive`, `hS_coercive`, `hell_lower` strengthen the paper's hypotheses.  They are
  needed because the paper's proof step "since `δ^k` is summable it follows that
  `‖x^k - x^{k-1}‖_{S_k} → 0`" silently requires a *uniform* positivity constant for
  `S_k = M - (λ_k/2)L` and a uniform positive lower bound on `λ_k` in order to convert the
  `S_k`-norm into the ambient norm; the paper only assumes `λ_k > 0` and pointwise positive
  definiteness of `S_k`.  §3 derives all three from the numbered conditions (22)/(31)-(34).
* `hinitial` (`x^0 = x^{-1}`) is not needed: with `ℕ`-indexing, `x 0 = x (0 - 1)` is `rfl`.
-/

/-- Theorem 1: under positive-definite metrics and the inertial summability
condition, the iteration (10) converges weakly to a zero of `A+B`. -/
theorem inertial_forward_backward_weakly_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : SetValuedOperator H H) (B : H → H)
    (M L Linv : H →L[ℝ] H) (α ell : ℕ → ℝ)
    (it : InertialForwardBackwardIteration H A B M α ell)
    (S : Set H) (hmaxA : SetValuedOperator.IsMaximalMonotone A)
    (hmaxB : SetValuedOperator.IsMaximalMonotone
      (SetValuedOperator.ofFunction Set.univ (fun x ↦ B x)))
    (hsolution : S = {z | ∃ a ∈ A z, a + B z = 0})
    (hS_nonempty : S.Nonempty)
    (hLinv : Linv.comp L = ContinuousLinearMap.id ℝ H)
    (hLcomp : L.comp Linv = ContinuousLinearMap.id ℝ H)
    (hB_lipschitz : ∃ cB : ℝ, 0 < cB ∧ ∀ u v, ‖B u - B v‖ ≤ cB * ‖u - v‖)
    (hL_selfadjoint : ∀ u v, inner ℝ (L u) v = inner ℝ u (L v))
    (hL_positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ (L u) u)
    (hcocoercive : IsCocoerciveWithInverseMetric B Linv S)
    (hell : ∀ k, 0 < ell k) (hα : ∃ αbar : ℝ, αbar < 1 ∧ ∀ k, 0 ≤ α k ∧ α k ≤ αbar)
    (hmetric : ∀ k u, u ≠ 0 → 0 < inner ℝ ((M - (ell k / 2) • L) u) u)
    (hM_coercive : ∃ cM : ℝ, 0 < cM ∧ ∀ u, cM * ‖u‖ ^ 2 ≤ inner ℝ (M u) u)
    (hS_coercive : ∃ cS : ℝ, 0 < cS ∧ ∀ k u,
      cS * ‖u‖ ^ 2 ≤ inner ℝ ((M - (ell k / 2) • L) u) u)
    (hsummax : SetValuedOperator.IsMaximalMonotone
      (A + SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) ↦ B x.1)))
    (hell_lower : ∃ l0 : ℝ, 0 < l0 ∧ ∀ k, l0 ≤ ell k)
    (hsummable : Summable (fun k ↦ α k * inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - it.x (k - 1))) ) :
    ∃ z ∈ S, Tendsto (fun k ↦ toWeakSpace ℝ H (it.x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  rcases hS_nonempty with ⟨xstar, hxstarS⟩
  have hminusB : -B xstar ∈ A xstar :=
    neg_apply_mem_of_solution_set A B S hsolution hxstarS
  choose ak hak hfb using it.forward_backward
  rcases hα with ⟨αbar, hαbar_lt, hαrange⟩
  have hαbar_nonneg : 0 ≤ αbar := by
    exact le_trans (hαrange 0).1 (hαrange 0).2
  have hmetric_young := metric_young_from_two_sided_inverse L Linv hL_selfadjoint
    hL_positive_definite hLcomp
  rcases hB_lipschitz with ⟨cB, -, hB_lipschitz⟩
  let T : SetValuedOperator H H :=
    A + SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) ↦ B x.1)
  let vk : ℕ → H := fun k ↦ ak k + B (it.x (k + 1))
  have hvk_mem : ∀ k, vk k ∈ T (it.x (k + 1)) := by
    intro k
    dsimp [vk, T]
    refine Set.mem_add.2 ⟨ak k, hak k, B (it.x (k + 1)), ?_, rfl⟩
    exact ⟨Set.mem_univ _, rfl⟩
  have hmonotonicity (k : ℕ) :
      0 ≤ inner ℝ (ak k + B xstar) (it.x (k + 1) - xstar) := by
    have hmono := hmaxA.1 (ak k) (hak k) (-B xstar) hminusB
    simpa [sub_eq_add_neg] using hmono
  let φ : H → ℕ → ℝ := fun z k ↦
    (1 / 2 : ℝ) * inner ℝ (M (it.x k - z)) (it.x k - z)
  let Δ : ℕ → ℝ := fun k ↦
    (1 / 2 : ℝ) * inner ℝ (M (it.x k - it.x (k - 1)))
      (it.x k - it.x (k - 1))
  let Γ : (H →L[ℝ] H) → ℕ → ℝ := fun P k ↦
    (1 / 2 : ℝ) * inner ℝ (P (it.x (k + 1) - it.y k))
      (it.x (k + 1) - it.y k)
  let R : ℕ → H := fun k ↦ it.x (k + 1) - it.y k
  let δ : ℕ → ℝ := fun k ↦ 2 * α k * Δ k
  have hΔ_nonneg (k : ℕ) : 0 ≤ Δ k := by
    dsimp [Δ]
    by_cases hk : it.x k - it.x (k - 1) = 0
    · simp [hk]
    · exact mul_nonneg (by norm_num) (le_of_lt (it.metric_positive_definite _ hk))
  have hΓS_nonneg (k : ℕ) : 0 ≤ Γ (M - (ell k / 2) • L) k := by
    dsimp [Γ]
    by_cases hk : it.x (k + 1) - it.y k = 0
    · simp [hk]
    · exact mul_nonneg (by norm_num) (le_of_lt (hmetric k _ hk))
  have hδ_eq (k : ℕ) : δ k =
      α k * inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - it.x (k - 1)) := by
    dsimp [δ, Δ]
    ring
  have hδ_nonneg (k : ℕ) : 0 ≤ δ k := by
    dsimp [δ]
    exact mul_nonneg (mul_nonneg (by norm_num) (hαrange k).1) (hΔ_nonneg k)
  have hδ_summable : Summable δ := by
    exact hsummable.congr (fun k ↦ (hδ_eq k).symm)
  have henergy_step (z : H) (hz : z ∈ S) (k : ℕ) :
      φ z (k + 1) - (1 / 2 : ℝ) * inner ℝ (M (it.y k - z)) (it.y k - z) ≤
        -Γ (M - (ell k / 2) • L) k := by
    have hminusBz : -B z ∈ A z :=
      neg_apply_mem_of_solution_set A B S hsolution hz
    have hmono : 0 ≤ inner ℝ (ak k + B z) (it.x (k + 1) - z) := by
      have h := hmaxA.1 (ak k) (hak k) (-B z) hminusBz
      simpa [sub_eq_add_neg] using h
    have hscaled : 0 ≤ inner ℝ (ell k • (ak k + B z)) (it.x (k + 1) - z) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      exact mul_nonneg (le_of_lt (hell k)) hmono
    have hgraph_eq : ell k • (ak k + B z) =
        M (it.y k - it.x (k + 1)) - ell k • (B (it.y k) - B z) := by
      rw [smul_add, ← hfb k]
      module
    rw [hgraph_eq] at hscaled
    have hur : it.x (k + 1) - z = (it.y k - z) + (it.x (k + 1) - it.y k) := by
      abel
    have hcoco : inner ℝ (Linv (B (it.y k) - B z)) (B (it.y k) - B z) ≤
        inner ℝ (B (it.y k) - B z) (it.y k - z) := by
      exact hcocoercive (it.y k) z hz
    have hstep := forward_backward_shifted_energy_step M L Linv (ell k)
      (it.x (k + 1) - z) (it.y k - z) (it.x (k + 1) - it.y k)
      (B (it.y k) - B z) it.metric_self_adjoint hL_selfadjoint hL_positive_definite
      hLcomp (le_of_lt (hell k)) hur (by
        have hneg : -(it.x (k + 1) - it.y k) = it.y k - it.x (k + 1) := by abel
        rw [hneg]
        exact hscaled) hcoco
    simpa [φ, Γ, ContinuousLinearMap.map_sub] using hstep
  have hinertial_energy (z : H) (k : ℕ) :
      (1 / 2 : ℝ) * inner ℝ (M (it.y k - z)) (it.y k - z) =
        φ z k + α k * (φ z k - φ z (k - 1)) +
          (α k + (α k)^2) * Δ k := by
    have hpol := weighted_polarization M it.metric_self_adjoint
      (it.x k) (it.x (k - 1)) z
    have hcross : inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - z) =
        Δ k + φ z k - φ z (k - 1) := by
      calc
        inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - z) =
            (1 / 2 : ℝ) *
              (inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - it.x (k - 1)) +
                inner ℝ (M (it.x k - z)) (it.x k - z) -
                inner ℝ (M (it.x (k - 1) - z)) (it.x (k - 1) - z)) := hpol
        _ = Δ k + φ z k - φ z (k - 1) := by
          simp only [φ, Δ]
          ring
    have hsymm : inner ℝ (M (it.x k - z)) (it.x k - it.x (k - 1)) =
        inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - z) := by
      calc
        inner ℝ (M (it.x k - z)) (it.x k - it.x (k - 1)) =
            inner ℝ (it.x k - z) (M (it.x k - it.x (k - 1))) :=
              it.metric_self_adjoint _ _
        _ = inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - z) := real_inner_comm _ _
    have hy : it.y k - z = (it.x k - z) + α k • (it.x k - it.x (k - 1)) := by
      rw [it.inertial k]
      module
    rw [hy, map_add, map_smul]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    rw [hsymm, hcross]
    ring
  have henergy (z : H) (hz : z ∈ S) (k : ℕ) :
      φ z (k + 1) - φ z k - α k * (φ z k - φ z (k - 1)) ≤
        -Γ (M - (ell k / 2) • L) k + δ k := by
    have hstep := henergy_step z hz k
    rw [hinertial_energy z k] at hstep
    have hαsq : (α k)^2 ≤ α k := by
      nlinarith [mul_nonneg (hαrange k).1
        (sub_nonneg.mpr (le_of_lt (it.inertia_range k).2))]
    have hcoeff : α k + (α k)^2 ≤ 2 * α k := by linarith
    have hterm : (α k + (α k)^2) * Δ k ≤ δ k := by
      rw [show δ k = 2 * α k * Δ k by rfl]
      nlinarith [hΔ_nonneg k]
    linarith
  have hφ_limit : ∀ z ∈ S, ∃ l : ℝ, Tendsto (φ z) Filter.atTop (nhds l) := by
    intro z hz
    rcases Alvarez2004.lemma_2_3 (φ z) δ α αbar
      (fun k => by
        dsimp [φ]
        by_cases hk : it.x k - z = 0
        · simp [hk]
        · exact mul_nonneg (by norm_num) (le_of_lt (it.metric_positive_definite _ hk)))
      hδ_nonneg (fun k => by
        have h := henergy z hz k
        nlinarith [hΓS_nonneg k]) hδ_summable hαrange hαbar_lt with
      ⟨_, ⟨l, _, hlim⟩⟩
    exact ⟨l, hlim⟩
  have hΓS_zero : Tendsto (fun k ↦ Γ (M - (ell k / 2) • L) k)
      Filter.atTop (nhds 0) := by
    rcases hφ_limit xstar hxstarS with ⟨l, hφ⟩
    have hφ_prev : Tendsto (fun k ↦ φ xstar (k - 1)) Filter.atTop (nhds l) :=
      hφ.comp (tendsto_sub_atTop_nat 1)
    have hφ_next : Tendsto (fun k ↦ φ xstar (k + 1)) Filter.atTop (nhds l) :=
      hφ.comp (tendsto_add_atTop_nat 1)
    have hdiff : Tendsto (fun k ↦ φ xstar k - φ xstar (k - 1)) Filter.atTop
        (nhds 0) := by simpa using hφ.sub hφ_prev
    have hprod : Tendsto (fun k ↦ α k * (φ xstar k - φ xstar (k - 1)))
        Filter.atTop (nhds 0) := by
      have hbound : ∀ k, |α k * (φ xstar k - φ xstar (k - 1))| ≤
          αbar * |φ xstar k - φ xstar (k - 1)| := by
        intro k
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa [abs_of_nonneg (hαrange k).1]
          using (hαrange k).2) (abs_nonneg _)
      have hright : Tendsto (fun k ↦ αbar * |φ xstar k - φ xstar (k - 1)|)
          Filter.atTop (nhds 0) := by
        simpa using hdiff.abs.const_mul αbar
      exact (tendsto_zero_iff_abs_tendsto_zero _).2
        (squeeze_zero (fun k ↦ abs_nonneg _) hbound hright)
    have hδ_zero : Tendsto δ Filter.atTop (nhds 0) := hδ_summable.tendsto_atTop_zero
    have hright : Tendsto (fun k ↦ φ xstar k - φ xstar (k + 1) +
        α k * (φ xstar k - φ xstar (k - 1)) + δ k) Filter.atTop (nhds 0) := by
      simpa using ((hφ.sub hφ_next).add hprod).add hδ_zero
    refine squeeze_zero' (f := fun k ↦ Γ (M - (ell k / 2) • L) k)
      (g := fun k ↦ φ xstar k - φ xstar (k + 1) +
        α k * (φ xstar k - φ xstar (k - 1)) + δ k) ?_ ?_ hright
    · exact Filter.Eventually.of_forall (fun k ↦ hΓS_nonneg k)
    · exact Filter.Eventually.of_forall (fun k ↦ by
      have h := henergy xstar hxstarS k
      linarith)
  rcases hS_coercive with ⟨cS, hcS_pos, hcS⟩
  have hR_sq_zero : Tendsto (fun k ↦ ‖R k‖ ^ 2) Filter.atTop (nhds 0) := by
    have hupper : Tendsto (fun k ↦ (2 / cS) * Γ (M - (ell k / 2) • L) k)
        Filter.atTop (nhds 0) := by
      simpa using hΓS_zero.const_mul (2 / cS)
    refine squeeze_zero (fun k ↦ sq_nonneg ‖R k‖) ?_ hupper
    intro k
    have hco := hcS k (R k)
    have hgamma : 2 * Γ (M - (ell k / 2) • L) k =
        inner ℝ ((M - (ell k / 2) • L) (R k)) (R k) := by
      simp only [Γ, R, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        map_sub]
      ring_nf
    rw [← hgamma] at hco
    have hscaled : ‖R k‖ ^ 2 ≤ (2 * Γ (M - (ell k / 2) • L) k) / cS :=
      (le_div_iff₀ hcS_pos).2 (by nlinarith [hco])
    convert hscaled using 1 <;> field_simp <;> ring
  have hR_norm_zero : Tendsto (fun k ↦ ‖R k‖) Filter.atTop (nhds 0) :=
    norm_tendsto_zero_of_sq_tendsto_zero (fun k ↦ ‖R k‖) (fun k ↦ norm_nonneg _) hR_sq_zero
  have hR_zero : Tendsto R Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hR_norm_zero
  have hMres_zero : Tendsto (fun k ↦ M (it.y k - it.x (k + 1))) Filter.atTop
      (nhds 0) := by
    have hneg : Tendsto (fun k ↦ it.y k - it.x (k + 1)) Filter.atTop (nhds 0) := by
      simpa [R] using hR_zero.neg
    simpa only [Function.comp_apply, map_zero] using (M.continuous.tendsto 0).comp hneg
  have hBres_norm_zero : Tendsto (fun k ↦ ‖B (it.x (k + 1)) - B (it.y k)‖)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (f := fun k ↦ ‖B (it.x (k + 1)) - B (it.y k)‖)
      (g := fun k ↦ cB * ‖R k‖) (fun k ↦ norm_nonneg _) ?_ ?_
    · intro k
      simpa [R] using hB_lipschitz (it.x (k + 1)) (it.y k)
    · simpa using hR_norm_zero.const_mul cB
  have hBres_zero : Tendsto (fun k ↦ B (it.x (k + 1)) - B (it.y k))
      Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hBres_norm_zero
  rcases hell_lower with ⟨l0, hl0_pos, hl0⟩
  have hvk_zero : Tendsto vk Filter.atTop (nhds 0) := by
    have hfirst : Tendsto (fun k ↦ (ell k)⁻¹ • M (it.y k - it.x (k + 1)))
        Filter.atTop (nhds 0) := by
      have hbound : ∀ k, ‖(ell k)⁻¹ • M (it.y k - it.x (k + 1))‖ ≤
          l0⁻¹ * ‖M (it.y k - it.x (k + 1))‖ := by
        intro k
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hl0_pos (hl0 k)))]
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ (hell k) hl0_pos).2 (hl0 k))
          (norm_nonneg _)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr <|
        squeeze_zero (fun k ↦ norm_nonneg _) hbound
          (by simpa using hMres_zero.norm.const_mul l0⁻¹)
    have hsecond : Tendsto (fun k ↦ B (it.x (k + 1)) - B (it.y k))
        Filter.atTop (nhds 0) := hBres_zero
    have hsum : Tendsto (fun k ↦ (ell k)⁻¹ • M (it.y k - it.x (k + 1)) +
        (B (it.x (k + 1)) - B (it.y k))) Filter.atTop (nhds 0) := by
      simpa using hfirst.add hsecond
    apply hsum.congr'
    filter_upwards with k
    symm
    have hell_ne : ell k ≠ 0 := ne_of_gt (lt_of_lt_of_le hl0_pos (hl0 k))
    have hscaled : ell k • vk k =
        M (it.y k - it.x (k + 1)) + ell k • (B (it.x (k + 1)) - B (it.y k)) := by
      dsimp [vk]
      rw [smul_add, ← hfb k]
      module
    calc
      vk k = (ell k)⁻¹ • (ell k • vk k) := by
        rw [inv_smul_smul₀ hell_ne]
      _ = (ell k)⁻¹ • (M (it.y k - it.x (k + 1)) +
          ell k • (B (it.x (k + 1)) - B (it.y k))) := by rw [hscaled]
      _ = (ell k)⁻¹ • M (it.y k - it.x (k + 1)) +
          (B (it.x (k + 1)) - B (it.y k)) := by
        rw [smul_add, inv_smul_smul₀ hell_ne]
  rcases hM_coercive with ⟨cM, hcM_pos, hcM⟩
  rcases hφ_limit xstar hxstarS with ⟨lstar, hφstar⟩
  have hφ_bounded : Bornology.IsBounded (Set.range (φ xstar)) :=
    Metric.isBounded_range_of_tendsto _ hφstar
  rcases isBounded_iff_forall_norm_le.mp hφ_bounded with ⟨Cφ, hCφ⟩
  let Cφ' : ℝ := max Cφ 0
  have hCφ'_nonneg : 0 ≤ Cφ' := le_max_right _ _
  have hφ_upper (k : ℕ) : φ xstar k ≤ Cφ' := by
    calc
      φ xstar k ≤ |φ xstar k| := le_abs_self _
      _ = ‖φ xstar k‖ := (Real.norm_eq_abs _).symm
      _ ≤ Cφ := hCφ _ (Set.mem_range_self k)
      _ ≤ Cφ' := le_max_left _ _
  have hdist_sq (k : ℕ) : ‖it.x k - xstar‖ ^ 2 ≤ 2 * Cφ' / cM := by
    apply (le_div_iff₀ hcM_pos).2
    have hco := hcM (it.x k - xstar)
    have hinner : inner ℝ (M (it.x k - xstar)) (it.x k - xstar) = 2 * φ xstar k := by
      dsimp [φ]
      ring
    rw [hinner] at hco
    nlinarith [hφ_upper k]
  have hdist (k : ℕ) : ‖it.x k - xstar‖ ≤ Real.sqrt (2 * Cφ' / cM) := by
    exact (Real.le_sqrt (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hCφ'_nonneg) (le_of_lt hcM_pos))).2
      (hdist_sq k)
  have hx_bounded : Bornology.IsBounded (Set.range it.x) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨Real.sqrt (2 * Cφ' / cM) + ‖xstar‖, ?_⟩
    rintro x ⟨k, rfl⟩
    calc
      ‖it.x k‖ = ‖(it.x k - xstar) + xstar‖ := by congr 1 <;> abel
      _ ≤ ‖it.x k - xstar‖ + ‖xstar‖ := norm_add_le _ _
      _ ≤ Real.sqrt (2 * Cφ' / cM) + ‖xstar‖ :=
        by simpa [add_comm] using add_le_add_left (hdist k) ‖xstar‖
  let d : ℕ → H := fun k ↦ it.x k - it.x (k - 1)
  have hd_bounded : ∃ C : ℝ, ∀ k, ‖d k‖ ≤ C := by
    rcases isBounded_iff_forall_norm_le.mp hx_bounded with ⟨C, hC⟩
    refine ⟨2 * C, ?_⟩
    intro k
    dsimp [d]
    calc
      ‖it.x k - it.x (k - 1)‖ ≤ ‖it.x k‖ + ‖it.x (k - 1)‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add
        (hC _ (Set.mem_range_self k)) (hC _ (Set.mem_range_self (k - 1)))
      _ = 2 * C := by ring
  have hd_rec (k : ℕ) : d (k + 1) = R k + α k • d k := by
    dsimp [d, R]
    rw [it.inertial k]
    module
  have hd_all_zero : Tendsto d Filter.atTop (nhds 0) :=
    inertial_increment_tendsto_zero_of_residual d R α αbar hd_rec hαrange hαbar_lt
      hd_bounded hR_zero
  have hd_zero : Tendsto (fun k ↦ it.x (k + 1) - it.x k) Filter.atTop (nhds 0) := by
    simpa [d] using hd_all_zero.comp (tendsto_add_atTop_nat 1)
  have hclusterS : ∀ z : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (it.x k))
        (toWeakSpace ℝ H z) → z ∈ S := by
    intro z hz
    rcases hz with ⟨ν, hν, hxν⟩
    have hxνsucc := weak_shift_of_increment_zero hν hxν hd_zero
    have hvν : Tendsto (fun j ↦ vk (ν j)) Filter.atTop (nhds 0) :=
      hvk_zero.comp hν.tendsto_atTop
    have hmemν : ∀ j, vk (ν j) ∈ T (it.x (ν j + 1)) := fun j ↦ hvk_mem _
    have hzeroT : (0 : H) ∈ T z :=
      Alvarez2004.weak_strong_closedness_maximal_monotone_graph T hsummax hxνsucc hvν hmemν
    dsimp [T] at hzeroT
    rcases Set.mem_add.mp hzeroT with ⟨a, ha, b, hb, hab⟩
    have hb' : b = B z := by
      rcases hb with ⟨u, hu, rfl⟩
      rfl
    rw [hsolution]
    refine ⟨a, ha, ?_⟩
    simpa [hb'] using hab
  have hcluster_unique : ∀ y z : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (it.x k)) (toWeakSpace ℝ H y) →
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (it.x k)) (toWeakSpace ℝ H z) → y = z := by
    intro y z hy hz
    have hyS := hclusterS y hy
    have hzS := hclusterS z hz
    rcases hφ_limit y hyS with ⟨ly, hφy⟩
    rcases hφ_limit z hzS with ⟨lz, hφz⟩
    let c : ℝ := (1 / 2 : ℝ) *
      (inner ℝ (M y) y - inner ℝ (M z) z) - (ly - lz)
    have hcoord : Tendsto (fun k ↦ inner ℝ (it.x k) (M (y - z))) Filter.atTop
        (nhds c) := by
      have hconst : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ) *
          (inner ℝ (M y) y - inner ℝ (M z) z)) Filter.atTop
          (nhds ((1 / 2 : ℝ) * (inner ℝ (M y) y - inner ℝ (M z) z))) :=
        tendsto_const_nhds
      have hlim := hconst.sub (hφy.sub hφz)
      convert hlim using 1
      · ext k
        have hdiff := weighted_energy_difference M it.metric_self_adjoint (it.x k) y z
        change φ y k - φ z k = -inner ℝ (it.x k) (M (y - z)) +
          (1 / 2 : ℝ) * (inner ℝ (M y) y - inner ℝ (M z) z) at hdiff
        nlinarith
    rcases hy with ⟨ν, hν, hνweak⟩
    rcases hz with ⟨μ, hμ, hμweak⟩
    have hycoord : Tendsto (fun j ↦ inner ℝ (it.x (ν j)) (M (y - z))) Filter.atTop
        (nhds (inner ℝ y (M (y - z)))) := by
      simpa using
        (weakConvergence_iff_forall_tendsto_inner_right (fun j ↦ it.x (ν j)) y).1
          hνweak (M (y - z))
    have hzcoord : Tendsto (fun j ↦ inner ℝ (it.x (μ j)) (M (y - z))) Filter.atTop
        (nhds (inner ℝ z (M (y - z)))) := by
      simpa using
        (weakConvergence_iff_forall_tendsto_inner_right (fun j ↦ it.x (μ j)) z).1
          hμweak (M (y - z))
    have hyc : inner ℝ y (M (y - z)) = c :=
      tendsto_nhds_unique hycoord (hcoord.comp hν.tendsto_atTop)
    have hzc : inner ℝ z (M (y - z)) = c :=
      tendsto_nhds_unique hzcoord (hcoord.comp hμ.tendsto_atTop)
    have hinner_zero : inner ℝ (M (y - z)) (y - z) = 0 := by
      calc
        inner ℝ (M (y - z)) (y - z) = inner ℝ (y - z) (M (y - z)) :=
          real_inner_comm _ _
        _ = inner ℝ y (M (y - z)) - inner ℝ z (M (y - z)) := by
          rw [inner_sub_left]
        _ = 0 := by rw [hyc, hzc, sub_self]
    have hco := hcM (y - z)
    rw [hinner_zero] at hco
    have hsq : ‖y - z‖ ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint it.x).2
      ⟨hx_bounded, hcluster_unique⟩ with ⟨z, hzweak⟩
  have hzcluster : IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (it.x k))
      (toWeakSpace ℝ H z) := ⟨id, strictMono_id, by simpa using hzweak⟩
  exact ⟨z, hclusterS z hzcluster, hzweak⟩

end LorenzPock
