import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

open Filter
open scoped Pointwise

namespace LorenzPock

/-! Elementary metric algebra used in the Lyapunov calculation for Theorem 2. -/
private theorem weighted_polarization_thm2 {H : Type*} [NormedAddCommGroup H]
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

private theorem inertial_cross_term_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (P : H →L[ℝ] H)
    (hP : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v))
    (hP_nonneg : ∀ u, 0 ≤ inner ℝ (P u) u) (u v : H) (a : ℝ) (ha : 0 ≤ a) :
    a * inner ℝ (P u) v ≤ a * ((1 / 2 : ℝ) * inner ℝ (P u) u) +
      a * ((1 / 2 : ℝ) * inner ℝ (P v) v) := by
  have hsq : 0 ≤ inner ℝ (P (u - v)) (u - v) := hP_nonneg (u - v)
  rw [map_sub, inner_sub_left, inner_sub_right] at hsq
  rw [inner_sub_right] at hsq
  have hsymm : inner ℝ (P v) u = inner ℝ (P u) v := by
    calc
      inner ℝ (P v) u = inner ℝ v (P u) := hP _ _
      _ = inner ℝ (P u) v := real_inner_comm _ _
  rw [hsymm] at hsq
  have hyoung : inner ℝ (P u) v ≤
      (1 / 2 : ℝ) * inner ℝ (P u) u + (1 / 2 : ℝ) * inner ℝ (P v) v := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hyoung ha]

/-- The completed-square estimate for the inverse metric appearing in the
forward--backward energy inequality. -/
private theorem metric_young_from_two_sided_inverse_thm2 {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (L Linv : H →L[ℝ] H)
    (hLself : ∀ u v, inner ℝ (L u) v = inner ℝ u (L v))
    (hLpos : ∀ u, u ≠ 0 → 0 < inner ℝ (L u) u)
    (hLcomp : L.comp Linv = ContinuousLinearMap.id ℝ H) (p r : H) :
    - inner ℝ (Linv p) p - (1 / 4 : ℝ) * inner ℝ (L r) r ≤ inner ℝ p r := by
  have hcomp : L (Linv p) = p := by
    have h := DFunLike.congr_fun hLcomp p
    simpa using h
  have hnonneg : 0 ≤ inner ℝ (L (r + (2 : ℝ) • Linv p))
      (r + (2 : ℝ) • Linv p) := by
    by_cases hzero : r + (2 : ℝ) • Linv p = 0
    · simp [hzero]
    · exact le_of_lt (hLpos _ hzero)
  have hcross : inner ℝ (L r) (Linv p) = inner ℝ p r := by
    calc
      inner ℝ (L r) (Linv p) = inner ℝ r (L (Linv p)) := hLself _ _
      _ = inner ℝ p r := by rw [hcomp, real_inner_comm]
  rw [map_add, map_smul, inner_add_left, inner_add_right] at hnonneg
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial] at hnonneg
  rw [inner_add_right] at hnonneg
  simp only [inner_smul_right] at hnonneg
  rw [hcross, hcomp] at hnonneg
  have hsym : inner ℝ p (Linv p) = inner ℝ (Linv p) p := real_inner_comm _ _
  rw [hsym] at hnonneg
  nlinarith

/-- The one-step forward--backward estimate in the shifted metric. -/
private theorem forward_backward_energy_step_thm2 {H : Type*}
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
  have hyoung := metric_young_from_two_sided_inverse_thm2 L Linv hL hLpos hcomp p r
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
  have hpol := weighted_polarization_thm2 M hM u w 0
  have hr : r = u - w := by rw [hur]; abel
  rw [hr] at hMr
  rw [hr]
  simp only [sub_zero] at hpol
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
  nlinarith [hpol]

/-- A positive-definite metric has a nonnegative associated quadratic form. -/
private theorem quadratic_nonneg_of_posdef_thm2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (P : H →L[ℝ] H)
    (hP : ∀ u, u ≠ 0 → 0 < inner ℝ (P u) u) (u : H) :
    0 ≤ (1 / 2 : ℝ) * inner ℝ (P u) u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact mul_nonneg (by norm_num) (le_of_lt (hP u hu))

/-- The finite telescoping identity used for the Lyapunov decrement. -/
private theorem sum_range_sub_telescope_thm2 (g : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (g i - g (i + 1)) = g 0 - g N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The quadratic form of the Lyapunov metric dominates `ε` times that of `M`. -/
private theorem quadratic_R_dominates_M_thm2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M L : H →L[ℝ] H) (α ell : ℕ → ℝ) (ε : ℝ)
    (hε : ∀ k u, 0 ≤ inner ℝ
      ((((1 - 3 * α k) • M) - (((1 - α k)^2 * ell k / 2) • L) - ε • M) u) u)
    (k : ℕ) (u : H) :
    ε * ((1 / 2 : ℝ) * inner ℝ (M u) u) ≤
      (1 / 2 : ℝ) * inner ℝ
        (((1 - 3 * α k) • M - ((1 - α k)^2 * ell k / 2) • L) u) u := by
  have h := hε k u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at h ⊢
  nlinarith

set_option maxHeartbeats 800000 in
/-- Theorem 2: the Lyapunov condition (17) guarantees the summability required
by Theorem 1 for monotone step and inertial sequences. -/
theorem inertial_lyapunov_condition_implies_weak_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : SetValuedOperator H H) (B : H → H)
    (M L Linv : H →L[ℝ] H) (α ell : ℕ → ℝ)
    (it : InertialForwardBackwardIteration H A B M α ell) (S : Set H)
    (hmaxA : SetValuedOperator.IsMaximalMonotone A)
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
      (A + SetValuedOperator.ofFunction Set.univ
        (fun x : (Set.univ : Set H) ↦ B x.1)))
    (hell_lower : ∃ l0 : ℝ, 0 < l0 ∧ ∀ k, l0 ≤ ell k)
    (hα_mono : Monotone α) (hell_mono : Monotone ell)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ k u, 0 ≤ inner ℝ
      ((((1 - 3 * α k) • M) - (((1 - α k)^2 * ell k / 2) • L) - ε • M) u) u)
    :
    ∃ z ∈ S, Tendsto (fun k ↦ toWeakSpace ℝ H (it.x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  rcases hS_nonempty with ⟨z, hzS⟩
  have hz : ∃ a ∈ A z, a + B z = 0 := by rw [hsolution] at hzS; exact hzS
  rcases hz with ⟨az, haz, hzero⟩
  have hminusB : -B z ∈ A z := by
    rw [← (eq_neg_iff_add_eq_zero.mpr hzero)]
    exact haz
  choose a ha hfb using it.forward_backward
  have hmonotonicity (k : ℕ) :
      0 ≤ inner ℝ (a k + B z) (it.x (k + 1) - z) := by
    have hmono := hmaxA.1 (a k) (ha k) (-B z) hminusB
    simpa [sub_eq_add_neg] using hmono
  have hgraph (k : ℕ) :
      0 ≤ inner ℝ
        (M (it.y k - it.x (k + 1)) - ell k • (B (it.y k) - B z))
        (it.x (k + 1) - z) := by
    have hscaled : 0 ≤ inner ℝ (ell k • (a k + B z)) (it.x (k + 1) - z) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      exact mul_nonneg (le_of_lt (hell k)) (hmonotonicity k)
    have heq : ell k • (a k + B z) =
        M (it.y k - it.x (k + 1)) - ell k • (B (it.y k) - B z) := by
      rw [smul_add, ← hfb k]
      module
    rw [heq] at hscaled
    exact hscaled
  rcases hα with ⟨αbar, hαbar_lt, hαrange⟩
  rcases hε with ⟨ε, hε_pos, hε⟩
  let d : ℕ → H := fun k ↦ it.x k - it.x (k - 1)
  let q : (H →L[ℝ] H) → H → ℝ :=
    fun P u ↦ (1 / 2 : ℝ) * inner ℝ (P u) u
  let Smet : ℕ → H →L[ℝ] H := fun k ↦ M - (ell k / 2) • L
  let Tmet : ℕ → H →L[ℝ] H :=
    fun k ↦ (2 : ℝ) • M - ((1 - α k) * ell k / 2) • L
  let Rmet : ℕ → H →L[ℝ] H :=
    fun k ↦ (1 - 3 * α k) • M - ((1 - α k)^2 * ell k / 2) • L
  let φ : ℕ → ℝ := fun k ↦ q M (it.x k - z)
  have hqM_nonneg (u : H) : 0 ≤ q M u := by
    exact quadratic_nonneg_of_posdef_thm2 M it.metric_positive_definite u
  have hqS_nonneg (k : ℕ) (u : H) : 0 ≤ q (Smet k) u := by
    exact quadratic_nonneg_of_posdef_thm2 (Smet k) (hmetric k) u
  have hR_dominates (k : ℕ) (u : H) : ε * q M u ≤ q (Rmet k) u := by
    simpa [q, Rmet] using quadratic_R_dominates_M_thm2 M L α ell ε hε k u
  have hstep (k : ℕ) :
      φ (k + 1) - q M (it.y k - z) ≤
        -q (Smet k) (it.x (k + 1) - it.y k) := by
    have hcoco : inner ℝ (Linv (B (it.y k) - B z)) (B (it.y k) - B z) ≤
        inner ℝ (B (it.y k) - B z) (it.y k - z) := by
      exact hcocoercive (it.y k) z hzS
    have hur : it.x (k + 1) - z = (it.y k - z) + (it.x (k + 1) - it.y k) := by
      abel
    have hg : 0 ≤ inner ℝ
        (M (-(it.x (k + 1) - it.y k)) - ell k • (B (it.y k) - B z))
        (it.x (k + 1) - z) := by
      rw [show -(it.x (k + 1) - it.y k) = it.y k - it.x (k + 1) by abel]
      exact hgraph k
    simpa [φ, q, Smet] using
      (forward_backward_energy_step_thm2 M L Linv (ell k) (it.x (k + 1) - z)
        (it.y k - z) (it.x (k + 1) - it.y k) (B (it.y k) - B z)
        it.metric_self_adjoint hL_selfadjoint hL_positive_definite hLcomp
        (le_of_lt (hell k)) hur hg hcoco)
  have hmetric_compare (k : ℕ) (u : H) :
      (α k - 1) * q (Smet k) u + α (k + 1) * q (Tmet (k + 1)) u ≤
        -q (Rmet (k + 1)) u := by
    have hab : α k ≤ α (k + 1) := hα_mono (Nat.le_succ k)
    have hb : 0 ≤ 1 - α (k + 1) := by
      have := (hαrange (k + 1)).2
      linarith
    have hel : ell k ≤ ell (k + 1) := hell_mono (Nat.le_succ k)
    have hprod : (1 - α (k + 1)) * ell k ≤
        (1 - α (k + 1)) * ell (k + 1) :=
      mul_le_mul_of_nonneg_left hel hb
    have hm : 0 ≤ inner ℝ (M u) u - (ell k / 2) * inner ℝ (L u) u := by
      have hs := hqS_nonneg k u
      simp only [q, Smet, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at hs
      nlinarith
    have hl : 0 ≤ inner ℝ (L u) u := by
      by_cases hu : u = 0
      · simp [hu]
      · exact le_of_lt (hL_positive_definite u hu)
    have hcoef :
        ((1 - α k) * ell k - (1 - α (k + 1)) * ell (k + 1)) / 2 ≤
          (α (k + 1) - α k) * ell k / 2 := by
      nlinarith
    have hcoef_mul := mul_le_mul_of_nonneg_right hcoef hl
    have hdelta := mul_nonneg (sub_nonneg.mpr hab) hm
    simp only [q, Smet, Tmet, Rmet, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial]
    nlinarith
  have hqR_nonneg (k : ℕ) (u : H) : 0 ≤ q (Rmet k) u := by
    exact le_trans (mul_nonneg (le_of_lt hε_pos) (hqM_nonneg u)) (hR_dominates k u)
  have hqL_nonneg (u : H) : 0 ≤ q L u := by
    exact quadratic_nonneg_of_posdef_thm2 L hL_positive_definite u
  have hqT_nonneg (k : ℕ) (u : H) : 0 ≤ q (Tmet k) u := by
    have hαk := (hαrange k).1
    have hellk := le_of_lt (hell k)
    have hmul : 0 ≤ α k * ell k := mul_nonneg hαk hellk
    have hM := hqM_nonneg u
    have hS := hqS_nonneg k u
    have hL := hqL_nonneg u
    simp only [q, Smet, Tmet, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial] at hM hS hL ⊢
    nlinarith
  have hrec (k : ℕ) :
      φ (k + 1) - φ k - α k * (φ k - φ (k - 1)) ≤
        (α k - 1) * q (Smet k) (d (k + 1)) +
          α k * q (Tmet k) (d k) := by
    have hy : it.y k - z = (it.x k - z) + α k • d k := by
      rw [it.inertial]
      dsimp [d]
      abel
    have hr : it.x (k + 1) - it.y k = d (k + 1) - α k • d k := by
      rw [it.inertial]
      dsimp [d]
      abel
    have hSself : ∀ u v, inner ℝ (Smet k u) v = inner ℝ u (Smet k v) := by
      intro u v
      simp only [Smet, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, inner_smul_left, inner_sub_right, inner_smul_right,
        starRingEnd_apply, star_trivial]
      rw [it.metric_self_adjoint, hL_selfadjoint]
    have hcross := inertial_cross_term_bound (Smet k) hSself
      (fun u => by simpa [q] using hqS_nonneg k u) (d (k + 1)) (d k) (α k)
      (hαrange k).1
    have hpol := weighted_polarization_thm2 M it.metric_self_adjoint
      (it.x k) (it.x (k - 1)) z
    have hs := hstep k
    rw [hy, hr] at hs
    have hMexp : q M (it.x k - z + α k • d k) =
        φ k + α k * (φ k - φ (k - 1)) +
          α k * (1 + α k) * q M (d k) := by
      have hcrossM : inner ℝ (M (it.x k - z)) (it.x k - it.x (k - 1)) =
          (1 / 2 : ℝ) * (inner ℝ (M (it.x k - it.x (k - 1)))
            (it.x k - it.x (k - 1)) + inner ℝ (M (it.x k - z)) (it.x k - z) -
              inner ℝ (M (it.x (k - 1) - z)) (it.x (k - 1) - z)) := by
        calc
          inner ℝ (M (it.x k - z)) (it.x k - it.x (k - 1)) =
              inner ℝ (it.x k - z) (M (it.x k - it.x (k - 1))) :=
                it.metric_self_adjoint _ _
          _ = inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - z) :=
                real_inner_comm _ _
          _ = _ := hpol
      dsimp [q, φ, d]
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
      linear_combination (α k / 2) * hpol + (α k / 2) * hcrossM
    have hSsym : inner ℝ (Smet k (d k)) (d (k + 1)) =
        inner ℝ (Smet k (d (k + 1))) (d k) := by
      calc
        inner ℝ (Smet k (d k)) (d (k + 1)) =
            inner ℝ (d k) (Smet k (d (k + 1))) := hSself _ _
        _ = _ := real_inner_comm _ _
    have hSexp : q (Smet k) (d (k + 1) - α k • d k) =
        q (Smet k) (d (k + 1)) + (α k)^2 * q (Smet k) (d k) -
          α k * inner ℝ (Smet k (d (k + 1))) (d k) := by
      dsimp [q]
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
      rw [hSsym]
      ring
    have hT : α k * (1 + α k) * q M (d k) +
        (α k - (α k)^2) * q (Smet k) (d k) = α k * q (Tmet k) (d k) := by
      dsimp [q, Smet, Tmet]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
      ring
    rw [hMexp, hSexp] at hs
    dsimp [q] at hs hcross hT ⊢
    ring_nf at hs hcross hT ⊢
    linarith
  let μ : ℕ → ℝ := fun k ↦
    φ k - α k * φ (k - 1) + α k * q (Tmet k) (d k)
  have hmu_dec (k : ℕ) :
      μ (k + 1) - μ k ≤ -q (Rmet (k + 1)) (d (k + 1)) := by
    have hαdiff : 0 ≤ α (k + 1) - α k := by
      exact sub_nonneg.mpr (hα_mono (Nat.le_succ k))
    have hφ_nonneg : 0 ≤ φ k := by
      simpa [φ] using hqM_nonneg (it.x k - z)
    have hdrop : -(α (k + 1) - α k) * φ k ≤ 0 := by
      nlinarith
    have hc := hmetric_compare k (d (k + 1))
    dsimp [μ]
    linarith [hrec k]
  have hmu_mono (k : ℕ) : μ (k + 1) ≤ μ k := by
    have hR : 0 ≤ q (Rmet (k + 1)) (d (k + 1)) := hqR_nonneg _ _
    linarith [hmu_dec k]
  have hmu_le_zero : ∀ k, μ k ≤ μ 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact le_trans (hmu_mono k) ih
  let Cφ : ℝ := φ 0 + |μ 0| / (1 - αbar)
  have hden : 0 < 1 - αbar := by linarith
  have hC_nonneg : 0 ≤ Cφ := by
    dsimp [Cφ]
    have hφ0 : 0 ≤ φ 0 := by simpa [φ] using hqM_nonneg (it.x 0 - z)
    positivity
  have hmu_rearr (k : ℕ) : φ k - α k * φ (k - 1) ≤ μ 0 := by
    have hT : 0 ≤ α k * q (Tmet k) (d k) :=
      mul_nonneg (hαrange k).1 (hqT_nonneg k _)
    dsimp [μ] at hmu_le_zero
    linarith [hmu_le_zero k]
  have hphi_step (k : ℕ) : φ (k + 1) ≤ α (k + 1) * φ k + μ 0 := by
    have h := hmu_rearr (k + 1)
    rw [Nat.succ_sub_one] at h
    linarith
  have hC_majorizes : μ 0 ≤ (1 - αbar) * Cφ := by
    have hφ0 : 0 ≤ φ 0 := by simpa [φ] using hqM_nonneg (it.x 0 - z)
    have hfactor : 0 ≤ (1 - αbar) * φ 0 := mul_nonneg hden.le hφ0
    dsimp [Cφ]
    field_simp [hden.ne']
    linarith [le_abs_self (μ 0)]
  have hphi_bound : ∀ k, φ k ≤ Cφ := by
    intro k
    induction k with
    | zero =>
        dsimp [Cφ]
        have : 0 ≤ |μ 0| / (1 - αbar) := div_nonneg (abs_nonneg _) hden.le
        linarith
    | succ k ih =>
        have ha0 := (hαrange (k + 1)).1
        have ha := (hαrange (k + 1)).2
        have hbar : 0 ≤ αbar := le_trans ha0 ha
        have hφk : 0 ≤ φ k := by simpa [φ] using hqM_nonneg (it.x k - z)
        have hs := hphi_step k
        have hmul : α (k + 1) * φ k ≤ αbar * Cφ := by
          exact mul_le_mul ha ih hφk hbar
        linarith [hC_majorizes]
  have hmu_lower (N : ℕ) : -αbar * Cφ ≤ μ N := by
    have hφN : 0 ≤ φ N := by simpa [φ] using hqM_nonneg (it.x N - z)
    have hαN0 := (hαrange N).1
    have hαN := (hαrange N).2
    have hφprev := hphi_bound (N - 1)
    have hT : 0 ≤ α N * q (Tmet N) (d N) :=
      mul_nonneg hαN0 (hqT_nonneg N _)
    dsimp [μ]
    nlinarith [mul_le_mul_of_nonneg_left hφprev hαN0,
      mul_le_mul_of_nonneg_right hαN hC_nonneg]
  have hsum_R (N : ℕ) :
      ∑ i ∈ Finset.range N, q (Rmet (i + 1)) (d (i + 1)) ≤ μ 0 + αbar * Cφ := by
    have hterm (i : ℕ) : q (Rmet (i + 1)) (d (i + 1)) ≤ μ i - μ (i + 1) := by
      linarith [hmu_dec i]
    calc
      ∑ i ∈ Finset.range N, q (Rmet (i + 1)) (d (i + 1)) ≤
          ∑ i ∈ Finset.range N, (μ i - μ (i + 1)) :=
            Finset.sum_le_sum (fun i hi => hterm i)
      _ = μ 0 - μ N := sum_range_sub_telescope_thm2 μ N
      _ ≤ μ 0 + αbar * Cφ := by linarith [hmu_lower N]
  have hsummable : Summable (fun k ↦ α k *
      inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - it.x (k - 1))) := by
    let g : ℕ → ℝ := fun k ↦ α k *
      inner ℝ (M (it.x k - it.x (k - 1))) (it.x k - it.x (k - 1))
    change Summable g
    let f : ℕ → ℝ := fun i ↦ g (i + 1)
    have hf_nonneg (i : ℕ) : 0 ≤ f i := by
      dsimp [f]
      have hinner : 0 ≤ inner ℝ (M (d (i + 1))) (d (i + 1)) := by
        dsimp [q] at hqM_nonneg
        nlinarith [hqM_nonneg (d (i + 1))]
      exact mul_nonneg (hαrange _).1 hinner
    have hmult_nonneg : 0 ≤ 2 * αbar / ε := by
      have hbar : 0 ≤ αbar := le_trans (hαrange 0).1 (hαrange 0).2
      positivity
    have hdom (i : ℕ) : f i ≤ (2 * αbar / ε) *
        q (Rmet (i + 1)) (d (i + 1)) := by
      have hεq := hR_dominates (i + 1) (d (i + 1))
      have hqR := hqR_nonneg (i + 1) (d (i + 1))
      have hcoef : 2 * α (i + 1) / ε ≤ 2 * αbar / ε := by
        apply div_le_div_of_nonneg_right
        · nlinarith [(hαrange (i + 1)).2]
        · linarith
      have hcoef_nonneg : 0 ≤ 2 * α (i + 1) / ε := by
        exact div_nonneg (mul_nonneg (by norm_num) (hαrange _).1) hε_pos.le
      have hscaled := mul_le_mul_of_nonneg_left hεq hcoef_nonneg
      have hreplace := mul_le_mul_of_nonneg_right hcoef hqR
      dsimp [f, q]
      calc
        α (i + 1) * inner ℝ (M (d (i + 1))) (d (i + 1)) =
            2 * α (i + 1) * ((1 / 2 : ℝ) *
              inner ℝ (M (d (i + 1))) (d (i + 1))) := by ring
        _ = (2 * α (i + 1) / ε) * (ε * ((1 / 2 : ℝ) *
              inner ℝ (M (d (i + 1))) (d (i + 1)))) := by field_simp
        _ ≤ (2 * α (i + 1) / ε) * q (Rmet (i + 1)) (d (i + 1)) := hscaled
        _ ≤ (2 * αbar / ε) * q (Rmet (i + 1)) (d (i + 1)) := hreplace
    have hbound_nonneg : 0 ≤ μ 0 + αbar * Cφ := by
      simpa using hsum_R 0
    have hsum_f (N : ℕ) : ∑ i ∈ Finset.range N, f i ≤
        (2 * αbar / ε) * (μ 0 + αbar * Cφ) := by
      calc
        ∑ i ∈ Finset.range N, f i ≤ ∑ i ∈ Finset.range N,
            (2 * αbar / ε) * q (Rmet (i + 1)) (d (i + 1)) :=
              Finset.sum_le_sum (fun i hi => hdom i)
        _ = (2 * αbar / ε) * ∑ i ∈ Finset.range N,
            q (Rmet (i + 1)) (d (i + 1)) := by rw [Finset.mul_sum]
        _ ≤ (2 * αbar / ε) * (μ 0 + αbar * Cφ) :=
              mul_le_mul_of_nonneg_left (hsum_R N) hmult_nonneg
    have hsucc : Summable f := summable_of_sum_range_le hf_nonneg hsum_f
    have htail : Summable (fun k ↦ g (k + 1)) := by
      simpa [f, g, d] using hsucc
    exact (summable_nat_add_iff (f := g) 1).mp (by simpa [Nat.add_comm] using htail)
  have hS_nonempty' : S.Nonempty := ⟨z, hzS⟩
  exact inertial_forward_backward_weakly_converges A B M L Linv α ell it S
    hmaxA hmaxB hsolution hS_nonempty' hLinv hLcomp hB_lipschitz
    hL_selfadjoint hL_positive_definite hcocoercive hell
    ⟨αbar, hαbar_lt, hαrange⟩ hmetric hM_coercive hS_coercive
    hsummax hell_lower hsummable

end LorenzPock
