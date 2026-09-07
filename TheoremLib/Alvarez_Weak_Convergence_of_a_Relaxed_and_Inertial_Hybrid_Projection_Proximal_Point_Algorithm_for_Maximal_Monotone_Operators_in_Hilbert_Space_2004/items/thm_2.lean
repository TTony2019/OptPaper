import Mathlib.Tactic
import Foundation.SetValued.Yosida
import Foundation.SetValued.Minty
import Foundation.SetValued.MaximalMonotone
import Foundation.FixedPoint.Nonexpansive
import Foundation.Hilbert.WeakConvergence
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.lem_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.lem_3
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.thm_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.ext_def_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.ext_thm_1

set_option maxHeartbeats 800000

/-!
# Theorem 3.1
-/

open SetValuedOperator
open Filter
open scoped Topology Pointwise InnerProductSpace

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Difference-of-squares identity used in the inertial expansion. -/
theorem inner_norm_sq_diff_eq_thm2 (a b : H) :
    ‖a‖ ^ 2 - ‖b‖ ^ 2 = 2 * ⟪a, a - b⟫_ℝ - ‖a - b‖ ^ 2 := by
  rw [norm_sub_sq_real]
  have hself : ⟪a, a⟫_ℝ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
  rw [inner_sub_right, hself]
  ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The coefficient appearing in the inertial error is dominated by `alpha`. -/
theorem inertial_delta_summable_thm2
    (x : ℕ → H) (alpha : ℕ → ℝ)
    (halpha_summable : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2)
    (halpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1) :
    Summable fun k : ℕ ↦
      ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 := by
  refine halpha_summable.of_nonneg_of_le ?hnonneg ?hle
  · intro k
    have ha0 : 0 ≤ alpha k := (halpha_mem k).1
    have hs : 0 ≤ ‖x k - x (k - 1)‖ ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (alpha k)]
  · intro k
    have ha0 : 0 ≤ alpha k := (halpha_mem k).1
    have ha1 : alpha k ≤ 1 := le_of_lt (halpha_mem k).2
    have hasq_le : alpha k ^ 2 ≤ alpha k := by
      nlinarith [sq_nonneg (alpha k), mul_le_mul_of_nonneg_left ha1 ha0]
    have hs : 0 ≤ ‖x k - x (k - 1)‖ ^ 2 := sq_nonneg _
    have hcoef : (alpha k + alpha k ^ 2) / 2 ≤ alpha k := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoef hs

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The inertial step length weighted by `alpha` tends to zero when the squared
weighted step lengths are summable. -/
theorem alpha_diff_norm_tendsto_zero_thm2
    (x : ℕ → H) (alpha : ℕ → ℝ)
    (halpha_summable : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2)
    (halpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1) :
    Tendsto (fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖) atTop (𝓝 0) := by
  have hsq_tendsto :
      Tendsto (fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2) atTop (𝓝 0) :=
    halpha_summable.tendsto_cofinite_zero.mono_left Filter.atTop_le_cofinite
  have hprod_sq_tendsto :
      Tendsto (fun k : ℕ ↦ (alpha k * ‖x k - x (k - 1)‖) ^ 2) atTop
        (𝓝 0) := by
    refine squeeze_zero (fun k => sq_nonneg _) ?_ hsq_tendsto
    intro k
    have ha0 : 0 ≤ alpha k := (halpha_mem k).1
    have ha1 : alpha k ≤ 1 := le_of_lt (halpha_mem k).2
    have hn : 0 ≤ ‖x k - x (k - 1)‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right ha1 hn]
  have hsqrt :
      Tendsto (fun k : ℕ ↦ Real.sqrt ((alpha k * ‖x k - x (k - 1)‖) ^ 2))
        atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hprod_sq_tendsto
  have hnonneg (k : ℕ) : 0 ≤ alpha k * ‖x k - x (k - 1)‖ :=
    mul_nonneg (halpha_mem k).1 (norm_nonneg _)
  simpa [Real.sqrt_sq (hnonneg _)] using hsqrt

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- If the weighted residual norms are summable with positive weights, then their
squares are summable. -/
theorem lam_sq_eta_sq_summable_thm2
    {eta : ℕ → H} {lam : ℕ → ℝ}
    (hlam_pos : ∀ k : ℕ, 0 < lam k)
    (h31 : Summable fun k : ℕ ↦ lam k * ‖eta k‖) :
    Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖eta k‖ ^ 2 := by
  let f : ℕ → ℝ := fun k => lam k * ‖eta k‖
  have hf_tendsto : Tendsto f atTop (𝓝 0) :=
    h31.tendsto_cofinite_zero.mono_left Filter.atTop_le_cofinite
  have hevent_lt : ∀ᶠ k in atTop, f k < 1 :=
    hf_tendsto.eventually_lt_const zero_lt_one
  have hbound_atTop :
      ∀ᶠ k in atTop, ‖(lam k) ^ 2 * ‖eta k‖ ^ 2‖ ≤ lam k * ‖eta k‖ := by
    filter_upwards [hevent_lt] with k hk
    have hf_nonneg : 0 ≤ f k := mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
    have hsquare : (lam k) ^ 2 * ‖eta k‖ ^ 2 = (f k) ^ 2 := by
      dsimp [f]
      ring
    have hsq_nonneg : 0 ≤ (f k) ^ 2 := sq_nonneg _
    have hsq_le : (f k) ^ 2 ≤ f k := by nlinarith
    rw [hsquare, Real.norm_of_nonneg hsq_nonneg]
    exact hsq_le
  exact Summable.of_norm_bounded_eventually_nat h31 hbound_atTop

omit [CompleteSpace H] in
/-- A firmly nonexpansive map on the whole Hilbert space is `1`-cocoercive. -/
theorem firmly_nonexpansive_cocoerciveOn_one_thm2 {T : H → H}
    (hT : FirmlyNonexpansive T) :
    CocoerciveOn (1 : ℝ) Set.univ (fun x : Set.univ ↦ T x) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner] at hT
  constructor
  · norm_num
  · intro x y
    simpa [real_inner_comm] using hT x y

omit [CompleteSpace H] in
/-- A firmly nonexpansive map on a subtype domain is `1`-cocoercive. -/
theorem firmly_nonexpansiveOn_cocoerciveOn_one_thm2 {D : Set H} {T : D → H}
    (hT : FirmlyNonexpansiveOn D T) :
    CocoerciveOn (1 : ℝ) D T := by
  rw [firmlyNonexpansiveOn_iff] at hT
  constructor
  · norm_num
  · intro x y
    simpa [real_inner_comm] using hT x y

omit [CompleteSpace H] in
/-- Scaling the residual of a firmly nonexpansive map by a positive `lam` gives the
usual `lam`-cocoercivity inequality for the single-valued Yosida representative. -/
theorem scaled_residual_cocoercive_thm2 (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hres : CocoerciveOn (1 : ℝ) Set.univ
      (residualMap Set.univ (fun z : Set.univ ↦ J z)))
    (x y : H) :
    lam * ‖(lam⁻¹ • (x - J x)) - (lam⁻¹ • (y - J y))‖ ^ 2 ≤
      inner ℝ ((lam⁻¹ • (x - J x)) - (lam⁻¹ • (y - J y))) (x - y) := by
  let Rdiff : H := (x - J x) - (y - J y)
  have hresxy : ‖Rdiff‖ ^ 2 ≤ inner ℝ (x - y) Rdiff := by
    have h := hres.ineq (⟨x, by simp⟩ : (Set.univ : Set H))
      (⟨y, by simp⟩ : (Set.univ : Set H))
    dsimp [residualMap] at h
    simpa [Rdiff] using h
  have hA :
      (lam⁻¹ • (x - J x)) - (lam⁻¹ • (y - J y)) = lam⁻¹ • Rdiff := by
    dsimp [Rdiff]
    rw [← smul_sub]
  rw [hA, norm_smul, real_inner_smul_left]
  have hinv_pos : 0 < lam⁻¹ := inv_pos.mpr hlam
  have habs : ‖lam⁻¹‖ = lam⁻¹ := abs_of_pos hinv_pos
  rw [habs]
  have hnonneg : 0 ≤ lam⁻¹ := le_of_lt hinv_pos
  have hmain : lam * (lam⁻¹ * ‖Rdiff‖) ^ 2 ≤ lam⁻¹ * inner ℝ (x - y) Rdiff := by
    calc
      lam * (lam⁻¹ * ‖Rdiff‖) ^ 2 = lam⁻¹ * ‖Rdiff‖ ^ 2 := by
        field_simp [hlam.ne']
      _ ≤ lam⁻¹ * inner ℝ (x - y) Rdiff :=
        mul_le_mul_of_nonneg_left hresxy hnonneg
  convert hmain using 1
  · rw [real_inner_comm]

omit [CompleteSpace H] in
/-- The inertial identity used to pass from `y k` back to the scalar energy of
`x k`. -/
theorem inertial_expansion_y_thm2
    (x y : ℕ → H) (alpha : ℕ → ℝ)
    (hy : ∀ k : ℕ, y k = x k + alpha k • (x k - x (k - 1)))
    (k : ℕ) (xbar : H) :
    (1 / 2 : ℝ) * ‖y k - xbar‖ ^ 2 =
      (1 / 2) * ‖x k - xbar‖ ^ 2 +
        alpha k * ((1 / 2) * ‖x k - xbar‖ ^ 2 -
          (1 / 2) * ‖x (k - 1) - xbar‖ ^ 2) +
        ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 := by
  rw [hy k]
  have h_y : x k + alpha k • (x k - x (k - 1)) - xbar =
      (x k - xbar) + alpha k • (x k - x (k - 1)) := by
    module
  rw [h_y]
  let a : H := x k - xbar
  let d : H := x k - x (k - 1)
  have hprev : x (k - 1) - xbar = a - d := by
    dsimp [a, d]
    module
  have hnorm : ‖a + alpha k • d‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * alpha k * inner ℝ a d + (alpha k) ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have hdiff := inner_norm_sq_diff_eq_thm2 a (a - d)
  have had : a - (a - d) = d := by
    module
  rw [had] at hdiff
  have hinner : 2 * inner ℝ a d = ‖a‖ ^ 2 - ‖a - d‖ ^ 2 + ‖d‖ ^ 2 := by
    nlinarith
  have htwo : 2 * alpha k * inner ℝ a d =
      alpha k * (‖a‖ ^ 2 - ‖a - d‖ ^ 2 + ‖d‖ ^ 2) := by
    calc
      2 * alpha k * inner ℝ a d = alpha k * (2 * inner ℝ a d) := by ring
      _ = alpha k * (‖a‖ ^ 2 - ‖a - d‖ ^ 2 + ‖d‖ ^ 2) := by rw [hinner]
  rw [show x k - xbar = a by rfl]
  rw [show x k - x (k - 1) = d by rfl]
  rw [hprev]
  rw [hnorm, htwo]
  ring

omit [CompleteSpace H] in
/-- Any everywhere-defined selection of the resolvent of a monotone operator is firmly
nonexpansive. This is the firm form needed for the Yosida cocoercivity step. -/
theorem firmly_nonexpansive_resolvent_selection_thm2
    {A : SetValuedOperator H H} (hA_mono : SetValuedOperator.IsMonotone A)
    (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : ∀ x : H, J x ∈ J[(lam • A)] x) :
    FirmlyNonexpansive J := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  have hx := hJ x
  have hy := hJ y
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hx hy
  dsimp [SetValuedOperator.identityAddScaled] at hx hy
  rcases hx with ⟨ax, hax, hxeq⟩
  rcases hy with ⟨ay, hay, hyeq⟩
  have h_ident : ⟪J x - J y, x - y⟫_ℝ - ‖J x - J y‖ ^ 2 =
      lam * ⟪ax - ay, J x - J y⟫_ℝ := by
    calc
      ⟪J x - J y, x - y⟫_ℝ - ‖J x - J y‖ ^ 2
          = ⟪J x - J y, (J x + lam • ax) - (J y + lam • ay)⟫_ℝ -
              ‖J x - J y‖ ^ 2 := by
            rw [hxeq, hyeq]
      _ = ⟪J x - J y, (J x - J y) + lam • (ax - ay)⟫_ℝ -
              ‖J x - J y‖ ^ 2 := by
            have hv :
                (J x + lam • ax) - (J y + lam • ay) =
                  (J x - J y) + lam • (ax - ay) := by
              rw [smul_sub]
              abel
            rw [hv]
      _ = (‖J x - J y‖ ^ 2 + lam * ⟪ax - ay, J x - J y⟫_ℝ) -
              ‖J x - J y‖ ^ 2 := by
            rw [inner_add_right, real_inner_self_eq_norm_sq, real_inner_smul_right,
              real_inner_comm (J x - J y)]
      _ = lam * ⟪ax - ay, J x - J y⟫_ℝ := by ring
  have hmono : 0 ≤ ⟪ax - ay, J x - J y⟫_ℝ := hA_mono ax hax ay hay
  nlinarith

omit [CompleteSpace H] in
/-- For a resolvent selection, the single-valued Yosida representative vanishes
exactly at zeros of the operator. -/
theorem yosida_selection_eq_zero_iff_thm2
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    {lam : ℝ} (hlam : 0 < lam) (J : H → H)
    (hJ : ∀ x : H, J x ∈ J[(lam • A)] x) (x : H) :
    (0 : H) ∈ A x ↔ lam⁻¹ • (x - J x) = 0 := by
  constructor
  · intro hzero
    have hx_res : x ∈ J[(lam • A)] x :=
      (Alvarez2004.resolvent_fixed_iff_zero A hA hlam x).mpr hzero
    have hsingle := resolvent_is_at_most_single_valued A hA hlam
    have hJx : J x = x := hsingle x (hJ x) hx_res
    simp [hJx]
  · intro hyos
    have hdiff : x - J x = 0 := by
      have hlam_inv_ne : lam⁻¹ ≠ 0 := inv_ne_zero hlam.ne'
      exact (smul_eq_zero.mp hyos).elim (fun h => (hlam_inv_ne h).elim) id
    have hJx : J x = x := by
      exact (sub_eq_zero.mp hdiff).symm
    have hx_res : x ∈ J[(lam • A)] x := by
      simpa [hJx] using hJ x
    exact (Alvarez2004.resolvent_fixed_iff_zero A hA hlam x).mp hx_res

omit [CompleteSpace H] in
/-- Positive scalar multiples of maximal monotone operators are maximal monotone. -/
private theorem scale_maximal_monotone {A : SetValuedOperator H H}
    (hA : SetValuedOperator.IsMaximalMonotone A) {c : ℝ} (hc : 0 < c) :
    SetValuedOperator.IsMaximalMonotone (fun x : H ↦ c • A x) := by
  let S : SetValuedOperator H H := fun x : H => c • A x
  have hS_mono : SetValuedOperator.IsMonotone S := by
    intro x y u hu v hv
    dsimp [S] at hu hv
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨b, hb, rfl⟩
    have hmono := hA.1 a ha b hb
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg (le_of_lt hc) hmono
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
    have hmono := hB_mono u hu v hv
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hc)) hmono
  have hA_subset_C : A.graph ⊆ C.graph := by
    intro p hpA
    rcases p with ⟨z, a⟩
    change a ∈ A z at hpA
    change a ∈ C z
    dsimp [C]
    refine ⟨c • a, ?_, ?_⟩
    · have hS_mem : c • a ∈ S z := by
        dsimp [S]
        exact ⟨a, hpA, rfl⟩
      exact (SetValuedOperator.mem_graph_iff B z (c • a)).mp
        (hsubset ((SetValuedOperator.mem_graph_iff S z (c • a)).mpr hS_mem))
    · simp [smul_smul, inv_mul_cancel₀ hc.ne']
  have hC_subset_A : C.graph ⊆ A.graph := hA.2 C hC_mono hA_subset_C
  change u ∈ S x
  dsimp [S]
  refine ⟨c⁻¹ • u, ?_, ?_⟩
  · exact (SetValuedOperator.mem_graph_iff A x (c⁻¹ • u)).mp
      (hC_subset_A ((SetValuedOperator.mem_graph_iff C x (c⁻¹ • u)).mpr (by
        dsimp [C]
        exact ⟨u, hp, rfl⟩)))
  · simp [smul_smul, mul_inv_cancel₀ hc.ne']

/-- Maximal monotonicity makes every positive-parameter resolvent nonempty. -/
private theorem resolvent_nonempty {A : SetValuedOperator H H}
    (hA : SetValuedOperator.IsMaximalMonotone A) {lam : ℝ} (hlam : 0 < lam) (y : H) :
    (J[(lam • A)] y).Nonempty := by
  have hsurj :=
    minty_surjective_of_maximal_monotone
      (T := fun x : H => lam • A x) (scale_maximal_monotone hA hlam) y
  rcases hsurj with ⟨x, u, hu, hy_eq⟩
  rcases hu with ⟨a, ha, rfl⟩
  refine ⟨x, ?_⟩
  rw [SetValuedOperator.mem_resolvent_smul_iff]
  dsimp [SetValuedOperator.identityAddScaled]
  exact ⟨a, ha, hy_eq.symm⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A summable weighted residual with weights bounded below has residual norm tending to zero. -/
private theorem eta_norm_tendsto_zero
    {eta : ℕ → H} {lam : ℕ → ℝ}
    (hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k)
    (h31 : Summable fun k : ℕ ↦ lam k * ‖eta k‖) :
    Tendsto (fun k : ℕ ↦ ‖eta k‖) atTop (𝓝 0) := by
  rcases hlam_lower with ⟨lam0, hlam0_pos, hlam0_le⟩
  have hterm : Tendsto (fun k : ℕ ↦ lam k * ‖eta k‖) atTop (𝓝 0) :=
    h31.tendsto_cofinite_zero.mono_left Filter.atTop_le_cofinite
  refine squeeze_zero
    (f := fun k : ℕ => ‖eta k‖)
    (g := fun k : ℕ => lam0⁻¹ * (lam k * ‖eta k‖))
    (fun k : ℕ => norm_nonneg (eta k)) ?_ ?_
  · intro k
    have hmul : lam0 * ‖eta k‖ ≤ lam k * ‖eta k‖ :=
      mul_le_mul_of_nonneg_right (hlam0_le k) (norm_nonneg (eta k))
    have hinv_nonneg : 0 ≤ lam0⁻¹ := le_of_lt (inv_pos.mpr hlam0_pos)
    calc
      ‖eta k‖ = lam0⁻¹ * (lam0 * ‖eta k‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hlam0_pos.ne', one_mul]
      _ ≤ lam0⁻¹ * (lam k * ‖eta k‖) :=
        mul_le_mul_of_nonneg_left hmul hinv_nonneg
  · simpa using hterm.const_mul lam0⁻¹

/-- The inexact proximal-point recurrence (3.2). -/
structure InexactProximalRecurrence
    (A : SetValuedOperator H H) (x y v eta : ℕ → H) (lam alpha rho : ℕ → ℝ) where
  y_def : ∀ k : ℕ, y k = x k + alpha k • (x k - x (k - 1))
  equation :
    ∀ k : ℕ, (lam k)⁻¹ • (x (k + 1) - y k) + v k = eta k
  inclusion :
    ∀ k : ℕ,
      v k ∈ (rho k) •
        A ((rho k)⁻¹ • x (k + 1) + (1 - (rho k)⁻¹) • y k)

/-- Theorem 3.1: weak convergence of the relaxed inertial proximal point
method under summable inexactness. -/
theorem theorem_3_1
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (x y v eta : ℕ → H) (lam alpha rho : ℕ → ℝ)
    (rec : InexactProximalRecurrence A x y v eta lam alpha rho)
    (params : ParameterAssumptions x)
    (hlam_eq : lam = params.lam)
    (halpha_eq : alpha = params.alpha)
    (hrho_eq : rho = params.rho)
    (hS : (SetValuedOperator.zeros A).Nonempty)
    (h31 : Summable fun k : ℕ ↦ lam k * ‖eta k‖)
    (h33 : Summable fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k‖) :
    Tendsto (fun k : ℕ ↦ v k) atTop (𝓝 (0 : H)) ∧
      ∃ xstar ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (x k)) atTop
          (𝓝 (toWeakSpace ℝ H xstar)) := by
  classical
  have hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k := by
    rcases params.lam_lower with ⟨lam0, hpos, hlow⟩
    refine ⟨lam0, hpos, ?_⟩
    intro k
    simpa [hlam_eq] using hlow k
  have hlam_pos (k : ℕ) : 0 < lam k := by
    rcases hlam_lower with ⟨lam0, hpos, hlow⟩
    exact lt_of_lt_of_le hpos (hlow k)
  have hlam_ne_zero (k : ℕ) : lam k ≠ 0 := (hlam_pos k).ne'
  have halpha_mem (k : ℕ) : 0 ≤ alpha k ∧ alpha k < 1 := by
    simpa [halpha_eq] using params.alpha_mem k
  have halpha_upper : ∃ alpha0 : ℝ, alpha0 < 1 ∧ ∀ k : ℕ, alpha k ≤ alpha0 := by
    rcases params.alpha_upper with ⟨alpha0, hlt, hub⟩
    refine ⟨alpha0, hlt, ?_⟩
    intro k
    simpa [halpha_eq] using hub k
  obtain ⟨alpha0, halpha0_lt, halpha_le⟩ := halpha_upper
  have halpha_bound : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0 := by
    intro k
    exact ⟨(halpha_mem k).1, halpha_le k⟩
  have halpha_summable :
      Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2 := by
    simpa [halpha_eq] using params.alpha_summable
  have hdelta_inertial_summable :
      Summable fun k : ℕ ↦
        ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 :=
    inertial_delta_summable_thm2 x alpha halpha_summable halpha_mem
  have hrho_lower : ∃ R1 : ℝ, 0 < R1 ∧ ∀ k : ℕ, R1 ≤ rho k := by
    rcases params.rho_lower with ⟨R1, hpos, hlow⟩
    refine ⟨R1, hpos, ?_⟩
    intro k
    simpa [hrho_eq] using hlow k
  have hrho_upper : ∃ R2 : ℝ, R2 < 2 ∧ ∀ k : ℕ, rho k ≤ R2 := by
    rcases params.rho_upper with ⟨R2, hlt, hub⟩
    refine ⟨R2, hlt, ?_⟩
    intro k
    simpa [hrho_eq] using hub k
  obtain ⟨R1, hR1_pos, hR1_le⟩ := hrho_lower
  obtain ⟨R2, hR2_lt, hR2_le⟩ := hrho_upper
  have hrho_pos (k : ℕ) : 0 < rho k := lt_of_lt_of_le hR1_pos (hR1_le k)
  have hrho_ne_zero (k : ℕ) : rho k ≠ 0 := (hrho_pos k).ne'
  have hR2_pos : 0 < R2 := lt_of_lt_of_le (hrho_pos 0) (hR2_le 0)
  have hR2_ne_zero : R2 ≠ 0 := hR2_pos.ne'
  let J_seq (k : ℕ) (z : H) : H :=
    Classical.choose (resolvent_nonempty hA (hlam_pos k) z)
  have hJ_seq (k : ℕ) (z : H) :
      J_seq k z ∈ J[(lam k • A)] z :=
    Classical.choose_spec (resolvent_nonempty hA (hlam_pos k) z)
  let A_lam_sv (k : ℕ) (z : H) : H := (lam k)⁻¹ • (z - J_seq k z)
  let w (k : ℕ) : H := (1 - rho k) • y k + rho k • J_seq k (y k)
  let xi (k : ℕ) : H := y k - J_seq k (y k)
  have h_eta_tendsto_zero : Tendsto (fun k : ℕ ↦ ‖eta k‖) atTop (𝓝 0) :=
    eta_norm_tendsto_zero (eta := eta) (lam := lam) hlam_lower h31
  have h_rho_factor_pos : 0 < R1 * (1 - R2 / 2) := by
    have hhalf : R2 / 2 < 1 := by linarith
    have hpos : 0 < 1 - R2 / 2 := by linarith
    exact mul_pos hR1_pos hpos
  have h_rho_factor_nonneg (k : ℕ) : 0 ≤ rho k * (1 - rho k / 2) := by
    have hhalf : rho k / 2 ≤ 1 := by linarith [hR2_le k, hR2_lt]
    have hnonneg : 0 ≤ 1 - rho k / 2 := by linarith
    exact mul_nonneg (le_of_lt (hrho_pos k)) hnonneg
  have h_rho_lower_bound (k : ℕ) :
      R1 * (1 - R2 / 2) ≤ rho k * (1 - rho k / 2) := by
    have hleft : 0 ≤ 1 - R2 / 2 := by linarith [hR2_lt]
    have hright : 0 ≤ rho k := le_of_lt (hrho_pos k)
    have hfactor : 1 - R2 / 2 ≤ 1 - rho k / 2 := by linarith [hR2_le k]
    have hmul₁ : R1 * (1 - R2 / 2) ≤ rho k * (1 - R2 / 2) :=
      mul_le_mul_of_nonneg_right (hR1_le k) hleft
    have hmul₂ : rho k * (1 - R2 / 2) ≤ rho k * (1 - rho k / 2) :=
      mul_le_mul_of_nonneg_left hfactor hright
    exact le_trans hmul₁ hmul₂
  rcases hS with ⟨xbar, hxbar⟩
  have h_y_error_summable :
      Summable fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k - xbar‖ := by
    have hconst : Summable fun k : ℕ ↦ ‖xbar‖ * (lam k * ‖eta k‖) :=
      h31.mul_left ‖xbar‖
    have hsum :
        Summable fun k : ℕ ↦
          lam k * ‖eta k‖ * ‖y k‖ + ‖xbar‖ * (lam k * ‖eta k‖) :=
      h33.add hconst
    refine hsum.of_nonneg_of_le ?hnonneg ?hle
    · intro k
      exact mul_nonneg (mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)) (norm_nonneg _)
    · intro k
      have hfac : 0 ≤ lam k * ‖eta k‖ :=
        mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
      have htri : ‖y k - xbar‖ ≤ ‖y k‖ + ‖xbar‖ := by
        simpa using norm_sub_le (y k) xbar
      calc
        lam k * ‖eta k‖ * ‖y k - xbar‖
            ≤ lam k * ‖eta k‖ * (‖y k‖ + ‖xbar‖) :=
              mul_le_mul_of_nonneg_left htri hfac
        _ = lam k * ‖eta k‖ * ‖y k‖ + ‖xbar‖ * (lam k * ‖eta k‖) := by
              ring
  have hJ_xbar_fixed (k : ℕ) : J_seq k xbar = xbar := by
    have hxbar_res : xbar ∈ J[(lam k • A)] xbar :=
      (Alvarez2004.resolvent_fixed_iff_zero A hA (hlam_pos k) xbar).mpr hxbar
    have hsingle := resolvent_is_at_most_single_valued A hA (hlam_pos k)
    exact hsingle xbar (hJ_seq k xbar) hxbar_res
  have hA_lam_xbar_zero (k : ℕ) : A_lam_sv k xbar = 0 := by
    dsimp [A_lam_sv]
    simp [hJ_xbar_fixed k]
  have hxi_graph (k : ℕ) : (lam k)⁻¹ • xi k ∈ A (y k - xi k) := by
    dsimp [xi]
    exact yosida_resolvent_equiv A (hlam_ne_zero k) (hJ_seq k (y k)) rfl
  have h_alpha_diff_norm_tendsto_zero :
      Tendsto (fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖) atTop (𝓝 0) :=
    alpha_diff_norm_tendsto_zero_thm2 x alpha halpha_summable halpha_mem
  have h_lam_sq_eta_sq_summable :
      Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖eta k‖ ^ 2 :=
    lam_sq_eta_sq_summable_thm2 hlam_pos h31
  have h_eta_tendsto_zero_vec : Tendsto (fun k : ℕ ↦ eta k) atTop (𝓝 (0 : H)) := by
    simpa [Metric.tendsto_atTop] using h_eta_tendsto_zero
  have h_xi_eq_lam_A_lam (k : ℕ) : xi k = lam k • A_lam_sv k (y k) := by
    dsimp [xi, A_lam_sv]
    simp [smul_smul, hlam_ne_zero k]
  have h_A_lam_eq_inv_smul_xi (k : ℕ) : A_lam_sv k (y k) = (lam k)⁻¹ • xi k := by
    dsimp [xi, A_lam_sv]
  have h_w_eq_y_sub_rho_xi (k : ℕ) : w k = y k - rho k • xi k := by
    dsimp [w, xi]
    module
  have hJ_firm (k : ℕ) : FirmlyNonexpansive (J_seq k) :=
    firmly_nonexpansive_resolvent_selection_thm2 hA.1 (lam k) (hlam_pos k)
      (J_seq k) (hJ_seq k)
  have hJ_cocoercive (k : ℕ) :
      CocoerciveOn (1 : ℝ) Set.univ (fun z : Set.univ ↦ J_seq k z) :=
    firmly_nonexpansive_cocoerciveOn_one_thm2 (hJ_firm k)
  have h_residual_firm (k : ℕ) :
      FirmlyNonexpansiveOn Set.univ
        (residualMap Set.univ (fun z : Set.univ ↦ J_seq k z)) := by
    rw [firmlyNonexpansiveOn_residualMap_iff]
    simpa [FirmlyNonexpansive] using hJ_firm k
  have h_residual_cocoercive (k : ℕ) :
      CocoerciveOn (1 : ℝ) Set.univ
        (residualMap Set.univ (fun z : Set.univ ↦ J_seq k z)) := by
    exact firmly_nonexpansiveOn_cocoerciveOn_one_thm2 (h_residual_firm k)
  have h_cocoercive (k : ℕ) (z₁ z₂ : H) :
      lam k * ‖A_lam_sv k z₁ - A_lam_sv k z₂‖ ^ 2 ≤
        inner ℝ (A_lam_sv k z₁ - A_lam_sv k z₂) (z₁ - z₂) := by
    simpa [A_lam_sv] using
      scaled_residual_cocoercive_thm2 (lam k) (hlam_pos k) (J_seq k)
        (h_residual_cocoercive k) z₁ z₂
  have h_inertial_expansion (k : ℕ) (xbar' : H) :
      (1 / 2 : ℝ) * ‖y k - xbar'‖ ^ 2 =
        (1 / 2) * ‖x k - xbar'‖ ^ 2 +
          alpha k * ((1 / 2) * ‖x k - xbar'‖ ^ 2 -
            (1 / 2) * ‖x (k - 1) - xbar'‖ ^ 2) +
          ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 :=
    inertial_expansion_y_thm2 x y alpha rec.y_def k xbar'
  let φ (xbar' : H) (k : ℕ) : ℝ := (1 / 2 : ℝ) * ‖x k - xbar'‖ ^ 2
  let δ (xbar' : H) (k : ℕ) : ℝ :=
    ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 +
      lam k * ‖eta k‖ * ‖y k - xbar'‖ +
      ((lam k) ^ 2 / 2) * ‖eta k‖ ^ 2
  have h35 : ∀ k : ℕ, ‖x (k + 1) - w k‖ ≤ lam k * ‖eta k‖ := by
    intro k
    have h_resolvent_rewrite :
        J_seq k (y k + ((lam k) / (rho k)) • eta k) =
          (rho k)⁻¹ • x (k + 1) + (1 - (rho k)⁻¹) • y k := by
      let z : H := (rho k)⁻¹ • x (k + 1) + (1 - (rho k)⁻¹) • y k
      have hv_mem := rec.inclusion k
      rw [Set.mem_smul_set] at hv_mem
      rcases hv_mem with ⟨a, ha, hv_eq⟩
      have heq := rec.equation k
      have h_eta :
          eta k = (lam k)⁻¹ • (x (k + 1) - y k) + rho k • a := by
        rw [← heq, hv_eq]
      have hdiff :
          y k + ((lam k) / (rho k)) • eta k - z = lam k • a := by
        dsimp [z]
        rw [h_eta]
        have hrho_nz : rho k ≠ 0 := hrho_ne_zero k
        have hlam_nz : lam k ≠ 0 := hlam_ne_zero k
        have hcoeff1 : (lam k / rho k) * (lam k)⁻¹ = (rho k)⁻¹ := by
          field_simp [hrho_nz, hlam_nz]
        have hcoeff2 : (lam k / rho k) * rho k = lam k := by
          field_simp [hrho_nz]
        rw [smul_add, smul_smul, smul_smul, hcoeff1, hcoeff2]
        module
      have hz_mem :
          z ∈ J[(lam k • A)] (y k + ((lam k) / (rho k)) • eta k) := by
        rw [SetValuedOperator.mem_resolvent_smul_iff]
        dsimp [SetValuedOperator.identityAddScaled]
        refine ⟨a, ha, ?_⟩
        dsimp [z] at hdiff ⊢
        exact (eq_add_of_sub_eq' hdiff).symm
      exact resolvent_is_at_most_single_valued A hA (hlam_pos k)
        (y k + ((lam k) / (rho k)) • eta k)
        (hJ_seq k (y k + ((lam k) / (rho k)) • eta k)) hz_mem
    have hx_next_eq :
        x (k + 1) =
          (1 - rho k) • y k +
            rho k • J_seq k (y k + ((lam k) / (rho k)) • eta k) := by
      rw [h_resolvent_rewrite]
      have hrho_nz : rho k ≠ 0 := hrho_ne_zero k
      have hcoeff1 : rho k * (rho k)⁻¹ = 1 := by field_simp [hrho_nz]
      have hcoeff2 : rho k * (1 - (rho k)⁻¹) = rho k - 1 := by field_simp [hrho_nz]
      rw [smul_add, smul_smul, smul_smul, hcoeff1, hcoeff2, one_smul]
      module
    calc
      ‖x (k + 1) - w k‖
          = ‖((1 - rho k) • y k +
                rho k • J_seq k (y k + ((lam k) / (rho k)) • eta k)) -
              ((1 - rho k) • y k + rho k • J_seq k (y k))‖ := by
            rw [hx_next_eq]
      _ = ‖rho k •
              (J_seq k (y k + ((lam k) / (rho k)) • eta k) - J_seq k (y k))‖ := by
            congr 1
            rw [smul_sub]
            abel
      _ = rho k *
            ‖J_seq k (y k + ((lam k) / (rho k)) • eta k) - J_seq k (y k)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hrho_pos k)]
      _ ≤ rho k * ‖((lam k) / (rho k)) • eta k‖ := by
            have hlip :=
              resolvent_selection_lipschitz A hA (hlam_pos k) (J_seq k) (hJ_seq k)
            have hdist := hlip.dist_le_mul
              (y k + ((lam k) / (rho k)) • eta k) (y k)
            simp [dist_eq_norm] at hdist
            exact mul_le_mul_of_nonneg_left hdist (le_of_lt (hrho_pos k))
      _ = rho k * ((lam k) / (rho k) * ‖eta k‖) := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (div_nonneg (le_of_lt (hlam_pos k)) (le_of_lt (hrho_pos k)))]
      _ = lam k * ‖eta k‖ := by
            field_simp [hrho_ne_zero k]
  have h_norm_sub_smul_sq (a b : H) (c : ℝ) :
      ‖a - c • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * c * inner ℝ a b + c ^ 2 * ‖b‖ ^ 2 := by
    calc
      ‖a - c • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner ℝ a (c • b) + ‖c • b‖ ^ 2 := by
        rw [norm_sub_sq_real]
      _ = ‖a‖ ^ 2 - 2 * c * inner ℝ a b + c ^ 2 * ‖b‖ ^ 2 := by
        rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
        nlinarith [sq_abs c]
  have h38 : ∀ k : ℕ, ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      (1 / 2 : ℝ) * ‖w k - xbar'‖ ^ 2 ≤
        (1 / 2) * ‖y k - xbar'‖ ^ 2 -
          (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
    intro k xbar' hxbar'
    have hA_lam_xbar'_zero : A_lam_sv k xbar' = 0 := by
      exact (yosida_selection_eq_zero_iff_thm2 A hA (hlam_pos k) (J_seq k) (hJ_seq k) xbar').mp hxbar'
    have h_w_expand :
        w k - xbar' =
          (y k - xbar') - (lam k * rho k) • A_lam_sv k (y k) := by
      calc
        w k - xbar' = (y k - rho k • xi k) - xbar' := by rw [h_w_eq_y_sub_rho_xi k]
        _ = (y k - xbar') - rho k • xi k := by module
        _ = (y k - xbar') - rho k • (lam k • A_lam_sv k (y k)) := by
              rw [h_xi_eq_lam_A_lam k]
        _ = (y k - xbar') - (lam k * rho k) • A_lam_sv k (y k) := by
              rw [smul_smul]
              ring_nf
    rw [h_w_expand]
    rw [h_norm_sub_smul_sq (y k - xbar') (A_lam_sv k (y k)) (lam k * rho k)]
    have h_coco :
        lam k * ‖A_lam_sv k (y k)‖ ^ 2 ≤
          inner ℝ (A_lam_sv k (y k)) (y k - xbar') := by
      have h := h_cocoercive k (y k) xbar'
      simpa [hA_lam_xbar'_zero] using h
    have hinner_comm :
        inner ℝ (y k - xbar') (A_lam_sv k (y k)) =
          inner ℝ (A_lam_sv k (y k)) (y k - xbar') := by
      rw [real_inner_comm]
    have hcoef_nonneg : 0 ≤ lam k * rho k :=
      mul_nonneg (le_of_lt (hlam_pos k)) (le_of_lt (hrho_pos k))
    have hmain :
        (1 / 2 : ℝ) *
            (‖y k - xbar'‖ ^ 2 -
              2 * (lam k * rho k) * inner ℝ (y k - xbar') (A_lam_sv k (y k)) +
              (lam k * rho k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) ≤
          (1 / 2 : ℝ) * ‖y k - xbar'‖ ^ 2 -
            (lam k) ^ 2 * rho k * (1 - rho k / 2) *
      ‖A_lam_sv k (y k)‖ ^ 2 := by
      rw [hinner_comm]
      nlinarith [mul_le_mul_of_nonneg_left h_coco hcoef_nonneg]
    exact hmain
  have h_sq_triangle (a b : H) :
      (1 / 2 : ℝ) * ‖a + b‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖a‖ ^ 2 + ‖a‖ * ‖b‖ + (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
    calc
      (1 / 2 : ℝ) * ‖a + b‖ ^ 2 =
          (1 / 2 : ℝ) * (‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2) := by
            rw [norm_add_sq_real]
      _ = (1 / 2 : ℝ) * ‖a‖ ^ 2 + inner ℝ a b + (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
            ring
      _ ≤ (1 / 2 : ℝ) * ‖a‖ ^ 2 + ‖a‖ * ‖b‖ + (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
            nlinarith [real_inner_le_norm a b]
  have h39 : ∀ k : ℕ, ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      (1 / 2 : ℝ) * ‖x (k + 1) - xbar'‖ ^ 2 ≤
        (1 / 2) * ‖y k - xbar'‖ ^ 2 -
          (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 +
          lam k * ‖eta k‖ * ‖y k - xbar'‖ +
          ((lam k) ^ 2 / 2) * ‖eta k‖ ^ 2 := by
    intro k xbar' hxbar'
    have h_w_sq_bound :
        (1 / 2 : ℝ) * ‖w k - xbar'‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖y k - xbar'‖ ^ 2 := by
      have hfull := h38 k xbar' hxbar'
      have hnonneg :
          0 ≤ (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
        have hleft : 0 ≤ (lam k) ^ 2 * (rho k * (1 - rho k / 2)) :=
          mul_nonneg (sq_nonneg _) (h_rho_factor_nonneg k)
        convert mul_nonneg hleft (sq_nonneg ‖A_lam_sv k (y k)‖) using 1
        ring
      nlinarith
    have h_w_norm_bound : ‖w k - xbar'‖ ≤ ‖y k - xbar'‖ := by
      have h_sq : ‖w k - xbar'‖ ^ 2 ≤ ‖y k - xbar'‖ ^ 2 := by nlinarith
      simpa [abs_of_nonneg (norm_nonneg _)] using sq_le_sq.mp h_sq
    have h_decomp :
        x (k + 1) - xbar' = (w k - xbar') + (x (k + 1) - w k) := by
      module
    rw [h_decomp]
    have htri := h_sq_triangle (w k - xbar') (x (k + 1) - w k)
    have h35k := h35 k
    have h38k := h38 k xbar' hxbar'
    have h_eta_sq :
        ‖x (k + 1) - w k‖ ^ 2 ≤ (lam k * ‖eta k‖) ^ 2 := by
      have hrhs_nonneg : 0 ≤ lam k * ‖eta k‖ :=
        mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
      nlinarith [h35k, norm_nonneg (x (k + 1) - w k)]
    have h_cross :
        ‖w k - xbar'‖ * ‖x (k + 1) - w k‖ ≤
          ‖y k - xbar'‖ * (lam k * ‖eta k‖) := by
      exact mul_le_mul h_w_norm_bound h35k (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have h310 : ∀ k : ℕ, ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      φ xbar' (k + 1) ≤
        φ xbar' k + alpha k * (φ xbar' k - φ xbar' (k - 1)) +
          δ xbar' k -
          (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
    intro k xbar' hxbar'
    have hdescent := h39 k xbar' hxbar'
    have hinertial := h_inertial_expansion k xbar'
    dsimp [φ, δ] at *
    nlinarith
  have hdelta_summable : ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      Summable (δ xbar') := by
    intro xbar' hxbar'
    have hyerr : Summable fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k - xbar'‖ := by
      have hconst : Summable fun k : ℕ ↦ ‖xbar'‖ * (lam k * ‖eta k‖) :=
        h31.mul_left ‖xbar'‖
      have hsum :
          Summable fun k : ℕ ↦
            lam k * ‖eta k‖ * ‖y k‖ + ‖xbar'‖ * (lam k * ‖eta k‖) :=
        h33.add hconst
      refine hsum.of_nonneg_of_le ?hyerr_nonneg ?hyerr_le
      · intro k
        exact mul_nonneg
          (mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg (eta k)))
          (norm_nonneg (y k - xbar'))
      · intro k
        have hfac : 0 ≤ lam k * ‖eta k‖ :=
          mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg (eta k))
        have htri : ‖y k - xbar'‖ ≤ ‖y k‖ + ‖xbar'‖ := by
          simpa using norm_sub_le (y k) xbar'
        calc
          lam k * ‖eta k‖ * ‖y k - xbar'‖
              ≤ lam k * ‖eta k‖ * (‖y k‖ + ‖xbar'‖) :=
                mul_le_mul_of_nonneg_left htri hfac
          _ = lam k * ‖eta k‖ * ‖y k‖ + ‖xbar'‖ * (lam k * ‖eta k‖) := by
                ring
    have hlam_sq_half :
        Summable fun k : ℕ ↦ ((lam k) ^ 2 / 2) * ‖eta k‖ ^ 2 := by
      convert h_lam_sq_eta_sq_summable.mul_left (1 / 2 : ℝ) using 1
      ext k
      ring
    exact (hdelta_inertial_summable.add hyerr).add hlam_sq_half
  have h_lemma23_concl : ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      Summable (fun k : ℕ ↦ posPart (φ xbar' k - φ xbar' (k - 1))) ∧
        ∃ φstar : ℝ, 0 ≤ φstar ∧ Tendsto (φ xbar') atTop (𝓝 φstar) := by
    intro xbar' hxbar'
    have hphi_nonneg : ∀ k : ℕ, 0 ≤ φ xbar' k := by
      intro k
      dsimp [φ]
      positivity
    have hdelta_nonneg : ∀ k : ℕ, 0 ≤ δ xbar' k := by
      intro k
      dsimp [δ]
      have ha0 : 0 ≤ alpha k := (halpha_mem k).1
      have hlam0 : 0 ≤ lam k := le_of_lt (hlam_pos k)
      positivity
    have hrec : ∀ k : ℕ,
        φ xbar' (k + 1) ≤
          φ xbar' k + alpha k * (φ xbar' k - φ xbar' (k - 1)) + δ xbar' k := by
      intro k
      have hfull := h310 k xbar' hxbar'
      have hnonneg :
          0 ≤ (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
        have hleft : 0 ≤ (lam k) ^ 2 * (rho k * (1 - rho k / 2)) :=
          mul_nonneg (sq_nonneg (lam k)) (h_rho_factor_nonneg k)
        convert mul_nonneg hleft (sq_nonneg ‖A_lam_sv k (y k)‖) using 1
        ring
      nlinarith
    exact lemma_2_3 (φ xbar') (δ xbar') alpha alpha0 hphi_nonneg hdelta_nonneg
      hrec (hdelta_summable xbar' hxbar') halpha_bound halpha0_lt
  have h_dist_all : ∀ xbar' ∈ SetValuedOperator.zeros A,
      ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar'‖) atTop (𝓝 l) := by
    intro xbar' hxbar'
    rcases (h_lemma23_concl xbar' hxbar').2 with ⟨φstar, hφstar_nonneg, hφ_tendsto⟩
    have h_norm_sq_tendsto :
        Tendsto (fun k : ℕ => ‖x k - xbar'‖ ^ 2) atTop (𝓝 (2 * φstar)) := by
      have h_eq :
          (fun k : ℕ => ‖x k - xbar'‖ ^ 2) = (fun k : ℕ => 2 * φ xbar' k) := by
        funext k
        dsimp [φ]
        ring
      rw [h_eq]
      simpa using hφ_tendsto.const_mul 2
    have h_norm_tendsto :
        Tendsto (fun k : ℕ => ‖x k - xbar'‖) atTop
          (𝓝 (Real.sqrt (2 * φstar))) := by
      have h_sqrt_tendsto :
          Tendsto (fun k : ℕ => Real.sqrt (‖x k - xbar'‖ ^ 2)) atTop
            (𝓝 (Real.sqrt (2 * φstar))) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp h_norm_sq_tendsto
      have h_eq :
          (fun k : ℕ => Real.sqrt (‖x k - xbar'‖ ^ 2)) =
            (fun k : ℕ => ‖x k - xbar'‖) := by
        funext k
        simp
      simpa [h_eq] using h_sqrt_tendsto
    exact ⟨Real.sqrt (2 * φstar), h_norm_tendsto⟩
  have h_yosida_sq_summable :
      Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2 := by
    set gamma_seq : ℕ → ℝ := fun k : ℕ =>
      (lam k) ^ 2 * rho k * (1 - rho k / 2) * ‖A_lam_sv k (y k)‖ ^ 2
      with hgamma_seq_def
    have hgamma_nonneg : ∀ k : ℕ, 0 ≤ gamma_seq k := by
      intro k
      rw [hgamma_seq_def]
      have hleft : 0 ≤ (lam k) ^ 2 * (rho k * (1 - rho k / 2)) :=
        mul_nonneg (sq_nonneg _) (h_rho_factor_nonneg k)
      convert mul_nonneg hleft (sq_nonneg ‖A_lam_sv k (y k)‖) using 1
      ring
    have hsummable_gamma : Summable gamma_seq := by
      have hrecurrence_rearranged (k : ℕ) :
          gamma_seq k ≤
            φ xbar k - φ xbar (k + 1) +
              alpha k * (φ xbar k - φ xbar (k - 1)) + δ xbar k := by
        have hfull := h310 k xbar hxbar
        rw [hgamma_seq_def]
        nlinarith
      have halpha_theta_bound (k : ℕ) :
          alpha k * (φ xbar k - φ xbar (k - 1)) ≤
            alpha0 * posPart (φ xbar k - φ xbar (k - 1)) := by
        set theta := φ xbar k - φ xbar (k - 1)
        by_cases htheta_nonneg : 0 ≤ theta
        · have hpospart_eq : posPart theta = theta := by
            dsimp [posPart]
            rw [max_eq_left htheta_nonneg]
          have h_alpha_le : alpha k ≤ alpha0 := (halpha_bound k).2
          nlinarith [(halpha_bound k).1]
        · have htheta_nonpos : theta ≤ 0 := le_of_not_ge htheta_nonneg
          have hnonpos : alpha k * theta ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (halpha_bound k).1 htheta_nonpos
          have hpospart_zero : posPart theta = 0 := by
            dsimp [posPart]
            rw [max_eq_right htheta_nonpos]
          have halpha0_nonneg : 0 ≤ alpha0 :=
            le_trans (halpha_bound 0).1 (halpha_bound 0).2
          nlinarith
      have hgamma_bound_partial (n : ℕ) :
          (Finset.range (n + 1)).sum gamma_seq ≤
            (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
            alpha0 * (Finset.range (n + 1)).sum
              (fun k => posPart (φ xbar k - φ xbar (k - 1))) +
            (Finset.range (n + 1)).sum (δ xbar) := by
        calc
          (Finset.range (n + 1)).sum gamma_seq ≤
              (Finset.range (n + 1)).sum
                (fun k => φ xbar k - φ xbar (k + 1) +
                  alpha k * (φ xbar k - φ xbar (k - 1)) + δ xbar k) := by
            exact Finset.sum_le_sum (fun i _hi => hrecurrence_rearranged i)
          _ = (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
              (Finset.range (n + 1)).sum
                (fun k => alpha k * (φ xbar k - φ xbar (k - 1))) +
              (Finset.range (n + 1)).sum (δ xbar) := by
            simp [Finset.sum_add_distrib]
          _ ≤ (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
              (Finset.range (n + 1)).sum
                (fun k => alpha0 * posPart (φ xbar k - φ xbar (k - 1))) +
              (Finset.range (n + 1)).sum (δ xbar) := by
            have hsum_le :
                (Finset.range (n + 1)).sum
                    (fun k => alpha k * (φ xbar k - φ xbar (k - 1))) ≤
                  (Finset.range (n + 1)).sum
                    (fun k => alpha0 * posPart (φ xbar k - φ xbar (k - 1))) :=
              Finset.sum_le_sum (fun i _hi => halpha_theta_bound i)
            nlinarith
          _ = (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
              alpha0 * (Finset.range (n + 1)).sum
                (fun k => posPart (φ xbar k - φ xbar (k - 1))) +
              (Finset.range (n + 1)).sum (δ xbar) := by
            simp [Finset.mul_sum]
      have htelescope (n : ℕ) :
          (Finset.range (n + 1)).sum (fun k : ℕ => φ xbar k - φ xbar (k + 1)) =
            φ xbar 0 - φ xbar (n + 1) := by
        induction' n with m ih
        · simp
        · rw [Finset.sum_range_succ, ih]
          ring
      have hphi_nonneg : ∀ k : ℕ, 0 ≤ φ xbar k := by
        intro k
        dsimp [φ]
        positivity
      have hdelta_nonneg : ∀ k : ℕ, 0 ≤ δ xbar k := by
        intro k
        dsimp [δ]
        have ha0 : 0 ≤ alpha k := (halpha_mem k).1
        have hlam0 : 0 ≤ lam k := le_of_lt (hlam_pos k)
        positivity
      have hgamma_bound_total (n : ℕ) :
          (Finset.range (n + 1)).sum gamma_seq ≤
            φ xbar 0 + alpha0 * ∑' k, posPart (φ xbar k - φ xbar (k - 1)) +
              ∑' k, δ xbar k := by
        have hpartial := hgamma_bound_partial n
        rw [htelescope n] at hpartial
        have hpospart_le :
            (Finset.range (n + 1)).sum
                (fun k => posPart (φ xbar k - φ xbar (k - 1))) ≤
              ∑' k, posPart (φ xbar k - φ xbar (k - 1)) :=
          (h_lemma23_concl xbar hxbar).1.sum_le_tsum (Finset.range (n + 1))
            (fun i _hi => by dsimp [posPart]; exact le_max_right _ _)
        have hdelta_le :
            (Finset.range (n + 1)).sum (δ xbar) ≤ ∑' k, δ xbar k :=
          (hdelta_summable xbar hxbar).sum_le_tsum (Finset.range (n + 1))
            (fun i _hi => hdelta_nonneg i)
        have halpha0_nonneg : 0 ≤ alpha0 :=
          le_trans (halpha_bound 0).1 (halpha_bound 0).2
        nlinarith [hphi_nonneg (n + 1)]
      have hbound_for_sum_range_le (n : ℕ) :
          (Finset.range n).sum gamma_seq ≤
            φ xbar 0 + alpha0 * ∑' k, posPart (φ xbar k - φ xbar (k - 1)) +
              ∑' k, δ xbar k := by
        cases n with
        | zero =>
            have hC_nonneg :
                0 ≤ φ xbar 0 + alpha0 * ∑' k, posPart (φ xbar k - φ xbar (k - 1)) +
                  ∑' k, δ xbar k := by
              have halpha0_nonneg : 0 ≤ alpha0 :=
                le_trans (halpha_bound 0).1 (halpha_bound 0).2
              have hpos_tsum :
                  0 ≤ ∑' k, posPart (φ xbar k - φ xbar (k - 1)) :=
                tsum_nonneg (fun k => by dsimp [posPart]; exact le_max_right _ _)
              have hdelta_tsum : 0 ≤ ∑' k, δ xbar k :=
                tsum_nonneg hdelta_nonneg
              nlinarith [hphi_nonneg 0]
            simpa using hC_nonneg
        | succ m => simpa using hgamma_bound_total m
      exact summable_of_sum_range_le hgamma_nonneg hbound_for_sum_range_le
    have hcoeff_pos : 0 < R1 * (1 - R2 / 2) := h_rho_factor_pos
    let term : ℕ → ℝ := fun k => (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2
    have hterm_nonneg_all : ∀ k : ℕ, 0 ≤ term k := by
      intro k
      dsimp [term]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hterm_le : ∀ k : ℕ, term k ≤ gamma_seq k / (R1 * (1 - R2 / 2)) := by
      intro k
      dsimp [term]
      have hterm_nonneg :
          0 ≤ (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hmul :
          (R1 * (1 - R2 / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) ≤
            (rho k * (1 - rho k / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (h_rho_lower_bound k) hterm_nonneg
      have hgamma_lower :
          (R1 * (1 - R2 / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) ≤ gamma_seq k := by
        calc
          (R1 * (1 - R2 / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2)
              ≤ (rho k * (1 - rho k / 2)) *
                  ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) := hmul
          _ = gamma_seq k := by
                rw [hgamma_seq_def]
                ring
      exact (le_div_iff₀ hcoeff_pos).mpr
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hgamma_lower)
    have hterm_summable : Summable term :=
      Summable.of_nonneg_of_le hterm_nonneg_all hterm_le
        (hsummable_gamma.div_const (R1 * (1 - R2 / 2)))
    simpa [term] using hterm_summable
  have h_xi_tendsto : Tendsto (fun k : ℕ ↦ xi k) atTop (𝓝 (0 : H)) := by
    have hxi_sq_summable : Summable fun k : ℕ ↦ ‖xi k‖ ^ 2 := by
      have h_eq :
          (fun k : ℕ ↦ ‖xi k‖ ^ 2) =
            fun k : ℕ ↦ (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2 := by
        funext k
        rw [h_xi_eq_lam_A_lam k, norm_smul, Real.norm_eq_abs,
          abs_of_pos (hlam_pos k)]
        ring
      simpa [h_eq] using h_yosida_sq_summable
    have hsq_tendsto :
        Tendsto (fun k : ℕ ↦ ‖xi k‖ ^ 2) atTop (𝓝 0) :=
      hxi_sq_summable.tendsto_atTop_zero
    have hsqrt :
        Tendsto (fun k : ℕ ↦ Real.sqrt (‖xi k‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tendsto
    have hnorm_tendsto : Tendsto (fun k : ℕ ↦ ‖xi k‖) atTop (𝓝 0) := by
      have h_eq :
          (fun k : ℕ ↦ Real.sqrt (‖xi k‖ ^ 2)) = fun k : ℕ ↦ ‖xi k‖ := by
        funext k
        simp
      simpa [h_eq] using hsqrt
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
  have hv_tendsto : Tendsto (fun k : ℕ ↦ v k) atTop (𝓝 (0 : H)) := by
    rcases hlam_lower with ⟨lam0, hlam0_pos, hlam0_le⟩
    have hstep_scaled_tendsto :
        Tendsto (fun k : ℕ ↦ (lam k)⁻¹ • (x (k + 1) - y k)) atTop
          (𝓝 (0 : H)) := by
      have hnorm_bound (k : ℕ) :
          ‖(lam k)⁻¹ • (x (k + 1) - y k)‖ ≤
            ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖ := by
        have hwy_bound : ‖w k - y k‖ ≤ R2 * ‖xi k‖ := by
          have hwy_eq : ‖w k - y k‖ = rho k * ‖xi k‖ := by
            rw [h_w_eq_y_sub_rho_xi k]
            have hvec : y k - rho k • xi k - y k = -rho k • xi k := by
              module
            rw [hvec, norm_smul, Real.norm_eq_abs]
            simp [abs_of_pos (hrho_pos k)]
          rw [hwy_eq]
          exact mul_le_mul_of_nonneg_right (hR2_le k) (norm_nonneg _)
        have hstep_bound :
            ‖x (k + 1) - y k‖ ≤ lam k * ‖eta k‖ + R2 * ‖xi k‖ := by
          have hdecomp :
              x (k + 1) - y k = (x (k + 1) - w k) + (w k - y k) := by
            module
          calc
            ‖x (k + 1) - y k‖
                = ‖(x (k + 1) - w k) + (w k - y k)‖ := by rw [hdecomp]
            _ ≤ ‖x (k + 1) - w k‖ + ‖w k - y k‖ := norm_add_le _ _
            _ ≤ lam k * ‖eta k‖ + R2 * ‖xi k‖ := add_le_add (h35 k) hwy_bound
        have hinv_nonneg : 0 ≤ (lam k)⁻¹ := le_of_lt (inv_pos.mpr (hlam_pos k))
        have hinv_le : (lam k)⁻¹ ≤ lam0⁻¹ :=
          (inv_le_inv₀ (hlam_pos k) hlam0_pos).mpr (hlam0_le k)
        calc
          ‖(lam k)⁻¹ • (x (k + 1) - y k)‖
              = (lam k)⁻¹ * ‖x (k + 1) - y k‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam_pos k))]
          _ ≤ (lam k)⁻¹ * (lam k * ‖eta k‖ + R2 * ‖xi k‖) :=
                mul_le_mul_of_nonneg_left hstep_bound hinv_nonneg
          _ = ‖eta k‖ + ((lam k)⁻¹ * R2) * ‖xi k‖ := by
                field_simp [hlam_ne_zero k]
          _ ≤ ‖eta k‖ + (lam0⁻¹ * R2) * ‖xi k‖ := by
                have hcoef : (lam k)⁻¹ * R2 ≤ lam0⁻¹ * R2 :=
                  mul_le_mul_of_nonneg_right hinv_le (le_of_lt hR2_pos)
                have hmul :=
                  mul_le_mul_of_nonneg_right hcoef (norm_nonneg (xi k))
                nlinarith
          _ = ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖ := by ring
      have hnorm_tendsto :
          Tendsto (fun k : ℕ ↦ ‖(lam k)⁻¹ • (x (k + 1) - y k)‖) atTop
            (𝓝 0) := by
        have hright :
            Tendsto (fun k : ℕ ↦ ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖) atTop
              (𝓝 (0 + (R2 * lam0⁻¹) * 0)) :=
          h_eta_tendsto_zero.add
            ((tendsto_zero_iff_norm_tendsto_zero.mp h_xi_tendsto).const_mul
              (R2 * lam0⁻¹))
        have hright0 :
            Tendsto (fun k : ℕ ↦ ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖) atTop
              (𝓝 0) := by
          simpa using hright
        exact squeeze_zero (fun k => norm_nonneg _) hnorm_bound hright0
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
    have hv_eq (k : ℕ) : v k = eta k - (lam k)⁻¹ • (x (k + 1) - y k) := by
      rw [← rec.equation k]
      module
    have hdiff := h_eta_tendsto_zero_vec.sub hstep_scaled_tendsto
    have h_eq :
        (fun k : ℕ ↦ eta k - (lam k)⁻¹ • (x (k + 1) - y k)) =
          fun k : ℕ ↦ v k := by
      funext k
      exact (hv_eq k).symm
    simpa [h_eq] using hdiff
  have h_weak_cluster_condition :
      ∀ xhat : H, ∀ subseq : ℕ → ℕ, StrictMono subseq →
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (x (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) →
        xhat ∈ SetValuedOperator.zeros A := by
    intro xhat subseq hstrict hweak_subseq
    have hcont_toWeak : Continuous (toWeakSpace ℝ H : H → WeakSpace ℝ H) := by
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ H).continuous
    have hsubseq_atTop : Tendsto subseq atTop atTop := hstrict.tendsto_atTop
    have h_inertial_tendsto :
        Tendsto (fun k : ℕ ↦ alpha k • (x k - x (k - 1))) atTop (𝓝 (0 : H)) := by
      have h_norm :
          Tendsto (fun k : ℕ ↦ ‖alpha k • (x k - x (k - 1))‖) atTop (𝓝 0) := by
        have h_eq :
            (fun k : ℕ ↦ ‖alpha k • (x k - x (k - 1))‖) =
              (fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖) := by
          funext k
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (halpha_mem k).1]
        rw [h_eq]
        exact h_alpha_diff_norm_tendsto_zero
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm
    have hy_weak :
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (y (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) := by
      have h_inertial_subseq :
          Tendsto (fun j : ℕ ↦ alpha (subseq j) •
            (x (subseq j) - x (subseq j - 1))) atTop (𝓝 (0 : H)) :=
        h_inertial_tendsto.comp hsubseq_atTop
      have h_inertial_weak :
          Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H
              (alpha (subseq j) • (x (subseq j) - x (subseq j - 1)))) atTop
            (𝓝 (toWeakSpace ℝ H (0 : H))) :=
        (hcont_toWeak.tendsto (0 : H)).comp h_inertial_subseq
      have hsum := hweak_subseq.add h_inertial_weak
      have h_eq :
          (fun j : ℕ =>
              toWeakSpace ℝ H (x (subseq j)) +
                toWeakSpace ℝ H
                  (alpha (subseq j) • (x (subseq j) - x (subseq j - 1)))) =
            (fun j : ℕ => toWeakSpace ℝ H (y (subseq j))) := by
        funext j
        rw [rec.y_def (subseq j)]
        simp
      rw [h_eq] at hsum
      simpa using hsum
    have hy_minus_xi_weak :
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (y (subseq j) - xi (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) := by
      have h_xi_subseq : Tendsto (fun j : ℕ ↦ xi (subseq j)) atTop (𝓝 (0 : H)) :=
        h_xi_tendsto.comp hsubseq_atTop
      have h_xi_weak :
          Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (xi (subseq j))) atTop
            (𝓝 (toWeakSpace ℝ H (0 : H))) :=
        (hcont_toWeak.tendsto (0 : H)).comp h_xi_subseq
      have hdiff := hy_weak.sub h_xi_weak
      simpa using hdiff
    have h_scaled_xi_tendsto :
        Tendsto (fun j : ℕ ↦ (lam (subseq j))⁻¹ • xi (subseq j)) atTop
          (𝓝 (0 : H)) := by
      rcases hlam_lower with ⟨lam0, hlam0_pos, hlam0_le⟩
      have hnorm_bound (j : ℕ) :
          ‖(lam (subseq j))⁻¹ • xi (subseq j)‖ ≤ lam0⁻¹ * ‖xi (subseq j)‖ := by
        have hlam_subseq_pos : 0 < lam (subseq j) := hlam_pos (subseq j)
        calc
          ‖(lam (subseq j))⁻¹ • xi (subseq j)‖ =
              (lam (subseq j))⁻¹ * ‖xi (subseq j)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam_subseq_pos)]
          _ ≤ lam0⁻¹ * ‖xi (subseq j)‖ :=
            mul_le_mul_of_nonneg_right
              ((inv_le_inv₀ hlam_subseq_pos hlam0_pos).mpr (hlam0_le (subseq j)))
              (norm_nonneg _)
      have h_xi_norm_tendsto :
          Tendsto (fun j : ℕ ↦ ‖xi (subseq j)‖) atTop (𝓝 0) :=
        (tendsto_zero_iff_norm_tendsto_zero.mp h_xi_tendsto).comp hsubseq_atTop
      have hnorm_tendsto :
          Tendsto (fun j : ℕ ↦ ‖(lam (subseq j))⁻¹ • xi (subseq j)‖) atTop
            (𝓝 0) :=
        squeeze_zero (fun j => norm_nonneg _) hnorm_bound
          (by simpa using h_xi_norm_tendsto.const_mul lam0⁻¹)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
    rw [SetValuedOperator.mem_zeros_iff]
    exact weak_strong_closedness_maximal_monotone_graph A hA
      hy_minus_xi_weak h_scaled_xi_tendsto (fun j => hxi_graph (subseq j))
  have h_weak_conv : ∃ xstar ∈ SetValuedOperator.zeros A,
      Tendsto (fun k : ℕ => toWeakSpace ℝ H (x k)) atTop
        (𝓝 (toWeakSpace ℝ H xstar)) :=
    lemma_2_4_opial x (SetValuedOperator.zeros A) ⟨xbar, hxbar⟩ h_dist_all
      h_weak_cluster_condition
  exact ⟨hv_tendsto, h_weak_conv⟩

end Alvarez2004
