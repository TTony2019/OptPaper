import Foundation.SetValued.Resolvent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.Basic
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.thm_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_def_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_thm_1

namespace AlvarezAttouch2001

open SetValuedOperator
open scoped InnerProductSpace Topology Pointwise BigOperators
open Filter

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

set_option maxHeartbeats 600000 in
-- The summability estimates require an extended tactic budget.
/-- For nondecreasing inertial parameters bounded by a number below `1 / 3`,
the increments are square summable and the inertial proximal iterates converge weakly. -/
theorem inertial_proximal_point_converges_of_monotone_parameters
    {A : SetValuedOperator H H}
    (hA_max : IsMaximalMonotone A)
    (x : ℕ → H) (α lam : ℕ → ℝ)
    (h_alg : InertialProximalPointAlgorithm A x α lam)
    (hS_nonempty : (A.zeros).Nonempty)
    (h_lam : ∃ (lam0 : ℝ), 0 < lam0 ∧ ∀ k, lam0 ≤ lam k)
    (h_alpha' : ∃ (alph0 : ℝ), 0 ≤ alph0 ∧ alph0 < 1 / 3 ∧ (∀ k, 0 ≤ α k ∧ α k ≤ alph0) ∧ Monotone α) :
    Summable (fun k : ℕ ↦ ‖x (k + 1) - x k‖ ^ 2) ∧
    ∃ (xstar : H), xstar ∈ A.zeros ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xstar)) := by
  rcases h_alpha' with ⟨alph0, halph0_nonneg, halph0_lt_third, h_alpha_range, hα_mono⟩
  rcases h_lam with ⟨lam0, hlam0_pos, hlam0_le⟩
  have hA_max_orig : IsMaximalMonotone A := hA_max
  rcases hA_max with ⟨hA_mono, hA_max_graph⟩
  have hlam_pos (k : ℕ) : 0 < lam k := by
    have h := hlam0_le k; linarith
  have hα_nonneg (k : ℕ) : 0 ≤ α k := (h_alpha_range k).1
  have hα_le (k : ℕ) : α k ≤ alph0 := (h_alpha_range k).2
  have halph0_lt_one : alph0 < 1 := by linarith

  -- Algorithm witness
  have h_alg_witness (k : ℕ) (hk : 1 ≤ k) :
      ∃ (w : H), w ∈ A (x (k + 1)) ∧ x (k + 1) + lam k • w = x k + α k • (x k - x (k - 1)) := by
    have h := h_alg.update k hk
    rw [SetValuedOperator.mem_resolvent_smul_iff] at h
    simpa [SetValuedOperator.identityAddScaled, eq_comm] using h

  -- Monotonicity → inner product inequality
  have h_mono_ineq (z : H) (hz : z ∈ A.zeros) (k : ℕ) (hk : 1 ≤ k) :
      ⟪x (k + 1) - x k - α k • (x k - x (k - 1)), x (k + 1) - z⟫_ℝ ≤ 0 := by
    rcases h_alg_witness k hk with ⟨w, hw, hw_eq⟩
    have h0z : (0 : H) ∈ A z := by
      simpa [SetValuedOperator.mem_zeros_iff] using hz
    have hmono : 0 ≤ ⟪w, x (k + 1) - z⟫_ℝ := by
      simpa using hA_mono w hw (0 : H) h0z
    have h_eq_vec : x (k + 1) - x k - α k • (x k - x (k - 1)) + lam k • w = 0 := by
      calc
        x (k + 1) - x k - α k • (x k - x (k - 1)) + lam k • w
            = (x (k + 1) + lam k • w) - x k - α k • (x k - x (k - 1)) := by abel
        _ = (x k + α k • (x k - x (k - 1))) - x k - α k • (x k - x (k - 1)) := by rw [hw_eq]
        _ = 0 := by abel
    have h_inner_eq : ⟪x (k + 1) - x k - α k • (x k - x (k - 1)), x (k + 1) - z⟫_ℝ
        + lam k * ⟪w, x (k + 1) - z⟫_ℝ = 0 := by
      calc
        ⟪x (k + 1) - x k - α k • (x k - x (k - 1)), x (k + 1) - z⟫_ℝ
            + lam k * ⟪w, x (k + 1) - z⟫_ℝ
            = ⟪x (k + 1) - x k - α k • (x k - x (k - 1)) + lam k • w, x (k + 1) - z⟫_ℝ := by
          simp [inner_add_left, inner_smul_left]
        _ = ⟪(0 : H), x (k + 1) - z⟫_ℝ := by rw [h_eq_vec]
        _ = 0 := by simp
    have hpos : 0 ≤ lam k * ⟪w, x (k + 1) - z⟫_ℝ :=
      mul_nonneg (le_of_lt (hlam_pos k)) hmono
    linarith

  rcases hS_nonempty with ⟨z0, hz0⟩

  -- Energy: φ_n = (1/2)‖x^n - z0‖²
  set φ := fun (n : ℕ) => (1/2 : ℝ) * ‖x n - z0‖^2 with hφ_def
  have hφ_nonneg (n : ℕ) : 0 ≤ φ n := by
    dsimp [φ]; nlinarith [sq_nonneg ‖x n - z0‖]

  -- Helper: expand inner product
  have h_inner_expand (a b z : H) :
      ⟪a - b, a - z⟫_ℝ = (1/2 : ℝ) * (‖a - b‖^2 + ‖a - z‖^2 - ‖b - z‖^2) := by
    have h_norm_eq : ‖a - z‖^2 = ‖a - b‖^2 + 2 * ⟪a - b, b - z⟫_ℝ + ‖b - z‖^2 := by
      calc
        ‖a - z‖^2 = ‖(a - b) + (b - z)‖^2 := by simp
        _ = ⟪(a - b) + (b - z), (a - b) + (b - z)⟫_ℝ := by rw [← real_inner_self_eq_norm_sq]
        _ = ⟪a - b, a - b⟫_ℝ + ⟪a - b, b - z⟫_ℝ + ⟪b - z, a - b⟫_ℝ + ⟪b - z, b - z⟫_ℝ := by
          rw [inner_add_add_self]
        _ = ‖a - b‖^2 + 2 * ⟪a - b, b - z⟫_ℝ + ‖b - z‖^2 := by
          simp [real_inner_comm (a - b) (b - z)]; ring
    calc
      ⟪a - b, a - z⟫_ℝ = ⟪a - b, (a - b) + (b - z)⟫_ℝ := by simp
      _ = ‖a - b‖^2 + ⟪a - b, b - z⟫_ℝ := by
        rw [inner_add_right, real_inner_self_eq_norm_sq]
      _ = (1/2 : ℝ) * (‖a - b‖^2 + ‖a - z‖^2 - ‖b - z‖^2) := by linarith

  -- ============================================================
  -- STEP 1: Key inequality
  --   φ_{k+1} - φ_k - α_k(φ_k - φ_{k-1}) ≤
  --     ((α_k - 1)/2)‖x^{k+1} - x^k‖² + α_k‖x^k - x^{k-1}‖²
  -- ============================================================
  have h_phi_ineq (k : ℕ) (hk : 1 ≤ k) :
      φ (k+1) - φ k - α k * (φ k - φ (k-1)) ≤
      ((α k - 1)/2) * ‖x (k+1) - x k‖^2 + α k * ‖x k - x (k-1)‖^2 := by
    have h_ineq := h_mono_ineq z0 hz0 k hk
    -- h_ineq : ⟪x(k+1) - x k - α_k·(x k - x(k-1)), x(k+1) - z0⟫ ≤ 0
    have h_cross_expand : ⟪x k - x (k-1), x (k+1) - z0⟫_ℝ =
        (φ k - φ (k-1)) + (1/2 : ℝ) * ‖x k - x (k-1)‖^2
        + ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ := by
      have h_decomp : x (k+1) - z0 = (x k - z0) + (x (k+1) - x k) := by abel
      rw [h_decomp, inner_add_right, h_inner_expand (x k) (x (k-1)) z0]
      dsimp [φ]; ring
    have h_full_expand : ⟪x (k+1) - x k - α k • (x k - x (k-1)), x (k+1) - z0⟫_ℝ
        = (φ (k+1) - φ k) + (1/2 : ℝ) * ‖x (k+1) - x k‖^2
          - α k * ((φ k - φ (k-1)) + (1/2 : ℝ) * ‖x k - x (k-1)‖^2
            + ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ) := by
      rw [inner_sub_left, real_inner_smul_left]
      rw [h_inner_expand (x (k+1)) (x k) z0, h_cross_expand]
      dsimp [φ]; ring
    rw [h_full_expand] at h_ineq
    -- Rearrange h_ineq
    have h_intermediate : φ (k+1) - φ k - α k * (φ k - φ (k-1))
        ≤ -(1/2 : ℝ) * ‖x (k+1) - x k‖^2 + α k * ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ
          + (α k / 2) * ‖x k - x (k-1)‖^2 := by linarith
    -- Bound the cross inner product using 0 ≤ ‖a - b‖² = ‖a‖² + ‖b‖² - 2⟨a,b⟩
    have h_cross_bound : ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ ≤
        (1/2 : ℝ) * (‖x k - x (k-1)‖^2 + ‖x (k+1) - x k‖^2) := by
      set u := x k - x (k-1) with hu
      set v := x (k+1) - x k with hv
      have h_sq_expand : ‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * ⟪u, v⟫_ℝ := by
        rw [← real_inner_self_eq_norm_sq]
        rw [inner_sub_left]
        simp [inner_sub_right, real_inner_comm u v]
        ring
      have h_nonneg : 0 ≤ ‖u‖^2 + ‖v‖^2 - 2 * ⟪u, v⟫_ℝ := by
        rw [← h_sq_expand]; exact sq_nonneg _
      linarith
    -- Multiply the cross bound by α_k ≥ 0
    have h_α_cross_bound : α k * ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ
        ≤ α k * ((1/2 : ℝ) * (‖x k - x (k-1)‖^2 + ‖x (k+1) - x k‖^2)) := by
      have hαk_nonneg : 0 ≤ α k := hα_nonneg k
      nlinarith
    linarith

  -- ============================================================
  -- STEP 2: Define μ_k and prove key properties
  -- ============================================================

  set μ := fun (k : ℕ) => φ k - α k * φ (k-1) + α k * ‖x k - x (k-1)‖^2 with hμ_def

  have h_μ_diff (k : ℕ) (hk : 1 ≤ k) :
      μ (k+1) - μ k ≤ -((1 - 3*alph0)/2) * ‖x (k+1) - x k‖^2 := by
    dsimp [μ]
    have h_α_nondec_nonpos : α k - α (k+1) ≤ 0 := by
      have h := hα_mono (Nat.le_succ k)
      linarith
    have hcoeff_bound : ((α k - 1)/2 + α (k+1)) ≤ -((1 - 3*alph0)/2) := by
      have hk : α k ≤ alph0 := hα_le k
      have hkp1 : α (k+1) ≤ alph0 := hα_le (k+1)
      nlinarith
    calc
      (φ (k+1) - α (k+1) * φ k + α (k+1) * ‖x (k+1) - x k‖^2)
          - (φ k - α k * φ (k-1) + α k * ‖x k - x (k-1)‖^2)
        = (φ (k+1) - φ k - α k * (φ k - φ (k-1)))
          + (α k - α (k+1)) * φ k
          + (α (k+1) * ‖x (k+1) - x k‖^2 - α k * ‖x k - x (k-1)‖^2) := by ring
      _ ≤ (((α k - 1)/2) * ‖x (k+1) - x k‖^2 + α k * ‖x k - x (k-1)‖^2)
          + (α k - α (k+1)) * φ k
          + (α (k+1) * ‖x (k+1) - x k‖^2 - α k * ‖x k - x (k-1)‖^2) := by
        nlinarith [h_phi_ineq k hk]
      _ = ((α k - 1)/2 + α (k+1)) * ‖x (k+1) - x k‖^2 + (α k - α (k+1)) * φ k := by ring
      _ ≤ ((α k - 1)/2 + α (k+1)) * ‖x (k+1) - x k‖^2 := by
        have h_nonpos_φk : (α k - α (k+1)) * φ k ≤ 0 := by
          nlinarith [hφ_nonneg k]
        nlinarith
      _ ≤ -((1 - 3*alph0)/2) * ‖x (k+1) - x k‖^2 := by
        nlinarith [sq_nonneg ‖x (k+1) - x k‖]

  -- Corollary: μ is nonincreasing for k ≥ 1
  have h_μ_noninc (k : ℕ) (hk : 1 ≤ k) : μ (k+1) ≤ μ k := by
    have h := h_μ_diff k hk
    nlinarith [sq_nonneg ‖x (k+1) - x k‖]

  -- Bound on ‖x(k+1)-x k‖² in terms of μ_k - μ_{k+1}
  have h_sq_perstep (k : ℕ) (hk : 1 ≤ k) :
      ((1 - 3*alph0)/2) * ‖x (k+1) - x k‖^2 ≤ μ k - μ (k+1) := by
    have h := h_μ_diff k hk
    linarith

  -- Lower bound on μ_k
  have h_μ_lower (k : ℕ) (hk : 1 ≤ k) : -alph0 * φ (k-1) ≤ μ k := by
    dsimp [μ]
    have hφk1_nonneg : 0 ≤ φ (k-1) := hφ_nonneg (k-1)
    have hαk_nonneg : 0 ≤ α k := hα_nonneg k
    nlinarith [hα_le k, sq_nonneg ‖x k - x (k-1)‖, hφ_nonneg k, hφk1_nonneg, hαk_nonneg]

  -- μ is nonincreasing chain: 1 ≤ a ≤ b → μ b ≤ μ a
  have h_μ_noninc_gen (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) : μ b ≤ μ a := by
    induction' hab with b hab ih
    · rfl
    · have hb1 : 1 ≤ b := le_trans ha hab
      exact le_trans (h_μ_noninc b hb1) ih

  -- Recurrence for φ
  have h_φ_recurse (k : ℕ) (hk : 1 ≤ k) : φ k ≤ alph0 * φ (k-1) + μ 1 := by
    have h_lower : φ k - alph0 * φ (k-1) ≤ μ k := by
      dsimp [μ]
      nlinarith [hα_le k, sq_nonneg ‖x k - x (k-1)‖, hφ_nonneg (k-1), hα_nonneg k]
    have h_μk_le_μ1 : μ k ≤ μ 1 := h_μ_noninc_gen 1 k (by omega) hk
    linarith

  -- ============================================================
  -- STEP 3: Prove μ 1 ≥ 0 (by quadratic form argument)
  -- ============================================================

  have hμ1_nonneg : 0 ≤ μ 1 := by
    dsimp [μ, φ]
    set u := x 1 - z0 with hu
    set v := x 0 - z0 with hv
    have h_diff : x 1 - x 0 = u - v := by simp [u, v]
    rw [h_diff]
    by_cases hα1_zero : α 1 = 0
    · rw [hα1_zero]; simp
    · have hpos : 0 < 1/2 + α 1 := by
        have hα1_nonneg : 0 ≤ α 1 := hα_nonneg 1
        nlinarith
      -- Key: ‖√(1/2+α₁)·u - (α₁/√(1/2+α₁))·v‖² ≥ 0  →  controls the cross term
      set s := Real.sqrt (1/2 + α 1) with hs
      set t := α 1 / s with ht
      have hs_sq : s^2 = 1/2 + α 1 := Real.sq_sqrt (by nlinarith)
      have hs_pos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
      have h_ineq : 2 * α 1 * ⟪u, v⟫_ℝ ≤ (1/2 + α 1) * ‖u‖^2 + (α 1 ^ 2 / (1/2 + α 1)) * ‖v‖^2 := by
        have h_norm_sq_nonneg : 0 ≤ ‖s • u - t • v‖^2 := sq_nonneg _
        have h_expand : ‖s • u - t • v‖^2 = s^2 * ‖u‖^2 - 2 * (s * t) * ⟪u, v⟫_ℝ + t^2 * ‖v‖^2 := by
          calc
            ‖s • u - t • v‖^2 = ⟪s • u - t • v, s • u - t • v⟫_ℝ := by rw [← real_inner_self_eq_norm_sq]
            _ = ⟪s • u, s • u⟫_ℝ - ⟪s • u, t • v⟫_ℝ - ⟪t • v, s • u⟫_ℝ + ⟪t • v, t • v⟫_ℝ := by
              rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
            _ = ‖s • u‖^2 - 2 * ⟪s • u, t • v⟫_ℝ + ‖t • v‖^2 := by
              simp [real_inner_comm (s • u) (t • v)]; ring
            _ = s^2 * ‖u‖^2 - 2 * (s * t) * ⟪u, v⟫_ℝ + t^2 * ‖v‖^2 := by
              simp [norm_smul, real_inner_smul_left, real_inner_smul_right, sq_abs, mul_pow]; ring
        have h_st : s * t = α 1 := by
          dsimp [t]
          field_simp [hs_pos.ne']
        rw [h_expand, h_st, hs_sq] at h_norm_sq_nonneg
        have ht_sq : t^2 = α 1 ^ 2 / (1/2 + α 1) := by
          dsimp [t]
          rw [div_pow]
          rw [hs_sq]
        rw [ht_sq] at h_norm_sq_nonneg
        nlinarith
      have hcoeff_nonneg : 0 ≤ (α 1 / 2) - (α 1 ^ 2 / (1/2 + α 1)) := by
        have hpos_den : 0 < 1/2 + α 1 := by nlinarith [hα_nonneg 1]
        have hα_lt_half : α 1 < 1/2 := by
          have h := hα_le 1; linarith
        have h_sq_div : α 1 ^ 2 / (1/2 + α 1) ≤ α 1 / 2 := by
          refine ((div_le_div_iff₀ hpos_den (by norm_num : 0 < (2 : ℝ))).mpr ?_)
          have h_nonpos : α 1 * (α 1 - 1/2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (hα_nonneg 1) (by linarith)
          nlinarith
        linarith
      have h_norm_sq_expand : ‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * ⟪u, v⟫_ℝ := by
        rw [← real_inner_self_eq_norm_sq]
        rw [inner_sub_left]
        simp [inner_sub_right, real_inner_comm u v]
        ring
      have h_main_ineq : 0 ≤ (1/2 : ℝ) * ‖u‖^2 - α 1 * ((1/2 : ℝ) * ‖v‖^2) + α 1 * ‖u - v‖^2 := by
        rw [h_norm_sq_expand]
        have h_expr : (1/2 : ℝ) * ‖u‖^2 - α 1 * ((1/2 : ℝ) * ‖v‖^2) + α 1 * (‖u‖^2 + ‖v‖^2 - 2 * ⟪u, v⟫_ℝ)
            = (1/2 + α 1) * ‖u‖^2 + (α 1 / 2) * ‖v‖^2 - 2 * α 1 * ⟪u, v⟫_ℝ := by ring
        rw [h_expr]
        have hpos : 0 ≤ (1/2 + α 1) * ‖u‖^2 + (α 1 / 2) * ‖v‖^2 - 2 * α 1 * ⟪u, v⟫_ℝ := by
          have h_v_sq_nonneg : 0 ≤ ‖v‖^2 := sq_nonneg _
          have h_nonneg_coeff : 0 ≤ (α 1 / 2) - (α 1 ^ 2 / (1/2 + α 1)) := hcoeff_nonneg
          have h_ineq' : 2 * α 1 * ⟪u, v⟫_ℝ ≤ (1/2 + α 1) * ‖u‖^2 + (α 1 ^ 2 / (1/2 + α 1)) * ‖v‖^2 := h_ineq
          have htemp : (1/2 + α 1) * ‖u‖^2 + (α 1 / 2) * ‖v‖^2 - 2 * α 1 * ⟪u, v⟫_ℝ
              ≥ ((α 1 / 2) - (α 1 ^ 2 / (1/2 + α 1))) * ‖v‖^2 := by
            linarith
          have h_nonneg_prod : 0 ≤ ((α 1 / 2) - (α 1 ^ 2 / (1/2 + α 1))) * ‖v‖^2 :=
            mul_nonneg h_nonneg_coeff h_v_sq_nonneg
          linarith
        exact hpos
      exact h_main_ineq

  -- ============================================================
  -- STEP 4: Bound φ_k
  -- ============================================================

  have h_φ_bound (k : ℕ) : φ k ≤ alph0 ^ k * φ 0 + μ 1 / (1 - alph0) := by
    induction' k with k ih
    · simp [pow_zero, one_mul]
      have hdiv_nonneg : 0 ≤ μ 1 / (1 - alph0) :=
        div_nonneg hμ1_nonneg (by linarith)
      nlinarith
    · by_cases hk0 : k = 0
      · subst hk0
        have h := h_φ_recurse 1 (by omega)
        calc
          φ 1 ≤ alph0 * φ 0 + μ 1 := h
          _ = alph0 ^ 1 * φ 0 + μ 1 / (1 - alph0) - alph0 * μ 1 / (1 - alph0) := by
            field_simp [show 1 - alph0 ≠ 0 from by linarith]; ring
          _ ≤ alph0 ^ 1 * φ 0 + μ 1 / (1 - alph0) := by
            have h_nonneg : 0 ≤ alph0 * μ 1 / (1 - alph0) :=
              div_nonneg (mul_nonneg halph0_nonneg hμ1_nonneg) (by linarith)
            nlinarith
      · have hk1 : 1 ≤ k + 1 := by omega
        have hrec := h_φ_recurse (k+1) hk1
        calc
          φ (k+1) ≤ alph0 * φ k + μ 1 := hrec
          _ ≤ alph0 * (alph0 ^ k * φ 0 + μ 1 / (1 - alph0)) + μ 1 := by
            have h_mul : alph0 * φ k ≤ alph0 * (alph0 ^ k * φ 0 + μ 1 / (1 - alph0)) :=
              mul_le_mul_of_nonneg_left ih halph0_nonneg
            nlinarith
          _ = alph0 ^ (k+1) * φ 0 + μ 1 * (alph0 / (1 - alph0) + 1) := by ring
          _ = alph0 ^ (k+1) * φ 0 + μ 1 / (1 - alph0) := by
            field_simp [show 1 - alph0 ≠ 0 from by linarith]; ring

  -- ============================================================
  -- STEP 5: Telescoping sum → partial sums bounded → summable
  -- ============================================================

  have h_telescope (N : ℕ) : (Finset.sum (Finset.range N) fun k => (μ (k+1) - μ (k+2))) = μ 1 - μ (N+1) := by
    induction' N with N ih
    · simp
    · rw [Finset.sum_range_succ, ih]
      linarith

  -- Constant bounding the tail sum
  set Ctail := (2 / (1 - 3*alph0)) * (μ 1 / (1 - alph0) + φ 0) with hCtail_def

  have hpos_denom : 0 < 1 - 3*alph0 := by linarith
  have hpos_factor : 0 ≤ 2/(1 - 3*alph0) := div_nonneg (by norm_num) hpos_denom.le

  have h_tail_sum_bound (M : ℕ) : (Finset.sum (Finset.range M) fun k => ‖x (k+1+1) - x (k+1)‖^2) ≤ Ctail := by
    have hcalc : (2 / (1 - 3*alph0)) * (μ 1 + alph0 * (alph0 ^ M * φ 0 + μ 1 / (1 - alph0)))
        = (2 / (1 - 3*alph0)) * (μ 1 / (1 - alph0) + alph0 ^ (M+1) * φ 0) := by
      field_simp [show 1 - alph0 ≠ 0 from by linarith]
      ring
    have hpow_le : alph0 ^ (M+1) ≤ 1 :=
      pow_le_one₀ (a := alph0) (n := M+1) halph0_nonneg (by linarith)
    calc
      (Finset.sum (Finset.range M) fun k => ‖x (k+1+1) - x (k+1)‖^2)
          ≤ (Finset.sum (Finset.range M) fun k => ((2/(1 - 3*alph0)) * (μ (k+1) - μ (k+2)))) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hbound := h_sq_perstep (k+1) (by omega)
        calc
          ‖x (k+1+1) - x (k+1)‖^2
              = (2/(1 - 3*alph0)) * (((1 - 3*alph0)/2) * ‖x (k+1+1) - x (k+1)‖^2) := by
            field_simp [hpos_denom.ne']
          _ ≤ (2/(1 - 3*alph0)) * (μ (k+1) - μ (k+2)) :=
            mul_le_mul_of_nonneg_left hbound hpos_factor
      _ = (2/(1 - 3*alph0)) * (Finset.sum (Finset.range M) fun k => (μ (k+1) - μ (k+2))) := by
        rw [Finset.mul_sum]
      _ = (2/(1 - 3*alph0)) * (μ 1 - μ (M+1)) := by rw [h_telescope M]
      _ ≤ (2/(1 - 3*alph0)) * (μ 1 + alph0 * φ M) := by
        have hlow : -alph0 * φ M ≤ μ (M+1) := h_μ_lower (M+1) (by omega)
        gcongr; linarith
      _ ≤ (2/(1 - 3*alph0)) * (μ 1 + alph0 * (alph0 ^ M * φ 0 + μ 1 / (1 - alph0))) := by
        gcongr
        · nlinarith [halph0_nonneg, h_φ_bound M]
      _ = (2/(1 - 3*alph0)) * (μ 1 / (1 - alph0) + alph0 ^ (M+1) * φ 0) := by rw [hcalc]
      _ ≤ (2/(1 - 3*alph0)) * (μ 1 / (1 - alph0) + φ 0) := by
        gcongr
        · nlinarith [hpow_le, hφ_nonneg 0, halph0_nonneg]
      _ = Ctail := rfl

  -- Decomposition: Σ_{0}^{N-1} a_k = a_0 + Σ_{0}^{N-2} a_{k+1}
  have h_sum_decomp (N : ℕ) (hN : 1 ≤ N) : (Finset.sum (Finset.range N) fun k => ‖x (k+1) - x k‖^2)
      = ‖x 1 - x 0‖^2 + (Finset.sum (Finset.range (N-1)) fun k => ‖x (k+1+1) - x (k+1)‖^2) := by
    induction' N with M ih
    · omega
    · by_cases hM0 : M = 0
      · subst hM0; simp
      · have hM : 1 ≤ M := by omega
        rw [Finset.sum_range_succ, ih hM]
        have hM_eq : ((M:ℕ)-1)+1 = M := Nat.sub_add_cancel hM
        have hB : Finset.sum (Finset.range M) (fun k => ‖x (k+1+1) - x (k+1)‖^2)
            = Finset.sum (Finset.range (M-1)) (fun k => ‖x (k+1+1) - x (k+1)‖^2)
              + ‖x (M+1) - x M‖^2 := by
          calc
            Finset.sum (Finset.range M) (fun k => ‖x (k+1+1) - x (k+1)‖^2)
                = Finset.sum (Finset.range (((M:ℕ)-1)+1)) (fun k => ‖x (k+1+1) - x (k+1)‖^2) := by rw [hM_eq]
            _ = Finset.sum (Finset.range (M-1)) (fun k => ‖x (k+1+1) - x (k+1)‖^2)
                + ‖x ((M-1)+1+1) - x ((M-1)+1)‖^2 := by rw [Finset.sum_range_succ]
            _ = Finset.sum (Finset.range (M-1)) (fun k => ‖x (k+1+1) - x (k+1)‖^2)
                + ‖x (M+1) - x M‖^2 := by
              have h2 : (M-1 : ℕ)+1 = M := by omega
              simp [h2]
        simp [hB, add_comm, add_left_comm]

  -- Final partial sum bound
  set C := ‖x 1 - x 0‖^2 + Ctail with hC_def

  have h_partial_sum_bound (N : ℕ) : (Finset.sum (Finset.range N) fun k => ‖x (k+1) - x k‖^2) ≤ C := by
    by_cases hN0 : N = 0
    · subst hN0; simp [C, hC_def, Ctail]
      have h_nonneg : 0 ≤ ‖x 1 - x 0‖^2 + (2 / (1 - 3*alph0)) * (μ 1 / (1 - alph0) + φ 0) := by
        refine add_nonneg (sq_nonneg _) (mul_nonneg
          (div_nonneg (by norm_num) (by linarith)) ?_)
        refine add_nonneg (div_nonneg hμ1_nonneg (by linarith)) (hφ_nonneg 0)
      exact h_nonneg
    · have hNpos : 1 ≤ N := by omega
      rw [h_sum_decomp N hNpos]
      have htail := h_tail_sum_bound (N-1)
      dsimp [C, Ctail]
      nlinarith

  -- ============================================================
  -- STEP 6: Conclude summability
  -- ============================================================

  have h_summable_sq : Summable (fun k : ℕ ↦ ‖x (k + 1) - x k‖ ^ 2) := by
    refine summable_of_sum_range_le (c := C) (fun n => sq_nonneg _) (fun n => ?_)
    exact h_partial_sum_bound n

  -- ============================================================
  -- STEP 7: Apply Theorem 2.1 to get convergence
  -- ============================================================

  have h_summable_α_sq : Summable (fun k : ℕ ↦ α (k + 1) * ‖x (k + 1) - x k‖ ^ 2) := by
    have h_nonneg (k : ℕ) : 0 ≤ α (k+1) * ‖x (k+1) - x k‖ ^ 2 := by
      nlinarith [hα_nonneg (k+1), sq_nonneg ‖x (k+1) - x k‖]
    have h_bound (k : ℕ) : α (k+1) * ‖x (k+1) - x k‖ ^ 2 ≤ alph0 * (‖x (k+1) - x k‖ ^ 2) := by
      gcongr; exact hα_le (k+1)
    have h_summable_dom : Summable (fun k : ℕ => alph0 * (‖x (k+1) - x k‖ ^ 2)) :=
      h_summable_sq.const_smul alph0
    refine Summable.of_nonneg_of_le h_nonneg h_bound h_summable_dom

  have h_alpha_for_thm : ∃ (alph0' : ℝ), 0 ≤ alph0' ∧ alph0' < 1 ∧ ∀ k, 0 ≤ α k ∧ α k ≤ alph0' := by
    refine ⟨alph0, halph0_nonneg, halph0_lt_one, h_alpha_range⟩

  rcases inertial_proximal_point_converges hA_max_orig x α lam h_alg ⟨z0, hz0⟩
    ⟨lam0, hlam0_pos, hlam0_le⟩ h_alpha_for_thm h_summable_α_sq with ⟨xstar, hxstar, hxstar_weak⟩

  exact ⟨h_summable_sq, xstar, hxstar, hxstar_weak⟩

end AlvarezAttouch2001
