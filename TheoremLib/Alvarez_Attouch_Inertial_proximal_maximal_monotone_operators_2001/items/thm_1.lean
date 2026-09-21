import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.Basic
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_2
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.algo_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.lem_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_def_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_thm_1

namespace AlvarezAttouch2001

open SetValuedOperator
open scoped InnerProductSpace Topology Pointwise BigOperators
open Filter

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

set_option maxHeartbeats 600000 in
-- The energy estimates and subsequence argument require an extended tactic budget.
/-- The inertial proximal point iterates converge weakly under the summability condition. -/
theorem inertial_proximal_point_converges
    {A : SetValuedOperator H H}
    (hA_max : IsMaximalMonotone A)
    (x : ℕ → H) (α lam : ℕ → ℝ)
    (h_alg : InertialProximalPointAlgorithm A x α lam)
    (hS_nonempty : (A.zeros).Nonempty)
    (h_lam : ∃ (lam0 : ℝ), 0 < lam0 ∧ ∀ k, lam0 ≤ lam k)
    (h_alpha : ∃ (alph0 : ℝ), 0 ≤ alph0 ∧ alph0 < 1 ∧ ∀ k, 0 ≤ α k ∧ α k ≤ alph0)
    (h_summable : Summable fun k : ℕ ↦ α (k + 1) * ‖x (k + 1) - x k‖ ^ 2) :
    ∃ (xstar : H), xstar ∈ A.zeros ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xstar)) := by
  -- Extract parameters
  rcases hA_max with ⟨hA_mono, hA_max⟩
  rcases h_lam with ⟨lam0, hlam0_pos, hlam0_le⟩
  rcases h_alpha with ⟨alph0, halph0_nonneg, halph0_lt_one, h_alpha_range⟩
  have hlam_pos (k : ℕ) : 0 < lam k := by
    have h := hlam0_le k; linarith
  have hα_nonneg (k : ℕ) : 0 ≤ α k := (h_alpha_range k).1
  have hα_le (k : ℕ) : α k ≤ alph0 := (h_alpha_range k).2

  /- A monotone bounded-above sequence of reals converges to its supremum. -/
  -- This is mathlib's `tendsto_atTop_ciSup`

  -- Algorithm expands to give a witness in A
  have h_alg_witness (k : ℕ) (hk : 1 ≤ k) :
      ∃ (w : H), w ∈ A (x (k + 1)) ∧ x (k + 1) + lam k • w = x k + α k • (x k - x (k - 1)) := by
    have h := h_alg.update k hk
    rw [SetValuedOperator.mem_resolvent_smul_iff] at h
    have hmem : x k + α k • (x k - x (k - 1)) ∈
        {x (k + 1) + lam k • v | v ∈ A (x (k + 1))} := by
      simpa [SetValuedOperator.identityAddScaled] using h
    rcases hmem with ⟨w, hw, hw_eq⟩
    exact ⟨w, hw, hw_eq⟩

  -- Monotonicity gives inner product inequality
  have h_mono_ineq (z : H) (hz : z ∈ A.zeros) (k : ℕ) (hk : 1 ≤ k) :
      ⟪x (k + 1) - x k - α k • (x k - x (k - 1)), x (k + 1) - z⟫_ℝ ≤ 0 := by
    rcases h_alg_witness k hk with ⟨w, hw, hw_eq⟩
    have h0z : (0 : H) ∈ A z := by
      simpa [SetValuedOperator.mem_zeros_iff] using hz
    have hmono : 0 ≤ ⟪w - (0 : H), x (k + 1) - z⟫_ℝ := hA_mono w hw (0 : H) h0z
    simp at hmono
    have h_eq_vec : x (k + 1) - x k - α k • (x k - x (k - 1)) + lam k • w = 0 := by
      calc
        x (k + 1) - x k - α k • (x k - x (k - 1)) + lam k • w
            = (x (k + 1) + lam k • w) - x k - α k • (x k - x (k - 1)) := by abel
        _ = (x k + α k • (x k - x (k - 1))) - x k - α k • (x k - x (k - 1)) := by rw [hw_eq]
        _ = 0 := by abel
    have h_inner_eq :
        ⟪x (k + 1) - x k - α k • (x k - x (k - 1)), x (k + 1) - z⟫_ℝ
        + lam k * ⟪w, x (k + 1) - z⟫_ℝ = 0 := by
      calc
        ⟪x (k + 1) - x k - α k • (x k - x (k - 1)), x (k + 1) - z⟫_ℝ
            + lam k * ⟪w, x (k + 1) - z⟫_ℝ
            = ⟪x (k + 1) - x k - α k • (x k - x (k - 1)) + lam k • w, x (k + 1) - z⟫_ℝ := by
          simp [inner_add_left, inner_smul_left]
        _ = ⟪(0 : H), x (k + 1) - z⟫_ℝ := by rw [h_eq_vec]
        _ = 0 := by simp
    have hpos : 0 ≤ lam k * ⟪w, x (k + 1) - z⟫_ℝ := by
      have hlam_nonneg : 0 ≤ lam k := by linarith [hlam_pos k]
      nlinarith
    linarith

  -- Inner product identity
  have h_inner_expand1 (a b z : H) :
      ⟪a - b, a - z⟫_ℝ = (1/2 : ℝ) * (‖a - b‖^2 + ‖a - z‖^2 - ‖b - z‖^2) := by
    have h := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (a - b) (a - z)
    have hsub : (a - b) - (a - z) = z - b := by abel
    calc
      ⟪a - b, a - z⟫_ℝ = (‖a - b‖ * ‖a - b‖ + ‖a - z‖ * ‖a - z‖
        - ‖(a - b) - (a - z)‖ * ‖(a - b) - (a - z)‖) / 2 := h
      _ = (‖a - b‖^2 + ‖a - z‖^2 - ‖(a - b) - (a - z)‖^2) / 2 := by simp [sq]
      _ = (‖a - b‖^2 + ‖a - z‖^2 - ‖b - z‖^2) / 2 := by
        rw [hsub, show z - b = -(b - z) by abel, norm_neg]
      _ = (1/2 : ℝ) * (‖a - b‖^2 + ‖a - z‖^2 - ‖b - z‖^2) := by ring

  -- Define φ_k(z) = (1/2) ‖x^k - z‖²
  set φ := fun (z : H) (n : ℕ) => (1/2 : ℝ) * ‖x n - z‖^2

  -- Define v^{k+1} = x^{k+1} - x^k - α_k(x^k - x^{k-1})
  set v := fun (k : ℕ) => x (k+1) - x k - α k • (x k - x (k-1))

  -- Key inequality linking φ differences to v
  have h_phi_ineq (z : H) (hz : z ∈ A.zeros) (k : ℕ) (hk : 1 ≤ k) :
      φ z (k+1) - φ z k - α k * (φ z k - φ z (k-1)) ≤
      -(1/2 : ℝ) * ‖v k‖^2 + (1/2 : ℝ) * (α k + (α k)^2) * ‖x k - x (k-1)‖^2 := by
    have h_ineq := h_mono_ineq z hz k hk
    -- h_ineq: ⟪v k, x(k+1)-z⟫ ≤ 0
    -- Expand the inner product in terms of φ and norms
    -- Helper: ⟪x k - x(k-1), x(k+1) - z⟫ expansion
    have h_second_cross : ⟪x k - x (k-1), x (k+1) - z⟫_ℝ =
        (φ z k - φ z (k-1)) + (1/2 : ℝ) * ‖x k - x (k-1)‖^2
        + ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ := by
      have h_expand2 : x (k+1) - z = (x k - z) + (x (k+1) - x k) := by abel
      rw [h_expand2, inner_add_right, h_inner_expand1 (x k) (x (k-1)) z]
      dsimp [φ]
      ring_nf
    have h_expand : ⟪v k, x (k+1) - z⟫_ℝ
        = (φ z (k+1) - φ z k) + (1/2 : ℝ) * ‖x (k+1) - x k‖^2
          - α k * ((φ z k - φ z (k-1)) + (1/2 : ℝ) * ‖x k - x (k-1)‖^2
            + ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ) := by
      dsimp [v]
      rw [inner_sub_left]; simp [real_inner_smul_left]
      rw [h_inner_expand1 (x (k+1)) (x k) z, h_second_cross]
      dsimp [φ]
      ring_nf
    rw [h_expand] at h_ineq
    -- Now h_ineq: φ(k+1)-φ(k) + (1/2)‖x(k+1)-x k‖² - α_k·(...) ≤ 0
    -- Rearrange to isolate φ terms
    have h_rearr : φ z (k+1) - φ z k - α k * (φ z k - φ z (k-1))
        ≤ -(1/2 : ℝ) * ‖x (k+1) - x k‖^2
          + α k * ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ
          + (α k / 2) * ‖x k - x (k-1)‖^2 := by linarith
    -- Complete the square
    have h_sq : -(1/2 : ℝ) * ‖x (k+1) - x k‖^2
        + α k * ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ
        + (α k / 2) * ‖x k - x (k-1)‖^2
        = -(1/2 : ℝ) * ‖v k‖^2 + (1/2 : ℝ) * (α k + (α k)^2) * ‖x k - x (k-1)‖^2 := by
      dsimp [v]
      have h_sq_expand : ‖x (k+1) - x k - α k • (x k - x (k-1))‖^2 =
          ‖x (k+1) - x k‖^2 - 2 * α k * ⟪x (k+1) - x k, x k - x (k-1)⟫_ℝ
          + (α k)^2 * ‖x k - x (k-1)‖^2 := by
        calc
          ‖x (k+1) - x k - α k • (x k - x (k-1))‖^2
              = ‖x (k+1) - x k‖^2 - 2 * inner ℝ (x (k+1) - x k) (α k • (x k - x (k-1)))
                + ‖α k • (x k - x (k-1))‖^2 := by rw [norm_sub_pow_two_real]
          _ = ‖x (k+1) - x k‖^2 - 2 * (α k * inner ℝ (x (k+1) - x k) (x k - x (k-1)))
              + ‖α k • (x k - x (k-1))‖^2 := by rw [real_inner_smul_right]
          _ = ‖x (k+1) - x k‖^2 - 2 * α k * inner ℝ (x (k+1) - x k) (x k - x (k-1))
              + ‖α k • (x k - x (k-1))‖^2 := by ring
          _ = ‖x (k+1) - x k‖^2 - 2 * α k * ⟪x (k+1) - x k, x k - x (k-1)⟫_ℝ
              + (α k)^2 * ‖x k - x (k-1)‖^2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα_nonneg k)]
            ring
      have h_symm : ⟪x (k+1) - x k, x k - x (k-1)⟫_ℝ
          = ⟪x k - x (k-1), x (k+1) - x k⟫_ℝ := real_inner_comm _ _
      rw [h_sq_expand, h_symm]
      ring
    rw [h_sq] at h_rearr
    exact h_rearr

  -- Define δ_seq(m) = α(m+1) ‖x(m+1) - x m‖²
  set δ_seq := fun (m : ℕ) => α (m+1) * ‖x (m+1) - x m‖^2

  -- Simplified θ inequality: φ_{k+1} - φ_k ≤ α_k·u_{k-1} + δ_{k-1}
  -- where u_{k-1} = [φ_k - φ_{k-1}]_+
  have h_theta_ineq (z : H) (hz : z ∈ A.zeros) (k : ℕ) (hk : 1 ≤ k) :
      φ z (k+1) - φ z k ≤ α k * max (φ z k - φ z (k-1)) 0 + δ_seq (k-1) := by
    have h := h_phi_ineq z hz k hk
    have h_nonpos : -(1/2 : ℝ) * ‖v k‖^2 ≤ 0 := by nlinarith [sq_nonneg ‖v k‖]
    have h_sq_bound : (α k + (α k)^2) ≤ 2 * α k := by
      have hαk_le_one : α k ≤ 1 := by linarith [hα_le k, halph0_lt_one]
      calc
        (α k + (α k)^2) = α k * (1 + α k) := by ring
        _ ≤ α k * (1 + 1) := mul_le_mul_of_nonneg_left (by linarith) (hα_nonneg k)
        _ = 2 * α k := by ring
    have h_alpha_bound : (1/2 : ℝ) * (α k + (α k)^2) * ‖x k - x (k-1)‖^2 ≤ δ_seq (k-1) := by
      dsimp [δ_seq]
      have hk' : (k : ℕ) - 1 + 1 = k := by omega
      simp [hk']
      have h_nonneg_sq : 0 ≤ ‖x k - x (k-1)‖^2 := sq_nonneg _
      have h_mul : (α k + (α k)^2) * ‖x k - x (k-1)‖^2 ≤ 2 * α k * ‖x k - x (k-1)‖^2 :=
        mul_le_mul_of_nonneg_right h_sq_bound h_nonneg_sq
      linarith
    have h_simple : φ z (k+1) - φ z k - α k * (φ z k - φ z (k-1)) ≤ δ_seq (k-1) := by linarith
    by_cases hpos : 0 ≤ φ z k - φ z (k-1)
    · have : φ z (k+1) - φ z k ≤ α k * (φ z k - φ z (k-1)) + δ_seq (k-1) := by linarith
      have hmax : α k * (φ z k - φ z (k-1)) = α k * max (φ z k - φ z (k-1)) 0 := by
        rw [max_eq_left hpos]
      rw [hmax] at this; exact this
    · have : φ z (k+1) - φ z k ≤ α k * (φ z k - φ z (k-1)) + δ_seq (k-1) := by linarith
      have hmax : max (φ z k - φ z (k-1)) 0 = 0 := max_eq_right (by linarith)
      have hneg_mul : α k * (φ z k - φ z (k-1)) ≤ 0 := by nlinarith
      nlinarith

  -- Define u_k = [θ_{k+1}]_+ = max(φ_{k+1} - φ_k, 0)
  set u := fun (z : H) (k : ℕ) => max (φ z (k+1) - φ z k) 0
  have hu_nonneg (z : H) (k : ℕ) : 0 ≤ u z k := by simp [u]

  -- Recurrence: u_k ≤ alph0·u_{k-1} + δ_seq(k-1) for k ≥ 1
  have h_u_recurrence (z : H) (hz : z ∈ A.zeros) (k : ℕ) (hk : 1 ≤ k) :
      u z k ≤ alph0 * u z (k-1) + δ_seq (k-1) := by
    have h_ineq := h_theta_ineq z hz k hk
    have h_nonneg_rhs : 0 ≤ alph0 * u z (k-1) + δ_seq (k-1) := by
      have h_nonneg_u : 0 ≤ u z (k-1) := hu_nonneg z (k-1)
      have h_nonneg_δ : 0 ≤ δ_seq (k-1) := by
        dsimp [δ_seq]
        have hk' : (k-1 : ℕ) + 1 = k := by omega
        simp [hk']
        nlinarith [hα_nonneg k, sq_nonneg ‖x k - x (k-1)‖]
      nlinarith
    have h_le_rhs : φ z (k+1) - φ z k ≤ alph0 * u z (k-1) + δ_seq (k-1) := by
      have hαk_bound : α k * u z (k-1) ≤ alph0 * u z (k-1) := by
        nlinarith [hα_le k, hu_nonneg z (k-1)]
      have htemp : φ z (k+1) - φ z k ≤ α k * u z (k-1) + δ_seq (k-1) := by
        have hk_eq : ((k : ℕ) - 1) + 1 = k := by omega
        simpa [u, hk_eq] using h_ineq
      linarith
    have hu_pos : u z k = max (φ z (k+1) - φ z k) 0 := rfl
    rw [hu_pos]
    have : max (φ z (k+1) - φ z k) 0 ≤ max (alph0 * u z (k-1) + δ_seq (k-1)) 0 :=
      max_le_max h_le_rhs (by rfl)
    simpa [max_eq_left h_nonneg_rhs]

  -- ====== OPIAL CONDITION (a): ‖x n - z‖ converges for each z ∈ A.zeros ======
  have h_dist_converges (z : H) (hz : z ∈ A.zeros) :
      ∃ (l : ℝ), Tendsto (fun n : ℕ ↦ ‖x n - z‖) atTop (𝓝 l) := by
    -- Bounded partial sums of δ_seq
    have h_bdd_delta : BddAbove (Set.range fun n : ℕ => Finset.sum (Finset.range n) δ_seq) :=
      h_summable.hasSum.tendsto_sum_nat.bddAbove_range
    rcases h_bdd_delta with ⟨D, hD⟩
    have h_fin_sum_le_D (n : ℕ) : Finset.sum (Finset.range n) δ_seq ≤ D :=
      hD (Set.mem_range_self n)
    have hD_nonneg : 0 ≤ D := by
      have h0 : Finset.sum (Finset.range 0) δ_seq = 0 := by simp
      have hle : Finset.sum (Finset.range 0) δ_seq ≤ D := h_fin_sum_le_D 0
      simpa [h0] using hle

    -- Define S_n = ∑_{k=0}^{n-1} u_k (partial sums of u)
    set S := fun (n : ℕ) => Finset.sum (Finset.range n) (u z)
    have hS_mono : Monotone S := by
      refine monotone_nat_of_le_succ (fun n => ?_)
      dsimp [S]; rw [Finset.sum_range_succ]
      have h := hu_nonneg z n
      linarith

    -- THE KEY BOUND: (1-alph0)·S_N ≤ u_0 + D
    -- This implies all partial sums S_N are bounded, so S_n converges
    have h_S_bound (N : ℕ) : (1 - alph0) * S N ≤ u z 0 + D := by
      by_cases hN : N < 2
      · -- N = 0 or 1
        have hN_cases : N = 0 ∨ N = 1 := by omega
        rcases hN_cases with (rfl | rfl)
        · -- N = 0
          simp [S]
          exact add_nonneg (hu_nonneg z 0) hD_nonneg
        · -- N = 1
          simp [S]
          have h_mul : (1 - alph0) * u z 0 ≤ u z 0 := by
            have h' : 1 - alph0 ≤ 1 := by linarith
            have h_u0_nonneg : 0 ≤ u z 0 := hu_nonneg z 0
            nlinarith
          nlinarith [hD_nonneg]
      · -- N ≥ 2
        have h_recur_sum : Finset.sum (Finset.range (N-1))
            (fun k => u z (k+1) - alph0 * u z k) ≤ Finset.sum (Finset.range (N-1)) δ_seq := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          have hkpos : 1 ≤ k+1 := by omega
          have hrec := h_u_recurrence z hz (k+1) hkpos
          have hrec' : u z (k+1) ≤ alph0 * u z k + δ_seq k := by
            simpa [show ((k+1 : ℕ) - 1) = k by omega] using hrec
          linarith
        have h_sum_eq : Finset.sum (Finset.range (N-1)) (fun k => u z (k+1) - alph0 * u z k) =
            S N - u z 0 - alph0 * S (N-1) := by
          dsimp [S]
          calc
            Finset.sum (Finset.range (N-1)) (fun k => u z (k+1) - alph0 * u z k)
                = Finset.sum (Finset.range (N-1)) (fun k => u z (k+1))
                  - alph0 * Finset.sum (Finset.range (N-1)) (u z) := by
              simp [Finset.sum_sub_distrib, Finset.mul_sum]
            _ = (Finset.sum (Finset.range N) (u z) - u z 0)
                - alph0 * Finset.sum (Finset.range (N-1)) (u z) := by
              have h_shift : Finset.sum (Finset.range (N-1)) (fun k => u z (k+1)) =
                  Finset.sum (Finset.range N) (u z) - u z 0 := by
                have h := Finset.sum_range_succ' (u z) (N-1)
                have h_idx : (N : ℕ) - 1 + 1 = N := by omega
                rw [h_idx] at h; linarith
              rw [h_shift]
            _ = Finset.sum (Finset.range N) (u z) - u z 0
                - alph0 * Finset.sum (Finset.range (N-1)) (u z) := rfl
        rw [h_sum_eq] at h_recur_sum
        have h_S_N1_le : Finset.sum (Finset.range (N-1)) (u z) ≤ S N := by
          dsimp [S]
          have hN_eq : N = (N-1) + 1 := by omega
          rw [hN_eq, Finset.sum_range_succ]
          exact le_add_of_nonneg_right (hu_nonneg z (N-1))
        have h_target : S N - alph0 * S N ≤ u z 0 + D := by
          calc
            S N - alph0 * S N ≤ S N - alph0 * Finset.sum (Finset.range (N-1)) (u z) := by
              dsimp [S]
              nlinarith
            _ ≤ u z 0 + Finset.sum (Finset.range (N-1)) δ_seq := by
              dsimp [S] at h_recur_sum; linarith
            _ ≤ u z 0 + D := by nlinarith [h_fin_sum_le_D (N-1)]
        dsimp [S] at h_target ⊢
        nlinarith

    -- Partial sums are bounded
    have hS_bdd : BddAbove (Set.range S) := by
      refine ⟨(u z 0 + D) / (1 - alph0), ?_⟩
      rintro y ⟨N, rfl⟩
      have hpos : 0 < 1 - alph0 := by linarith
      have h := h_S_bound N
      -- S ≤ (u0 + D)/(1-alph0)
      rw [le_div_iff₀ hpos]
      nlinarith

    -- Monotone bounded → converges
    set u_limit := ⨆ n, S n
    have hS_tendsto : Tendsto S atTop (𝓝 u_limit) :=
      tendsto_atTop_ciSup hS_mono hS_bdd

    -- Define w_n = φ_n - S_n; show w_n is nonincreasing and bounded below
    set w := fun (n : ℕ) => φ z n - S n
    have hw_noninc (k : ℕ) : w (k+1) ≤ w k := by
      dsimp [w, S]
      rw [Finset.sum_range_succ (u z) k]
      have hφ_diff : φ z (k+1) - φ z k ≤ u z k := by
        have : φ z (k+1) - φ z k ≤ max (φ z (k+1) - φ z k) 0 := le_max_left _ _
        simp [u]
      linarith
    have hw_bdd_below : BddBelow (Set.range w) := by
      rcases hS_bdd with ⟨M, hM⟩
      refine ⟨-M, ?_⟩
      rintro y ⟨n, rfl⟩
      dsimp [w]
      have hφ_nonneg : 0 ≤ φ z n := by dsimp [φ]; nlinarith [sq_nonneg ‖x n - z‖]
      have hSn_le : S n ≤ M := hM (Set.mem_range_self n)
      linarith
    have hw_anti : Antitone w := by
      intro a b h
      induction' h with b h ih
      · rfl
      · exact le_trans (hw_noninc b) ih
    have hw_conv : ∃ lw, Tendsto w atTop (𝓝 lw) := by
      -- w is antitone and bounded below, so -w is monotone and bounded above → converges
      have h_neg_w_mono : Monotone (-w) := by
        intro a b h
        have hwab : w b ≤ w a := hw_anti h
        exact neg_le_neg hwab
      have h_neg_w_bdd : BddAbove (Set.range (-w)) := by
        rcases hw_bdd_below with ⟨L, hL⟩
        refine ⟨-L, ?_⟩
        rintro y ⟨n, rfl⟩
        have h := hL (Set.mem_range_self n)
        exact neg_le_neg h
      have h_neg_w_tendsto : Tendsto (-w) atTop (𝓝 (⨆ n, (-w) n)) :=
        tendsto_atTop_ciSup h_neg_w_mono h_neg_w_bdd
      have h_w_tendsto : Tendsto w atTop (𝓝 (-(⨆ n, (-w) n))) := by
        simpa using h_neg_w_tendsto.neg
      exact ⟨-(⨆ n, (-w) n), h_w_tendsto⟩
    rcases hw_conv with ⟨lw, hw_tendsto⟩

    -- φ_n = w_n + S_n converges
    have hφ_conv : Tendsto (φ z) atTop (𝓝 (lw + u_limit)) := by
      simpa [w] using hw_tendsto.add hS_tendsto
    -- φ_n = (1/2)‖x n - z‖², so norms converge
    have h_normsq_conv : Tendsto (fun n : ℕ => ‖x n - z‖^2) atTop (𝓝 (2 * (lw + u_limit))) := by
      have : (fun n : ℕ => ‖x n - z‖^2) = fun n => 2 * φ z n := by
        ext n; dsimp [φ]; ring
      rw [this]; simpa using hφ_conv.const_mul 2
    have h_lim_nonneg : 0 ≤ 2 * (lw + u_limit) := by
      have h_nonneg : ∀ n, 0 ≤ ‖x n - z‖^2 := fun n => by positivity
      have h_mem : ∀ᶠ n in atTop, ‖x n - z‖^2 ∈ {x : ℝ | 0 ≤ x} :=
        Filter.Eventually.of_forall h_nonneg
      exact isClosed_Ici.mem_of_tendsto h_normsq_conv h_mem
    have h_norm_conv : Tendsto (fun n : ℕ => ‖x n - z‖) atTop (𝓝 (Real.sqrt (2 * (lw + u_limit)))) := by
      have h_eq : (fun n : ℕ => ‖x n - z‖) = Real.sqrt ∘ (fun n : ℕ => ‖x n - z‖^2) := by
        ext n; simp
      rw [h_eq]
      exact Real.continuous_sqrt.continuousAt.tendsto.comp h_normsq_conv
    exact ⟨Real.sqrt (2 * (lw + u_limit)), h_norm_conv⟩

  -- ====== OPIAL CONDITION (b): weak cluster points are in A.zeros ======
  have h_cluster_property : ∀ (z : H),
      IsSequentialClusterPt (fun n : ℕ => toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ A.zeros := by
    intro z h_cluster
    -- Pick a reference point in A.zeros to use pointwise inequalities
    rcases hS_nonempty with ⟨z0, hz0⟩

    -- From h_dist_converges, φ(z0, n) = (1/2)‖x n - z0‖² converges
    rcases h_dist_converges z0 hz0 with ⟨lz0, hlz0⟩
    have h_phi_tendsto : Tendsto (φ z0) atTop (𝓝 ((1/2 : ℝ) * lz0 ^ 2)) := by
      have : (φ z0) = fun n => (1/2 : ℝ) * (‖x n - z0‖ ^ 2) := by
        ext n; dsimp [φ]
      rw [this]
      simpa using (hlz0.pow 2).const_mul (1/2 : ℝ)

    -- Hence the differences φ(k+1) - φ(k) → 0, so u_k = max(φ(k+1)-φ(k), 0) → 0
    have h_phi_diff_tendsto : Tendsto (fun k : ℕ => φ z0 (k+1) - φ z0 k) atTop (𝓝 0) := by
      have h_shift : Tendsto (fun k : ℕ => φ z0 (k+1)) atTop (𝓝 ((1/2 : ℝ) * lz0 ^ 2)) :=
        h_phi_tendsto.comp (tendsto_add_atTop_nat 1)
      simpa [sub_self] using h_shift.sub h_phi_tendsto

    have hu_tendsto : Tendsto (u z0) atTop (𝓝 0) := by
      have h_nonneg : ∀ k, 0 ≤ u z0 k := hu_nonneg z0
      have h_bound : ∀ k, u z0 k ≤ |φ z0 (k+1) - φ z0 k| := by
        intro k
        dsimp [u]
        by_cases h : 0 ≤ φ z0 (k+1) - φ z0 k
        · rw [max_eq_left h, abs_of_nonneg h]
        · rw [max_eq_right (by linarith : φ z0 (k+1) - φ z0 k ≤ 0)]
          exact abs_nonneg _
      have h_abs_tendsto : Tendsto (fun k : ℕ => |φ z0 (k+1) - φ z0 k|) atTop (𝓝 |(0 : ℝ)|) :=
        h_phi_diff_tendsto.abs
      simp at h_abs_tendsto
      -- squeeze_zero: 0 ≤ u_k ≤ |d_k| → 0 ⇒ u_k → 0
      exact squeeze_zero (fun n => h_nonneg n) h_bound h_abs_tendsto

    -- δ_seq → 0 (terms of summable series)
    have hδ_tendsto : Tendsto δ_seq atTop (𝓝 0) :=
      h_summable.tendsto_atTop_zero

    -- Helper to shift a null sequence: if f n → 0, then f (n-1) → 0 as n → ∞
    have h_tendsto_shift {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
        Tendsto (fun k : ℕ => f (k-1)) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop] at hf ⊢
      intro ε hε
      rcases hf ε hε with ⟨N, hN⟩
      refine ⟨N+1, fun k hk => hN (k-1) (by omega)⟩

    -- The key pointwise inequality for k ≥ 1
    have h_v_sq_bound (k : ℕ) (hk : 1 ≤ k) : ‖v k‖^2 ≤ 2 * (φ z0 k - φ z0 (k+1) + alph0 * u z0 (k-1) + δ_seq (k-1)) := by
      have hineq := h_phi_ineq z0 hz0 k hk
      -- Rearrange: (1/2)·‖v k‖² ≤ (φ_k - φ_{k+1}) + α_k·(φ_k-φ_{k-1}) + (1/2)(α_k+α_k²)·‖x_k - x_{k-1}‖²
      have h_rearr : (1/2 : ℝ) * ‖v k‖^2 ≤ φ z0 k - φ z0 (k+1) + α k * (φ z0 k - φ z0 (k-1))
          + (1/2 : ℝ) * (α k + (α k)^2) * ‖x k - x (k-1)‖^2 := by linarith
      -- Bound the third term: (1/2)(α_k+α_k²)·‖x_k - x_{k-1}‖² ≤ δ_{k-1} (since α_k ≤ 1)
      have h_third_bound : (1/2 : ℝ) * (α k + (α k)^2) * ‖x k - x (k-1)‖^2 ≤ δ_seq (k-1) := by
        have hαk_sq : (α k + (α k)^2) ≤ 2 * α k := by
          have hαk_le_one : α k ≤ 1 := by linarith [hα_le k, halph0_lt_one]
          calc
            (α k + (α k)^2) = α k * (1 + α k) := by ring
            _ ≤ α k * (1 + 1) := mul_le_mul_of_nonneg_left (by linarith) (hα_nonneg k)
            _ = 2 * α k := by ring
        have h_nonneg_sq : 0 ≤ ‖x k - x (k-1)‖^2 := sq_nonneg _
        have hδ_eq : δ_seq (k-1) = α k * ‖x k - x (k-1)‖^2 := by
          dsimp [δ_seq]
          have : ((k : ℕ) - 1) + 1 = k := by omega
          simp [this]
        rw [hδ_eq]
        nlinarith
      -- Bound α_k·(φ_k - φ_{k-1}) ≤ alph0·u_{k-1}
      have h_u_bound : α k * (φ z0 k - φ z0 (k-1)) ≤ alph0 * u z0 (k-1) := by
        by_cases hpos : 0 ≤ φ z0 k - φ z0 (k-1)
        · have hle : φ z0 k - φ z0 (k-1) ≤ u z0 (k-1) := by
            dsimp [u]
            rw [show (k-1 : ℕ) + 1 = k by omega]
            exact le_max_left _ _
          nlinarith [hα_le k, hα_nonneg k, hu_nonneg z0 (k-1)]
        · nlinarith [hα_nonneg k, hu_nonneg z0 (k-1)]
      nlinarith

    -- RHS bound: each term → 0 individually
    have h_rhs_tendsto : Tendsto (fun k : ℕ => 2 * (φ z0 k - φ z0 (k+1) + alph0 * u z0 (k-1) + δ_seq (k-1))) atTop (𝓝 0) := by
      have h_phi_diff_neg : Tendsto (fun k : ℕ => φ z0 k - φ z0 (k+1)) atTop (𝓝 0) := by
        simpa using h_phi_diff_tendsto.neg
      have h_u_shift : Tendsto (fun k : ℕ => u z0 (k-1)) atTop (𝓝 0) := h_tendsto_shift hu_tendsto
      have hδ_shift : Tendsto (fun k : ℕ => δ_seq (k-1)) atTop (𝓝 0) := h_tendsto_shift hδ_tendsto
      have h_sum : Tendsto (fun k : ℕ => (φ z0 k - φ z0 (k+1)) + alph0 * u z0 (k-1) + δ_seq (k-1)) atTop (𝓝 0) := by
        have h_term2 : Tendsto (fun k : ℕ => alph0 * u z0 (k-1)) atTop (𝓝 0) := by
          simpa [mul_zero] using Filter.Tendsto.const_mul alph0 h_u_shift
        simpa [add_assoc] using (h_phi_diff_neg.add h_term2).add hδ_shift
      simpa using h_sum.const_mul 2

    -- Therefore ‖v k‖² → 0 (since 0 ≤ ‖v k‖² ≤ RHS for k ≥ 1)
    have hv_sq_tendsto : Tendsto (fun k : ℕ => ‖v k‖^2) atTop (𝓝 0) := by
      have h_nonneg : ∀ k, 0 ≤ ‖v k‖^2 := fun k => sq_nonneg _
      -- Define a modified RHS that equals the true bound for k ≥ 1, and equals ‖v k‖² for k = 0
      let b : ℕ → ℝ := fun k =>
        if h : 1 ≤ k then
          2 * (φ z0 k - φ z0 (k+1) + alph0 * u z0 (k-1) + δ_seq (k-1))
        else ‖v k‖^2
      have hb_bound : ∀ k, ‖v k‖^2 ≤ b k := by
        intro k; dsimp [b]
        by_cases hk : 1 ≤ k
        · simp [hk, h_v_sq_bound k hk]
        · simp [hk]
      have hb_tendsto : Tendsto b atTop (𝓝 0) := by
        -- Direct epsilon-N proof: for k ≥ max(N,1), b k = rhs k
        rw [Metric.tendsto_atTop]
        intro ε hε
        rw [Metric.tendsto_atTop] at h_rhs_tendsto
        rcases h_rhs_tendsto ε hε with ⟨N, hN⟩
        refine ⟨max N 1, fun n hn => ?_⟩
        have hn1 : 1 ≤ n := by omega
        have hnN : N ≤ n := by omega
        have hbn : b n = 2 * (φ z0 n - φ z0 (n+1) + alph0 * u z0 (n-1) + δ_seq (n-1)) := by
          dsimp [b]; simp [hn1]
        rw [hbn]
        simpa using hN n hnN
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb_tendsto h_nonneg hb_bound

    have hv_norm_tendsto : Tendsto (fun k : ℕ => ‖v k‖) atTop (𝓝 0) := by
      have h_eq : (fun k : ℕ => ‖v k‖) = Real.sqrt ∘ (fun k : ℕ => ‖v k‖^2) := by
        ext k; simp
      rw [h_eq]
      simpa using (Real.continuous_sqrt.tendsto 0).comp hv_sq_tendsto

    have hv_tendsto : Tendsto v atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero (f := v)).mpr hv_norm_tendsto

    -- ====== Extract subsequence from the weak cluster point ======
    rcases h_cluster.exists_subseq_tendsto with ⟨φ, hφ_mono, hφ_tendsto⟩
    -- hφ_tendsto: Tendsto (fun n => toWeakSpace ℝ H (x (φ n))) atTop (𝓝 (toWeakSpace ℝ H z))

    -- Shift by 2 so φ(n+2) ≥ 2, guaranteeing 1 ≤ φ(n+2)-1 for h_alg_witness
    set φ2 : ℕ → ℕ := fun n => φ (n + 2)
    have hφ2_strictMono : StrictMono φ2 := by
      intro a b h
      dsimp [φ2]
      exact hφ_mono (by omega)
    have hφ2_tendsto : Tendsto (fun n : ℕ => toWeakSpace ℝ H (x (φ2 n))) atTop (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [φ2] using hφ_tendsto.comp (tendsto_add_atTop_nat 2)

    -- For each n, get witness w ∈ A(x(φ2 n)) from the algorithm
    have hwitness (n : ℕ) : ∃ (w : H), w ∈ A (x (φ2 n)) ∧
        lam (φ2 n - 1) • w = -v (φ2 n - 1) := by
      have h_φ_ge_id : ∀ m, m ≤ φ m := by
        intro m
        induction' m with k ih
        · exact Nat.zero_le _
        · have hlt : φ k < φ (k+1) := hφ_mono (Nat.lt_succ_self k)
          have h_succ_le : φ k + 1 ≤ φ (k+1) := Nat.succ_le_of_lt hlt
          omega
      have hk : 1 ≤ φ2 n - 1 := by
        have hge2 : 2 ≤ φ2 n := by
          dsimp [φ2]
          have h := h_φ_ge_id (n+2)
          omega
        omega
      rcases h_alg_witness (φ2 n - 1) hk with ⟨w, hw_mem, hw_eq⟩
      have h_idx : (φ2 n - 1) + 1 = φ2 n := by omega
      have hw_mem' : w ∈ A (x (φ2 n)) := by
        simpa [h_idx] using hw_mem
      have hw_eq' : x (φ2 n) + lam (φ2 n - 1) • w =
          x (φ2 n - 1) + α (φ2 n - 1) • (x (φ2 n - 1) - x ((φ2 n - 1) - 1)) := by
        simpa [h_idx] using hw_eq
      have h_goal : lam (φ2 n - 1) • w = -v (φ2 n - 1) := by
        dsimp [v]
        -- v expands to x((φ2 n - 1)+1) - x(φ2 n - 1) - α(...)
        -- So we need to rewrite (φ2 n - 1) + 1 = φ2 n
        rw [h_idx]
        -- Goal: lam•w = -(x(φ2 n) - x(φ2 n - 1) - α(...)•(...))
        -- RHS simplifies: -(x - x' - c) = (x' + c) - x  (true in any AddCommGroup)
        have hRHS : -(x (φ2 n) - x (φ2 n - 1) - α (φ2 n - 1) • (x (φ2 n - 1) - x ((φ2 n - 1) - 1))) =
            (x (φ2 n - 1) + α (φ2 n - 1) • (x (φ2 n - 1) - x ((φ2 n - 1) - 1))) - x (φ2 n) := by
          abel
        rw [hRHS]
        -- Goal: lam•w = (x' + c) - x
        -- Using eq_sub_iff_add_eq: a = b - c ↔ a + c = b
        rw [eq_sub_iff_add_eq]
        -- Goal: lam•w + x(φ2 n) = x(φ2 n - 1) + α•(...)
        rw [add_comm, hw_eq']
      exact ⟨w, hw_mem', h_goal⟩

    -- y n ∈ A(x(φ2 n)) with lam·y n = -v(φ2 n - 1)
    let y : ℕ → H := fun n => (hwitness n).choose
    have hy_mem (n : ℕ) : y n ∈ A (x (φ2 n)) := (hwitness n).choose_spec.1
    have hy_eq (n : ℕ) : lam (φ2 n - 1) • y n = -v (φ2 n - 1) := (hwitness n).choose_spec.2

    -- Show y n → 0 using ‖y n‖ = ‖v(φ2 n - 1)‖ / lam(φ2 n - 1) ≤ ‖v(φ2 n - 1)‖ / lam0
    have hy_norm_bound (n : ℕ) : ‖y n‖ ≤ ‖v (φ2 n - 1)‖ / lam0 := by
      have h_lam_pos : 0 < lam (φ2 n - 1) := hlam_pos (φ2 n - 1)
      have h_norm_eq : ‖lam (φ2 n - 1) • y n‖ = lam (φ2 n - 1) * ‖y n‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_lam_pos]
      have h_norm_v : ‖lam (φ2 n - 1) • y n‖ = ‖v (φ2 n - 1)‖ := by
        rw [hy_eq n, norm_neg]
      rw [h_norm_eq] at h_norm_v
      calc
        ‖y n‖ = ‖v (φ2 n - 1)‖ / lam (φ2 n - 1) := by
          field_simp [ne_of_gt h_lam_pos]; linarith
        _ = ‖v (φ2 n - 1)‖ * (1 / lam (φ2 n - 1)) := by ring
        _ ≤ ‖v (φ2 n - 1)‖ * (1 / lam0) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (one_div_le_one_div (by positivity) hlam0_pos).mpr (hlam0_le (φ2 n - 1))
        _ = ‖v (φ2 n - 1)‖ / lam0 := by ring

    -- Compose: ‖v k‖ → 0 and φ2 n → ∞ ⇒ ‖v(φ2 n - 1)‖ → 0
    have h_φ2_tendsto_atTop : Tendsto φ2 atTop atTop := hφ2_strictMono.tendsto_atTop
    have h_φ2_sub1_tendsto : Tendsto (fun n : ℕ => φ2 n - 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro C
      rcases (Filter.tendsto_atTop_atTop.mp h_φ2_tendsto_atTop) (C+1) with ⟨N, hN⟩
      exact ⟨N, fun n hn => by have h := hN n hn; omega⟩

    have hv_norm_comp : Tendsto (fun n : ℕ => ‖v (φ2 n - 1)‖) atTop (𝓝 0) :=
      hv_norm_tendsto.comp h_φ2_sub1_tendsto

    have hdiv_tendsto : Tendsto (fun n : ℕ => ‖v (φ2 n - 1)‖ / lam0) atTop (𝓝 0) := by
      simpa using hv_norm_comp.div_const lam0

    have hy_norm_tendsto : Tendsto (fun n : ℕ => ‖y n‖) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv_tendsto
        (fun n => norm_nonneg _) hy_norm_bound

    have hy_tendsto : Tendsto y atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero (f := y)).mpr hy_norm_tendsto

    -- Apply weak-strong closedness of maximal monotone graphs
    have hA_max' : IsMaximalMonotone A := ⟨hA_mono, hA_max⟩
    have h0_in_Az : (0 : H) ∈ A z :=
      weak_strong_closedness_maximal_monotone_graph A hA_max' hφ2_tendsto hy_tendsto hy_mem

    rw [SetValuedOperator.mem_zeros_iff]
    exact h0_in_Az

  -- Apply Opial's lemma
  have h_opial_dist : ∀ z ∈ (A.zeros : Set H), ∃ l : ℝ,
      Tendsto (fun n : ℕ => ‖x n - z‖) atTop (𝓝 l) := by
    intro z hz; exact h_dist_converges z hz
  rcases opial_lemma hS_nonempty x h_opial_dist h_cluster_property with ⟨xstar, hxstar, hxstar_weak⟩
  exact ⟨xstar, hxstar, hxstar_weak⟩

end AlvarezAttouch2001
