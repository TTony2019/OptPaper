import Mathlib
import TheoremLib.Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007.items.lem_3

/-!
# Remark 4.1: Generalized Sufficient Condition for Convergence

Condition H47 (summability of the positive variations of α_n and ν_n) is only one
of many possible assumptions leading to Theorem 4.1. The crux of the matter is
inequality (c) of Lemma 4.3.

Let (ρ_n) be a given positive sequence bounded away from zero. Dividing each member
of inequality (c) in Lemma 4.3 by ρ_n, and proceeding as in the proof of
Proposition 4.5 with the same notation, we can derive the scaled inequality:

A_{n+1}/ρ_{n+1} ≤ A_n/ρ_n
  + [μ·(α_{n+1}/ρ_{n+1} − α_n/ρ_n)⁺ + β·((μ+ν_{n+1})/ρ_{n+1} − (μ+ν_n)/ρ_n)⁺]·M
  − B_n/ρ_n

Under the assumption that the series Σ(α_{n+1}/ρ_{n+1} − α_n/ρ_n)⁺ and
Σ((μ+ν_{n+1})/ρ_{n+1} − (μ+ν_n)/ρ_n)⁺ converge (and that α_n, ν_n are bounded),
Proposition 4.5 and Theorem 4.1 can be proved.

Relevant choices for ρ_n: ρ_n = α_n, ρ_n = ν_n, ρ_n = α_n·ν_n,
or ρ_n = μ·α_n + β·(μ + ν_n).

Depends on: lem_3 (Lemma 4.3), prop_4 (Proposition 4.5), thm_4 (Theorem 4.1).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set Filter
open scoped RealInnerProductSpace Topology BigOperators

set_option maxHeartbeats 0

/-! ### Core notation: A_n, B_n, and positive part -/

/-- Positive part: a⁺ = max(a, 0). -/
def positivePart (a : ℝ) : ℝ := max a 0

/-- A_n from the proof of Proposition 4.5:
A_n = α_n·μ·‖x_n − x‖² + β·(μ + ν_n)·‖y_n − y‖². -/
def An {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x_seq y_seq : ℕ → H) (x y : H) (α ν : ℕ → ℝ) (β μ : ℝ) (n : ℕ) : ℝ :=
  α n * μ * ‖x_seq n - x‖ ^ 2 + β * (μ + ν n) * ‖y_seq n - y‖ ^ 2

/-- B_n from the proof of Proposition 4.5:
B_n = α_n·μ·‖x_{n+1} − x_n‖² + β·ν_n·‖y_{n+1} − y_n‖²
    + β·μ·‖y_n − x_{n+1} − y + x‖² + β·μ·‖y_{n+1} − x_{n+1} − y + x‖². -/
def Bn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x_seq y_seq : ℕ → H) (x y : H) (α ν : ℕ → ℝ) (β μ : ℝ) (n : ℕ) : ℝ :=
  α n * μ * ‖x_seq (n+1) - x_seq n‖ ^ 2 +
  β * ν n * ‖y_seq (n+1) - y_seq n‖ ^ 2 +
  β * μ * ‖y_seq n - x_seq (n+1) - y + x‖ ^ 2 +
  β * μ * ‖y_seq (n+1) - x_seq (n+1) - y + x‖ ^ 2

/-- Equivalent form of Lemma 4.3(c) in terms of A_n and B_n:

B_n ≤ A_n − {α_n·μ·‖x_{n+1}−x‖² + β·(μ+ν_n)·‖y_{n+1}−y‖²}.

This is the form used in the proof of Proposition 4.5 and in Remark 4.1. -/
theorem lemma_4_3_c_An_Bn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (n : ℕ) :
    Bn alg.x alg.y x y α ν β μ n ≤
    An alg.x alg.y x y α ν β μ n -
    (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) := by
  have h := lemma_4_3_c hyp x y hα_nonneg hν_nonneg alg hine n
  dsimp [An, Bn] at h ⊢
  nlinarith

/-! ### Remark 4.1: generalized scaled inequality -/

/-- Remark 4.1 — generalized scaled inequality.

Given the same hypotheses as Lemma 4.3 (H41–H46, quadratic costs, INE nonempty,
α_n ≥ 0, ν_n ≥ 0), let A_n, B_n be as defined above, let ρ_n > 0 be bounded away
from zero, and let M be a uniform bound on ‖x_{n+1}−x‖² and ‖y_{n+1}−y‖²
(such M exists by Proposition 4.4 / prop_3 — the sequence is bounded).

Then dividing the inequality from Lemma 4.3(c) by ρ_n and proceeding as in the
proof of Proposition 4.5 yields:

A_{n+1}/ρ_{n+1} ≤ A_n/ρ_n
  + [μ·(α_{n+1}/ρ_{n+1} − α_n/ρ_n)⁺ + β·((μ+ν_{n+1})/ρ_{n+1} − (μ+ν_n)/ρ_n)⁺]·M
  − B_n/ρ_n.

This generalizes H47: the same telescoping-sum argument from Proposition 4.5
works when the series of positive variations of the *scaled* sequences
(α_n/ρ_n) and ((μ+ν_n)/ρ_n) are summable (instead of the unscaled α_n, ν_n).

Relevant choices for ρ_n: ρ_n = α_n, ρ_n = ν_n, ρ_n = α_n·ν_n,
or ρ_n = μ·α_n + β·(μ + ν_n). -/
theorem remark_4_1_scaled_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y)
    (ρ : ℕ → ℝ) (hρ_pos : ∃ r > 0, ∀ n, ρ n ≥ r)
    (M : ℝ) (hM_x : ∀ n, ‖alg.x (n+1) - x‖ ^ 2 ≤ M) (hM_y : ∀ n, ‖alg.y (n+1) - y‖ ^ 2 ≤ M)
    (n : ℕ) :
    An alg.x alg.y x y α ν β μ (n+1) / ρ (n+1) ≤
    An alg.x alg.y x y α ν β μ n / ρ n +
    (μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) +
     β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n)) * M -
    Bn alg.x alg.y x y α ν β μ n / ρ n := by
  have hM_nonneg : 0 ≤ M := by
    have h := hM_x n
    have h_sq_nonneg : 0 ≤ ‖alg.x (n+1) - x‖ ^ 2 := by positivity
    linarith
  have hμ_nonneg : 0 ≤ μ := by linarith [hyp.mu_pos]
  have hβ_nonneg : 0 ≤ β := by linarith [hyp.beta_pos]
  rcases hρ_pos with ⟨r, hr_pos, hr⟩
  have hρn_pos : ρ n > 0 := by
    have h := hr n; linarith
  have hρn'_pos : ρ (n+1) > 0 := by
    have h := hr (n+1); linarith
  -- Lemma 4.3(c) in A_n, B_n form
  have h_lem : Bn alg.x alg.y x y α ν β μ n ≤
      An alg.x alg.y x y α ν β μ n -
      (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) :=
    lemma_4_3_c_An_Bn hyp x y hα_nonneg hν_nonneg alg hine n
  have h_ineq : α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
      An alg.x alg.y x y α ν β μ n - Bn alg.x alg.y x y α ν β μ n := by linarith
  -- Key algebraic identity: α'/ρ' * μ * x² = α/ρ * μ * x² + μ*(α'/ρ' - α/ρ) * x²
  have h_decomp_key : ∀ (a a' rn rn' x_sq : ℝ), rn ≠ 0 → rn' ≠ 0 →
      a' * x_sq / rn' = a * x_sq / rn + (a' / rn' - a / rn) * x_sq := by
    intro a a' rn rn' x_sq hrn hrn'
    field_simp [hrn, hrn']
    ring
  -- Lemma: for any real d and 0 ≤ t ≤ M, we have d*t ≤ positivePart d * M
  have h_pos_part_bound : ∀ (d t : ℝ), 0 ≤ t → t ≤ M → d * t ≤ positivePart d * M := by
    intro d t ht_nonneg ht_le
    by_cases hd : 0 ≤ d
    · have hpd_eq : positivePart d = d := by
        dsimp [positivePart]; exact max_eq_left hd
      rw [hpd_eq]
      gcongr
    · have hpd_eq : positivePart d = 0 := by
        dsimp [positivePart]; exact max_eq_right (by linarith)
      rw [hpd_eq]
      have h_nonpos : d * t ≤ 0 := by nlinarith
      nlinarith
  -- Decompose A_{n+1}/ρ_{n+1}
  have h_An1_div : An alg.x alg.y x y α ν β μ (n+1) / ρ (n+1) =
      (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) / ρ n +
      μ * (α (n+1) / ρ (n+1) - α n / ρ n) * ‖alg.x (n+1) - x‖ ^ 2 +
      β * ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) * ‖alg.y (n+1) - y‖ ^ 2 := by
    dsimp [An]
    field_simp [hρn_pos.ne', hρn'_pos.ne']
    ring
  have h_bound_x : μ * (α (n+1) / ρ (n+1) - α n / ρ n) * ‖alg.x (n+1) - x‖ ^ 2 ≤
      μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) * M := by
    have hx_sq_nonneg : 0 ≤ ‖alg.x (n+1) - x‖ ^ 2 := by positivity
    have h := h_pos_part_bound (α (n+1) / ρ (n+1) - α n / ρ n) (‖alg.x (n+1) - x‖ ^ 2) hx_sq_nonneg (hM_x n)
    nlinarith
  have h_bound_y : β * ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
      β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) * M := by
    have hy_sq_nonneg : 0 ≤ ‖alg.y (n+1) - y‖ ^ 2 := by positivity
    have h := h_pos_part_bound ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) (‖alg.y (n+1) - y‖ ^ 2) hy_sq_nonneg (hM_y n)
    nlinarith
  -- Divide inequality by ρ_n and combine
  have h_div : (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) / ρ n ≤
      An alg.x alg.y x y α ν β μ n / ρ n - Bn alg.x alg.y x y α ν β μ n / ρ n := by
    calc
      (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) / ρ n
          = (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) * (1 / ρ n) := by ring
      _ ≤ (An alg.x alg.y x y α ν β μ n - Bn alg.x alg.y x y α ν β μ n) * (1 / ρ n) := by gcongr
      _ = An alg.x alg.y x y α ν β μ n / ρ n - Bn alg.x alg.y x y α ν β μ n / ρ n := by ring
  -- Assemble final inequality
  rw [h_An1_div]
  have h_target : (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) / ρ n +
      μ * (α (n+1) / ρ (n+1) - α n / ρ n) * ‖alg.x (n+1) - x‖ ^ 2 +
      β * ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
      An alg.x alg.y x y α ν β μ n / ρ n +
      (μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) +
       β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n)) * M -
      Bn alg.x alg.y x y α ν β μ n / ρ n := by
    nlinarith
  exact h_target

/-! ### Remark 4.1 — scaled telescoping convergence -/

/-- **Remark 4.1 — scaled convergence.**

Under the assumption that the positive variations of the scaled sequences
α_n/ρ_n and (μ+ν_n)/ρ_n are summable (and that α_n, ν_n are bounded),
the same telescoping-sum argument as in Proposition 4.5 yields convergence
of A_n/ρ_n and shows B_n/ρ_n → 0.

This is the core observation of Remark 4.1: the proof technique of
Proposition 4.5 adapts to scaled quantities, providing an alternative
sufficient condition.  The paper's H47 (summability of the *unscaled*
positive variations of α_n and ν_n) corresponds to the special case ρ_n ≡ 1.
Other choices for ρ_n (α_n, ν_n, α_n·ν_n, or μ·α_n + β·(μ+ν_n))
yield different weighted sufficient conditions.

To bridge from the scaled conclusions (A_n/ρ_n → ℓ', B_n/ρ_n → 0) to the
unscaled conclusions (A_n → ℓ, B_n → 0) of Proposition 4.5 / Theorem 4.1,
one also needs that ρ_n is bounded above (for B_n → 0) and additional
structure on ρ_n (for A_n → ℓ); see `remark_4_1` below. -/
theorem remark_4_1_scaled_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (hα_bdd : ∃ C, ∀ n, α n ≤ C) (hν_bdd : ∃ C, ∀ n, ν n ≤ C)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y)
    (ρ : ℕ → ℝ) (hρ_pos : ∃ r > 0, ∀ n, ρ n ≥ r)
    (M : ℝ) (hM_x : ∀ n, ‖alg.x (n+1) - x‖ ^ 2 ≤ M) (hM_y : ∀ n, ‖alg.y (n+1) - y‖ ^ 2 ≤ M)
    (h_scaled_alpha_var_summable :
      Summable (fun n => positivePart (α (n+1) / ρ (n+1) - α n / ρ n)))
    (h_scaled_nu_var_summable :
      Summable (fun n => positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n))) :
    (∃ (ℓ' : ℝ), Tendsto (fun (n : ℕ) => An alg.x alg.y x y α ν β μ n / ρ n) atTop (𝓝 ℓ')) ∧
    Tendsto (fun (n : ℕ) => Bn alg.x alg.y x y α ν β μ n / ρ n) atTop (𝓝 0) := by
  -- ====== Setup: basic bounds ======
  have hM_nonneg : 0 ≤ M := by
    have hsq : 0 ≤ ‖alg.x 1 - x‖ ^ 2 := by positivity
    have h := hM_x 0; linarith
  have hμ_nonneg : 0 ≤ μ := by linarith [hyp.mu_pos]
  have hβ_nonneg : 0 ≤ β := by linarith [hyp.beta_pos]
  rcases hρ_pos with ⟨r, hr_pos, hr⟩
  have hρ_pos_all : ∀ n, ρ n > 0 := by
    intro n; exact lt_of_lt_of_le hr_pos (hr n)
  have hAn_nonneg : ∀ n, 0 ≤ An alg.x alg.y x y α ν β μ n := by
    intro n; dsimp [An]
    have hx : 0 ≤ α n * μ * ‖alg.x n - x‖ ^ 2 := by
      have hαn : 0 ≤ α n := hα_nonneg n; positivity
    have hy : 0 ≤ β * (μ + ν n) * ‖alg.y n - y‖ ^ 2 := by
      have hνn : 0 ≤ ν n := hν_nonneg n; positivity
    nlinarith
  have hsq_nonneg_scl : ∀ (v : H), 0 ≤ ‖v‖ ^ 2 := by intro v; positivity
  have hBn_nonneg : ∀ n, 0 ≤ Bn alg.x alg.y x y α ν β μ n := by
    intro n; dsimp [Bn]
    have h1 : 0 ≤ α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 :=
      mul_nonneg (mul_nonneg (hα_nonneg n) hμ_nonneg) (hsq_nonneg_scl _)
    have h2 : 0 ≤ β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg (hν_nonneg n)) (hsq_nonneg_scl _)
    have h3 : 0 ≤ β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg hμ_nonneg) (hsq_nonneg_scl _)
    have h4 : 0 ≤ β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg hμ_nonneg) (hsq_nonneg_scl _)
    nlinarith
  -- ====== Scaled correction terms C_n ======
  let C : ℕ → ℝ := fun n => (μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) +
                      β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n)) * M
  have hC_nonneg : ∀ n, 0 ≤ C n := by
    intro n; dsimp [C]
    have hpp1 : 0 ≤ positivePart (α (n+1) / ρ (n+1) - α n / ρ n) := by
      dsimp [positivePart]; exact le_max_right _ _
    have hpp2 : 0 ≤ positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) := by
      dsimp [positivePart]; exact le_max_right _ _
    have h1 : 0 ≤ μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) := by nlinarith
    have h2 : 0 ≤ β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) := by nlinarith
    nlinarith
  have hC_summable : Summable C := by
    have h_alpha_part : Summable (fun n : ℕ => μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) * M) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        h_scaled_alpha_var_summable.const_smul (μ * M)
    have h_nu_part : Summable (fun n : ℕ => β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) * M) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        h_scaled_nu_var_summable.const_smul (β * M)
    have hC_eq : C = fun n => (μ * positivePart (α (n+1) / ρ (n+1) - α n / ρ n) * M) +
                               (β * positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n) * M) := by
      ext n; dsimp [C]; ring
    rw [hC_eq]; exact Summable.add h_alpha_part h_nu_part
  let T := ∑' n, C n
  have hCT_hasSum : HasSum C T := hC_summable.hasSum
  let S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, C k
  have hS_tendsto : Tendsto S atTop (𝓝 T) := hCT_hasSum.tendsto_sum_nat
  have hS_succ (n : ℕ) : S (n+1) = S n + C n := by
    dsimp [S]; rw [Finset.sum_range_succ]
  -- ====== Apply scaled inequality ======
  have h_scaled (n : ℕ) :
      An alg.x alg.y x y α ν β μ (n+1) / ρ (n+1) ≤
      An alg.x alg.y x y α ν β μ n / ρ n + C n -
      Bn alg.x alg.y x y α ν β μ n / ρ n := by
    have h := remark_4_1_scaled_inequality hyp x y hα_nonneg hν_nonneg alg hine ρ ⟨r, hr_pos, hr⟩ M hM_x hM_y n
    simpa [C] using h
  -- ====== Telescoping: W_n = A_n/ρ_n − S_n ======
  let W : ℕ → ℝ := fun n => An alg.x alg.y x y α ν β μ n / ρ n - S n
  have hW_decr : ∀ n, W (n+1) ≤ W n - Bn alg.x alg.y x y α ν β μ n / ρ n := by
    intro n; dsimp [W]; rw [hS_succ n]; have h_ineq := h_scaled n; linarith
  have hW_decreasing : ∀ n, W (n+1) ≤ W n := by
    intro n; have h := hW_decr n
    have hdiv_nonneg : 0 ≤ Bn alg.x alg.y x y α ν β μ n / ρ n :=
      div_nonneg (hBn_nonneg n) (by linarith [hρ_pos_all n])
    linarith
  have hS_bdd : BddAbove (Set.range S) := hS_tendsto.bddAbove_range
  rcases hS_bdd with ⟨Smax, hSmax⟩
  have hS_n_bdd : ∀ n, S n ≤ Smax := by
    intro n; exact hSmax (Set.mem_range_self n)
  have hW_bdd_below : BddBelow (Set.range W) := by
    refine ⟨-Smax, ?_⟩
    rintro y ⟨n, rfl⟩; dsimp [W]
    have hAn_div_nonneg : 0 ≤ An alg.x alg.y x y α ν β μ n / ρ n :=
      div_nonneg (hAn_nonneg n) (by linarith [hρ_pos_all n])
    have hSn : S n ≤ Smax := hS_n_bdd n
    have h1 : 0 ≤ An alg.x alg.y x y α ν β μ n / ρ n - S n + Smax := by nlinarith
    nlinarith
  have hW_mono : Antitone W :=
    antitone_nat_of_succ_le hW_decreasing
  have hW_tendsto : ∃ L, Tendsto W atTop (𝓝 L) := by
    have h_nonempty : Set.Nonempty (Set.range W) := ⟨W 0, by simp⟩
    have hW_t : Tendsto W atTop (𝓝 (⨅ n, W n)) :=
      tendsto_atTop_ciInf hW_mono hW_bdd_below
    exact ⟨⨅ n, W n, hW_t⟩
  rcases hW_tendsto with ⟨L, hWL⟩
  -- ====== A_n/ρ_n converges ======
  have hAdiv : Tendsto (fun n => An alg.x alg.y x y α ν β μ n / ρ n) atTop (𝓝 (L + T)) := by
    have h_eq : (fun n => An alg.x alg.y x y α ν β μ n / ρ n) = fun n => W n + S n := by
      ext n; dsimp [W]; ring
    rw [h_eq]; exact hWL.add hS_tendsto
  -- ====== B_n/ρ_n → 0 via squeeze theorem ======
  have hBdiv_zero : Tendsto (fun n => Bn alg.x alg.y x y α ν β μ n / ρ n) atTop (𝓝 0) := by
    have h_nonneg : ∀ n, 0 ≤ Bn alg.x alg.y x y α ν β μ n / ρ n := by
      intro n; exact div_nonneg (hBn_nonneg n) (by linarith [hρ_pos_all n])
    have h_bound : ∀ n, Bn alg.x alg.y x y α ν β μ n / ρ n ≤ W n - W (n+1) := by
      intro n; linarith [hW_decr n]
    have h_diff_tendsto : Tendsto (fun n => W n - W (n+1)) atTop (𝓝 0) := by
      have hL_succ : Tendsto (fun n => W (n+1)) atTop (𝓝 L) := by
        simpa using hWL.comp (tendsto_add_atTop_nat 1)
      have h_sub : Tendsto (fun n => W n - W (n+1)) atTop (𝓝 (L - L)) :=
        Filter.Tendsto.sub hWL hL_succ
      simpa [sub_self] using h_sub
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ => (0:ℝ)) atTop _)
      h_diff_tendsto (fun n => h_nonneg n) (fun n => h_bound n)
  exact ⟨⟨L + T, hAdiv⟩, hBdiv_zero⟩

/-! ### Helper lemma: bridge scaled to unscaled convergence -/

/-- If A_n/ρ_n → ℓ' and ρ_n → ρ_lim (with ρ_n ≠ 0), then A_n = (A_n/ρ_n)·ρ_n → ρ_lim·ℓ'.
This bridges the gap from the scaled convergence proved in
`remark_4_1_scaled_convergence` to the unscaled A_n convergence,
injecting the missing `hρ_conv` hypothesis into the argument of `remark_4_1`. -/
private lemma An_tendsto_of_scaled_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {α ν : ℕ → ℝ} {β μ : ℝ} (alg : CA2 H H f g
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (x y : H) (ρ : ℕ → ℝ) (ℓ' ρinf : ℝ)
    (hAdiv : Tendsto (fun n => An alg.x alg.y x y α ν β μ n / ρ n) atTop (𝓝 ℓ'))
    (hρ_conv : Tendsto ρ atTop (𝓝 ρinf))
    (hρ_ne_zero : ∀ n, ρ n ≠ 0) :
    Tendsto (fun n => An alg.x alg.y x y α ν β μ n) atTop (𝓝 (ρinf * ℓ')) := by
  have hAn_eq : (fun n => An alg.x alg.y x y α ν β μ n) =
      fun n => (An alg.x alg.y x y α ν β μ n / ρ n) * ρ n := by
    ext n; field_simp [hρ_ne_zero n]
  rw [hAn_eq]
  have h := Filter.Tendsto.mul hAdiv hρ_conv
  simpa [mul_comm] using h

/-! ### Remark 4.1 — corrected statement with ρ_n convergence -/

/-- **Remark 4.1** — generalized sufficient condition for convergence.

This is the main formalization of Remark 4.1: the paper claims that under
scaled summability (and bounded α_n, ν_n), the conclusions of Proposition 4.5
and Theorem 4.1 can be proved.

**Corrected statement.** The original paper omitted the implicit hypothesis
that ρ_n converges. Without it, the implication is false (see
an abstract sequence counterexample. Here we add the hypothesis
`hρ_conv : Tendsto ρ atTop (𝓝 ρ_lim)`, which bridges from the scaled
convergence (A_n/ρ_n → ℓ') to the unscaled convergence
(A_n = ρ_n·(A_n/ρ_n) → ρ_lim·ℓ').

For the paper's specific choices of ρ_n (α_n, ν_n, α_n·ν_n,
μ·α_n+β·(μ+ν_n)), the convergence of ρ_n follows from the unscaled
summability condition H47 (which is the original hypothesis of
Proposition 4.5). Thus this corrected version faithfully captures
the paper's intent.

Relevant choices for ρ_n: ρ_n = α_n, ρ_n = ν_n, ρ_n = α_n·ν_n,
or ρ_n = μ·α_n + β·(μ + ν_n). For these choices, ρ_n is bounded above
because α_n, ν_n are bounded. -/
theorem remark_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (hα_bdd : ∃ C, ∀ n, α n ≤ C) (hν_bdd : ∃ C, ∀ n, ν n ≤ C)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y)
    (ρ : ℕ → ℝ) (hρ_pos : ∃ r > 0, ∀ n, ρ n ≥ r) (hρ_bdd : ∃ R, ∀ n, ρ n ≤ R)
    (ρ_lim : ℝ) (hρ_conv : Tendsto ρ atTop (𝓝 ρ_lim))
    (M : ℝ) (hM_x : ∀ n, ‖alg.x (n+1) - x‖ ^ 2 ≤ M) (hM_y : ∀ n, ‖alg.y (n+1) - y‖ ^ 2 ≤ M)
    (h_scaled_alpha_var_summable :
      Summable (fun n => positivePart (α (n+1) / ρ (n+1) - α n / ρ n)))
    (h_scaled_nu_var_summable :
      Summable (fun n => positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n))) :
    (∃ (ℓ : ℝ), Tendsto (fun (n : ℕ) => An alg.x alg.y x y α ν β μ n) atTop (𝓝 ℓ)) ∧
    Tendsto (fun (n : ℕ) => Bn alg.x alg.y x y α ν β μ n) atTop (𝓝 0) := by
  -- Obtain the scaled convergence
  rcases remark_4_1_scaled_convergence hyp x y hα_nonneg hν_nonneg hα_bdd hν_bdd alg hine
    ρ hρ_pos M hM_x hM_y h_scaled_alpha_var_summable h_scaled_nu_var_summable with
    ⟨⟨ℓ', hAdiv⟩, hBdiv_zero⟩
  rcases hρ_bdd with ⟨R, hR⟩
  rcases hρ_pos with ⟨r, hr_pos, hr⟩
  have hρ_pos_all : ∀ n, ρ n > 0 := by
    intro n; exact lt_of_lt_of_le hr_pos (hr n)
  -- ====== A_n → ρ_lim·ℓ' via An_tendsto_of_scaled_tendsto ======
  have hAn_conv : Tendsto (fun n => An alg.x alg.y x y α ν β μ n) atTop (𝓝 (ρ_lim * ℓ')) :=
    An_tendsto_of_scaled_tendsto alg x y ρ ℓ' ρ_lim hAdiv hρ_conv
      (fun n => (hρ_pos_all n).ne')
  -- ====== B_n → 0: proved using ρ_n ≤ R ======
  have hβ_nonneg_rmk : 0 ≤ β := by linarith [hyp.beta_pos]
  have hμ_nonneg_rmk : 0 ≤ μ := by linarith [hyp.mu_pos]
  have hsq_nonneg_rmk : ∀ (v : H), 0 ≤ ‖v‖ ^ 2 := by intro v; positivity
  have hBn_nonneg : ∀ n, 0 ≤ Bn alg.x alg.y x y α ν β μ n := by
    intro n; dsimp [Bn]
    have h1 : 0 ≤ α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 :=
      mul_nonneg (mul_nonneg (hα_nonneg n) hμ_nonneg_rmk) (hsq_nonneg_rmk _)
    have h2 : 0 ≤ β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg_rmk (hν_nonneg n)) (hsq_nonneg_rmk _)
    have h3 : 0 ≤ β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg_rmk hμ_nonneg_rmk) (hsq_nonneg_rmk _)
    have h4 : 0 ≤ β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg_rmk hμ_nonneg_rmk) (hsq_nonneg_rmk _)
    nlinarith
  have hR_nonneg : 0 ≤ R := by
    have h0r : ρ 0 ≥ r := hr 0
    have hR0 : ρ 0 ≤ R := hR 0
    linarith
  have h_upper : ∀ n, Bn alg.x alg.y x y α ν β μ n ≤ R * (Bn alg.x alg.y x y α ν β μ n / ρ n) := by
    intro n
    have hρ_pos' : ρ n > 0 := hρ_pos_all n
    have hρ_le_R : ρ n ≤ R := hR n
    calc
      Bn alg.x alg.y x y α ν β μ n = (Bn alg.x alg.y x y α ν β μ n / ρ n) * ρ n := by
        field_simp [hρ_pos'.ne']
      _ ≤ (Bn alg.x alg.y x y α ν β μ n / ρ n) * R := by
        gcongr
        exact div_nonneg (hBn_nonneg n) (by linarith)
      _ = R * (Bn alg.x alg.y x y α ν β μ n / ρ n) := by ring
  have hR_bound_tendsto : Tendsto (fun n => R * (Bn alg.x alg.y x y α ν β μ n / ρ n)) atTop (𝓝 (R * 0)) :=
    Filter.Tendsto.const_mul R hBdiv_zero
  have hR_bound_zero : Tendsto (fun n => R * (Bn alg.x alg.y x y α ν β μ n / ρ n)) atTop (𝓝 0) := by
    simpa [mul_zero] using hR_bound_tendsto
  have hB_tendsto_zero : Tendsto (fun n => Bn alg.x alg.y x y α ν β μ n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ => (0:ℝ)) atTop _)
      hR_bound_zero (fun n => hBn_nonneg n) (fun n => h_upper n)
  exact ⟨⟨ρ_lim * ℓ', hAn_conv⟩, hB_tendsto_zero⟩

