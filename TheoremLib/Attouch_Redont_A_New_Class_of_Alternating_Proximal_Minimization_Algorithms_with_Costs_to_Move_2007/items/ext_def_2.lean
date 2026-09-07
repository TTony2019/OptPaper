import Mathlib

/-!
# Firmly Nonexpansive Operator

An operator T : H → H on a Hilbert space H is firmly nonexpansive if
⟨T x - T x', x - x'⟩ ≥ ‖T x - T x'‖² for all x, x' ∈ H.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Real

/-- An operator T : H → H on a real Hilbert space is firmly nonexpansive if
‖T x - T y‖² ≤ ⟨T x - T y, x - y⟩ for all x, y ∈ H.
This is the standard definition used in the paper (equation at start of Section 1). -/
def IsFirmlyNonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)

/-- An operator restricted to a subset D is firmly nonexpansive on D. -/
def IsFirmlyNonexpansiveOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D : Set H) (T : H → H) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)

/-- Equivalent characterization: T is firmly nonexpansive iff T is the average of the
identity and a nonexpansive operator N, i.e. T = (I + N)/2 where ‖N x - N y‖ ≤ ‖x - y‖. -/
lemma firmly_nonexpansive_iff_averaged {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) : IsFirmlyNonexpansive T ↔
    ∃ (N : H → H), (∀ x y : H, ‖N x - N y‖ ≤ ‖x - y‖) ∧ (∀ x : H, T x = (1/2 : ℝ) • (x + N x)) := by
  constructor
  · intro hT
    -- Define N = 2T - I (the "reflection" of T)
    let N : H → H := λ x => (2 : ℝ) • T x - x
    refine ⟨N, ?_, ?_⟩
    · -- N is nonexpansive: ‖N x - N y‖ ≤ ‖x - y‖
      intro x y
      have h := hT x y
      -- h : ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)
      have h_diff : N x - N y = (2 : ℝ) • (T x - T y) - (x - y) := by
        dsimp [N]
        rw [smul_sub (2 : ℝ) (T x) (T y)]
        abel
      rw [h_diff]
      set a := T x - T y
      set b := x - y
      -- Prove: ‖2a - b‖² ≤ ‖b‖² via the identity ‖2a-b‖² = 4‖a‖² - 4⟨a,b⟩ + ‖b‖²
      have h_sq : ‖(2 : ℝ) • a - b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
        have h_eq : ‖(2 : ℝ) • a - b‖ ^ 2 - ‖b‖ ^ 2 = 4 * (‖a‖ ^ 2 - inner ℝ a b) := by
          rw [norm_sub_sq (𝕜 := ℝ) ((2 : ℝ) • a) b]
          simp
          -- Goal: (‖2a‖² - 2*inner(2a,b) + ‖b‖²) - ‖b‖² = 4*(‖a‖² - inner a b)
          have h_inner : inner ℝ ((2 : ℝ) • a) b = (2 : ℝ) * inner ℝ a b := by
            rw [inner_smul_left (x := a) (y := b) (r := (2 : ℝ))]
            simp
          rw [h_inner]
          have h_norm : ‖(2 : ℝ) • a‖ ^ 2 = 4 * ‖a‖ ^ 2 := by
            rw [norm_smul (r := (2 : ℝ)) (x := a)]
            norm_num
            ring
          rw [h_norm]
          ring
        have h_nonpos : ‖(2 : ℝ) • a - b‖ ^ 2 - ‖b‖ ^ 2 ≤ 0 := by
          rw [h_eq]
          nlinarith
        linarith
      have hpos1 : 0 ≤ ‖(2 : ℝ) • a - b‖ := norm_nonneg _
      have hpos2 : 0 ≤ ‖b‖ := norm_nonneg _
      nlinarith
    · -- T = (I + N)/2
      intro x
      dsimp [N]
      -- Goal: T x = (1/2) • (x + (2•Tx - x))
      -- Compute the RHS and show it equals T x
      have hcalc : (1/2 : ℝ) • (x + ((2 : ℝ) • T x - x)) = T x := by
        calc
          (1/2 : ℝ) • (x + ((2 : ℝ) • T x - x)) = (1/2 : ℝ) • (((2 : ℝ) • T x) + (x - x)) := by abel
          _ = (1/2 : ℝ) • ((2 : ℝ) • T x) := by simp
          _ = ((1/2 : ℝ) * (2 : ℝ)) • T x := by rw [mul_smul]
          _ = (1 : ℝ) • T x := by norm_num
          _ = T x := by simp
      exact hcalc.symm
  · intro ⟨N, hN_nonexp, hT⟩
    intro x y
    have hN := hN_nonexp x y
    -- hN : ‖N x - N y‖ ≤ ‖x - y‖
    have hTx_diff : T x - T y = (1/2 : ℝ) • ((x - y) + (N x - N y)) := by
      rw [hT x, hT y]
      rw [← smul_sub (1/2 : ℝ) (x + N x) (y + N y)]
      congr 1
      abel
    have h_key : inner ℝ (T x - T y) (x - y) - ‖T x - T y‖ ^ 2 =
        (1/4 : ℝ) * (‖x - y‖ ^ 2 - ‖N x - N y‖ ^ 2) := by
      rw [hTx_diff]
      set a := x - y
      set b := N x - N y
      -- Compute ⟨(1/2)(a+b), a⟩ and ‖(1/2)(a+b)‖²
      have h1 : inner ℝ ((1/2 : ℝ) • (a + b)) a = (1/2 : ℝ) * (‖a‖ ^ 2 + inner ℝ b a) := by
        rw [inner_smul_left (x := a + b) (y := a) (r := (1/2 : ℝ))]
        simp
        rw [inner_add_left, real_inner_self_eq_norm_sq]
      have h2 : ‖(1/2 : ℝ) • (a + b)‖ ^ 2 = (1/4 : ℝ) * (‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2) := by
        calc
          ‖(1/2 : ℝ) • (a + b)‖ ^ 2 = (‖(1/2 : ℝ)‖ * ‖a + b‖) ^ 2 := by
            rw [norm_smul (r := (1/2 : ℝ)) (x := a + b)]
          _ = ((1/2 : ℝ) * ‖a + b‖) ^ 2 := by norm_num
          _ = ((1/2 : ℝ) ^ 2) * ‖a + b‖ ^ 2 := by ring
          _ = (1/4 : ℝ) * ‖a + b‖ ^ 2 := by norm_num
          _ = (1/4 : ℝ) * (‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2) := by
            rw [norm_add_sq (𝕜 := ℝ) a b]; simp
      rw [h1, h2]
      -- Simplify: (1/2)(‖a‖²+⟨b,a⟩) - (1/4)(‖a‖²+2⟨a,b⟩+‖b‖²) = (1/4)(‖a‖²-‖b‖²)
      rw [real_inner_comm b a]
      ring
    have hN_sq : ‖N x - N y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hpos1 : 0 ≤ ‖N x - N y‖ := norm_nonneg _
      have hpos2 : 0 ≤ ‖x - y‖ := norm_nonneg _
      nlinarith
    have h_nonneg : 0 ≤ inner ℝ (T x - T y) (x - y) - ‖T x - T y‖ ^ 2 := by
      rw [h_key]
      nlinarith
    exact sub_nonneg.mp h_nonneg
