import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Minimal
import TheoremLib.Beck_Teboulle_FISTA_2009.items.algo_2

open Set

/-- ISTA with backtracking, equations (3.2)--(3.3).

At iteration `k ≥ 1`, `trial k j` is the proximal point obtained with the trial value
`η^j L_{k-1}`.  The chosen exponent is characterized by `IsLeast`, so this records both
acceptance and the paper's requirement to choose the smallest nonnegative integer `i_k`.
The estimate (3.4) is supplied separately to the rate theorem, since it is an analytical
invariant rather than an input to the backtracking algorithm. -/
structure ISTABacktracking {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) where
  L0 : ℝ
  eta : ℝ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  L : ℕ → ℝ
  i : ℕ → ℕ
  trial : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  L0_pos : 0 < L0
  eta_gt_one : 1 < eta
  L_zero : L 0 = L0
  x_zero : x 0 = x0
  trial_is_proximal : ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ,
    IsProxPoint f g (eta ^ j * L (k - 1)) (x (k - 1)) (trial k j)
  exponent_is_least : ∀ k : ℕ, 1 ≤ k →
    IsLeast
      {j : ℕ | BacktrackingAccepted f g (eta ^ j * L (k - 1))
        (x (k - 1)) (trial k j)}
      (i k)
  stepsize_update : ∀ k : ℕ, 1 ≤ k → L k = eta ^ (i k) * L (k - 1)
  x_update : ∀ k : ℕ, 1 ≤ k → x k = trial k (i k)

namespace ISTABacktracking

theorem stepsize_pos {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0) :
    ∀ k : ℕ, 0 < A.L k := by
  intro k
  induction k with
  | zero => simpa [A.L_zero] using A.L0_pos
  | succ k ih =>
      rw [A.stepsize_update (k + 1) (by omega)]
      have hprev : 0 < A.L ((k + 1) - 1) := by simpa using ih
      have heta : 0 < A.eta := by linarith [A.eta_gt_one]
      exact mul_pos (pow_pos heta _) hprev

theorem stepsize_non_decreasing {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) : A.L (k - 1) ≤ A.L k := by
  rw [A.stepsize_update k hk]
  have hpow : 1 ≤ A.eta ^ A.i k := one_le_pow₀ (le_of_lt A.eta_gt_one)
  have hprev : 0 ≤ A.L (k - 1) := le_of_lt (A.stepsize_pos (k - 1))
  calc
    A.L (k - 1) = 1 * A.L (k - 1) := by ring
    _ ≤ (A.eta ^ A.i k) * A.L (k - 1) :=
      mul_le_mul_of_nonneg_right hpow hprev

theorem trial_stepsize_pos {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k j : ℕ) (_hk : 1 ≤ k) : 0 < A.eta ^ j * A.L (k - 1) := by
  have heta : 0 < A.eta := by linarith [A.eta_gt_one]
  exact mul_pos (pow_pos heta _) (A.stepsize_pos (k - 1))

theorem exponent_nonnegative {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) : 0 ≤ A.i k := Nat.zero_le _

theorem selected_trial_accepted {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    BacktrackingAccepted f g (A.eta ^ (A.i k) * A.L (k - 1))
      (A.x (k - 1)) (A.trial k (A.i k)) := by
  exact (A.exponent_is_least k hk).1

theorem selected_exponent_is_smallest {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ j : ℕ, j < A.i k →
      ¬ BacktrackingAccepted f g (A.eta ^ j * A.L (k - 1))
        (A.x (k - 1)) (A.trial k j) := by
  intro j hj haccepted
  have hle : A.i k ≤ j := (A.exponent_is_least k hk).2 haccepted
  omega

theorem lower_bound {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0) :
    ∀ k : ℕ, A.L0 ≤ A.L k := by
  intro k
  induction k with
  | zero => simpa only [A.L_zero] using (le_refl A.L0)
  | succ k ih =>
      have hstep : A.L k ≤ A.L (k + 1) := by
        simpa only [Nat.add_sub_cancel] using
          A.stepsize_non_decreasing (k + 1) (by omega)
      exact le_trans ih hstep

theorem beta_pos {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (hLf : 0 < Lf) : 0 < backtrackingBeta Lf A.L0 := by
  unfold backtrackingBeta
  exact div_pos A.L0_pos hLf

theorem beta_lower_bound {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (hLf : 0 < Lf) :
    ∀ k : ℕ, 1 ≤ k → backtrackingBeta Lf A.L0 * Lf ≤ A.L k := by
  intro k hk
  have hLf_ne : Lf ≠ 0 := ne_of_gt hLf
  calc
    backtrackingBeta Lf A.L0 * Lf = A.L0 := by
      unfold backtrackingBeta
      exact div_mul_cancel₀ A.L0 hLf_ne
    _ ≤ A.L k := A.lower_bound k

theorem bounds_of_upper {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (hLf : 0 < Lf)
    (h_upper : ∀ k : ℕ, 1 ≤ k → A.L k ≤ A.eta * Lf) :
    BacktrackingStepsizeBounds Lf A.L0 A.eta A.L := by
  intro k hk
  exact ⟨A.beta_lower_bound hLf k hk, by simpa [backtrackingAlpha] using h_upper k hk⟩

theorem proximal_step {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) : IsProxPoint f g (A.L k) (A.x (k - 1)) (A.x k) := by
  rw [A.stepsize_update k hk, A.x_update k hk]
  exact A.trial_is_proximal k hk (A.i k)

theorem descent_condition {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) ≤
      quadraticApprox f g (A.L k) (A.x k) (A.x (k - 1)) := by
  have haccepted := (A.exponent_is_least k hk).1
  rw [A.stepsize_update k hk, A.x_update k hk]
  simpa [BacktrackingAccepted] using haccepted

end ISTABacktracking
