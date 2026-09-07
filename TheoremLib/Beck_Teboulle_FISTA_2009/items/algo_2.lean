import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Minimal
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7

open Set
open scoped RealInnerProductSpace

/-- A backtracking trial is accepted when it satisfies the paper's majorization
test `F(p_L(y)) ≤ Q_L(p_L(y), y)`.  The fact that the trial is the proximal
point is recorded separately by `trial_is_proximal`, just as `p_L(y)` is
defined separately from the test in (3.2). -/
def BacktrackingAccepted {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  compositeObjective f g z ≤ quadraticApprox f g L z y

/-- The constants used in Remark 3.2: `β = L₀ / L(f)` and `α = η` for backtracking. -/
noncomputable def backtrackingBeta (Lf L0 : ℝ) : ℝ := L0 / Lf

def backtrackingAlpha (eta : ℝ) : ℝ := eta

/-- The two-sided stepsize estimate (3.4) used in Theorems 3.1 and 4.1.
For the backtracking rule, the paper sets `β = L₀ / L(f)` and `α = η`.
The lower bound follows from the recurrence.  The upper bound is exposed as an
explicit hypothesis because `L₀ > 0` alone does not imply it when `L₀ > L(f)`. -/
def BacktrackingStepsizeBounds (Lf L0 eta : ℝ) (L : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    backtrackingBeta Lf L0 * Lf ≤ L k ∧ L k ≤ backtrackingAlpha eta * Lf

/-- FISTA with backtracking, as stated after equations (4.1)--(4.3).

For iteration `k ≥ 1`, `trial k j` denotes `p_{η^j L_{k-1}}(y_k)`.  The `IsLeast`
field records literally that `i k` is the smallest nonnegative integer whose trial satisfies
the majorization test.  Since `i k : ℕ`, nonnegativity is represented by its type.  The
estimate (3.4) is an analytical invariant of an accepted run and is supplied separately to
the rate theorems; it is not an input to the backtracking algorithm. -/
structure FISTABacktracking {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) where
  L0 : ℝ
  eta : ℝ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  y : ℕ → EuclideanSpace ℝ (Fin n)
  t : ℕ → ℝ
  L : ℕ → ℝ
  i : ℕ → ℕ
  trial : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  L0_pos : 0 < L0
  eta_gt_one : 1 < eta
  L_zero : L 0 = L0
  x_zero : x 0 = x0
  y_one : y 1 = x0
  t_one : t 1 = 1
  trial_is_proximal : ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ,
    IsProxPoint f g (eta ^ j * L (k - 1)) (y k) (trial k j)
  exponent_is_least : ∀ k : ℕ, 1 ≤ k →
    IsLeast
      {j : ℕ | BacktrackingAccepted f g (eta ^ j * L (k - 1))
        (y k) (trial k j)}
      (i k)
  stepsize_update : ∀ k : ℕ, 1 ≤ k → L k = eta ^ (i k) * L (k - 1)
  x_update : ∀ k : ℕ, 1 ≤ k → x k = trial k (i k)
  t_update : ∀ k : ℕ, 1 ≤ k →
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ 2)) / 2
  y_update : ∀ k : ℕ, 1 ≤ k →
    y (k + 1) = x k + ((t k - 1) / t (k + 1)) • (x k - x (k - 1))

namespace FISTABacktracking

theorem stepsize_pos {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0) :
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
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) : A.L (k - 1) ≤ A.L k := by
  rw [A.stepsize_update k hk]
  have hpow : 1 ≤ A.eta ^ A.i k := one_le_pow₀ (le_of_lt A.eta_gt_one)
  have hprev : 0 ≤ A.L (k - 1) := le_of_lt (A.stepsize_pos (k - 1))
  calc
    A.L (k - 1) = 1 * A.L (k - 1) := by ring
    _ ≤ (A.eta ^ A.i k) * A.L (k - 1) :=
      mul_le_mul_of_nonneg_right hpow hprev

theorem trial_stepsize_pos {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k j : ℕ) (_hk : 1 ≤ k) : 0 < A.eta ^ j * A.L (k - 1) := by
  have heta : 0 < A.eta := by linarith [A.eta_gt_one]
  exact mul_pos (pow_pos heta _) (A.stepsize_pos (k - 1))

theorem exponent_nonnegative {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) : 0 ≤ A.i k := Nat.zero_le _

theorem selected_trial_accepted {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    BacktrackingAccepted f g (A.eta ^ (A.i k) * A.L (k - 1))
      (A.y k) (A.trial k (A.i k)) := by
  exact (A.exponent_is_least k hk).1

theorem selected_exponent_is_smallest {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ j : ℕ, j < A.i k →
      ¬ BacktrackingAccepted f g (A.eta ^ j * A.L (k - 1))
        (A.y k) (A.trial k j) := by
  intro j hj haccepted
  have hle : A.i k ≤ j := (A.exponent_is_least k hk).2 haccepted
  omega

theorem lower_bound {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0) :
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
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (hLf : 0 < Lf) : 0 < backtrackingBeta Lf A.L0 := by
  unfold backtrackingBeta
  exact div_pos A.L0_pos hLf

theorem beta_lower_bound {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
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
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (hLf : 0 < Lf)
    (h_upper : ∀ k : ℕ, 1 ≤ k → A.L k ≤ A.eta * Lf) :
    BacktrackingStepsizeBounds Lf A.L0 A.eta A.L := by
  intro k hk
  exact ⟨A.beta_lower_bound hLf k hk, by simpa [backtrackingAlpha] using h_upper k hk⟩

theorem proximal_step {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) : IsProxPoint f g (A.L k) (A.y k) (A.x k) := by
  rw [A.stepsize_update k hk, A.x_update k hk]
  exact A.trial_is_proximal k hk (A.i k)

theorem descent_condition {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) ≤ quadraticApprox f g (A.L k) (A.x k) (A.y k) := by
  have haccepted := (A.exponent_is_least k hk).1
  rw [A.stepsize_update k hk, A.x_update k hk]
  exact haccepted

end FISTABacktracking
