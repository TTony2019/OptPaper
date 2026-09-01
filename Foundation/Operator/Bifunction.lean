import Mathlib

/-!
# Operator Bifunction

Bifunction conditions, Ky Fan minimax inequality problem, Minty dual problem,
and the bifunction resolvent. These definitions are fundamental for equilibrium
problems, variational inequalities, and proximal algorithms.

## Main definitions

- `condition_C1`–`condition_C6`: the six standard regularity conditions on a
  bifunction `F : H → H → ℝ` over a set `C`:
  * C1: `F(x, x) = 0`
  * C2: convexity in the second argument
  * C3: lower semicontinuity in the second argument
  * C4: monotonicity
  * C5: upper hemicontinuity
  * C6: ρ-monotonicity (generalizing monotonicity)

- `KyFanProblem`, `solutionSetKF`: the Ky Fan minimax inequality problem and
  its solution set.
- `MintyProblem`: the Minty (dual) form of the Ky Fan inequality.
- `isStronglyMonotone`, `isWeaklyMonotone`: strong and weak monotonicity
  derived from ρ-monotonicity.
- `bifunctionResolvent`: the resolvent of a bifunction.

Source paper: Chbani & Riahi (2012), "Weak and strong convergence of an
inertial proximal method for solving Ky Fan minimax inequalities."
-/

open Set
open Filter
open scoped Topology

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Bifunction conditions (C1)–(C6) -/

/-- Condition (C1): `F(x, x) = 0` for each `x ∈ C`. -/
def condition_C1 (F : H → H → ℝ) (C : Set H) : Prop :=
  ∀ x ∈ C, F x x = 0

/-- Condition (C2): For each `x ∈ C`, the function `y ↦ F(x, y)` is convex on `C`. -/
def condition_C2 (F : H → H → ℝ) (C : Set H) : Prop :=
  ∀ x ∈ C, ConvexOn ℝ C (F x)

/-- Condition (C3): For each `x ∈ C`, the function `y ↦ F(x, y)` is lower
    semicontinuous on `C`. -/
def condition_C3 (F : H → H → ℝ) (C : Set H) : Prop :=
  ∀ x ∈ C, LowerSemicontinuousOn (F x) C

/-- Condition (C4): `F` is monotone, i.e.
    `F(x, y) + F(y, x) ≤ 0` for all `x, y ∈ C`. -/
def condition_C4 (F : H → H → ℝ) (C : Set H) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, F x y + F y x ≤ 0

/-- Condition (C5): `F` is upper-hemicontinuous, i.e. for any `x, y, z ∈ C`,
    `lim_{t ↓ 0} F((1 - t) x + t z, y) ≤ F(x, y)`. -/
def condition_C5 (F : H → H → ℝ) (C : Set H) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C,
    Filter.limsup (fun (t : ℝ) ↦ F ((1 - t) • x + t • z) y) (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) ≤ F x y

/-- Condition (C6): `F` is ρ-monotone for some `ρ ∈ ℝ`, i.e.
    `F(x, y) + F(y, x) ≤ -(ρ/2) ‖x - y‖²` for all `x, y ∈ C`. -/
def condition_C6 (F : H → H → ℝ) (C : Set H) (ρ : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, F x y + F y x ≤ -(ρ / 2) * ‖x - y‖ ^ 2

/-! ### Strong and weak monotonicity -/

/-- `F` is ρ-strongly monotone on `C` when `ρ > 0` and `F` satisfies `condition_C6` for `ρ`. -/
def isStronglyMonotone (F : H → H → ℝ) (C : Set H) (ρ : ℝ) : Prop :=
  ρ > 0 ∧ condition_C6 F C ρ

/-- When `ρ < 0`, `F` is ρ-weakly monotone: `F(x, y) + F(y, x) ≤ -(ρ/2)‖x - y‖²`
    with `ρ` negative (so the right-hand side is positive, giving a weaker condition
    than monotonicity). -/
def isWeaklyMonotone (F : H → H → ℝ) (C : Set H) (ρ : ℝ) : Prop :=
  ρ < 0 ∧ condition_C6 F C ρ

/-- ρ-strong monotonicity of `F` implies monotonicity of `F`. -/
lemma stronglyMonotone_implies_monotone (F : H → H → ℝ) (C : Set H) (ρ : ℝ)
    (h : isStronglyMonotone F C ρ) : condition_C4 F C := by
  rcases h with ⟨hρpos, hρmon⟩
  intro x hx y hy
  have hineq := hρmon x hx y hy
  have : -(ρ / 2) * ‖x - y‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖x - y‖]
  nlinarith

/-! ### Ky Fan minimax inequality problem -/

/-- The Ky Fan minimax inequality problem (KF):
    Find `x̄ ∈ C` such that `F(x̄, y) ≥ 0` for each `y ∈ C`. -/
def KyFanProblem (F : H → H → ℝ) (C : Set H) (x : H) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, F x y ≥ 0

/-- The solution set `S(KF)` of the Ky Fan minimax inequality problem. -/
def solutionSetKF (F : H → H → ℝ) (C : Set H) : Set H :=
  {x ∈ C | ∀ y ∈ C, F x y ≥ 0}

/-- The Minty form of the Ky Fan minimax inequality (KF'):
    Find `x̄ ∈ C` such that `F(y, x̄) ≤ 0` for each `y ∈ C`. -/
def MintyProblem (F : H → H → ℝ) (C : Set H) (x : H) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, F y x ≤ 0

/-! ### Bifunction resolvent -/

open scoped InnerProductSpace

/-- The resolvent `J_r^F` of a bifunction `F` at `x ∈ H` with parameter `r > 0`:
    the set of `z ∈ C` such that `r F(z, y) + ⟨y - z, z - x⟩ ≥ 0` for all `y ∈ C`.

    The paper defines `J_r^F(x)` as the *unique* element satisfying this condition;
    we represent it as a set because uniqueness requires assumptions (C1)–(C4)
    and maximality. Under those hypotheses, this set is a singleton. -/
def bifunctionResolvent (F : H → H → ℝ) (C : Set H) (r : ℝ) (x : H) : Set H :=
  {z | z ∈ C ∧ ∀ y ∈ C, r * F z y + Inner.inner ℝ (y - z) (z - x) ≥ 0}
