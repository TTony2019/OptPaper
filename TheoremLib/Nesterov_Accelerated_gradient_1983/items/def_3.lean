import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.def_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_3

open scoped InnerProductSpace

namespace Nesterov1983

/-- The vector-valued map `f̄(x) = (f₁(x), …, f_m(x))` of problem (8). -/
def fbar {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExtremalProblem m E) (x : E) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => P.f i x)

/-- The componentwise affine model at `y` used by method (11)-(13). -/
noncomputable def linearizedComponents {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : ExtremalProblem m E) (y z : E) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => P.f i y + inner ℝ (gradient (P.f i) y) (z - y))

/-- The auxiliary objective `Φ(y,A,z)`. -/
noncomputable def auxiliaryFunction {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : ExtremalProblem m E) (y : E) (A : ℝ) (z : E) : ℝ :=
  P.F (linearizedComponents P y z) + (A / 2) * ‖y - z‖ ^ 2

/-- The minimum value `Φ*(y,A)` of the auxiliary problem over `Q`. -/
noncomputable def auxiliaryValue {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : ExtremalProblem m E) (y : E) (A : ℝ) : ℝ :=
  sInf (auxiliaryFunction P y A '' P.Q)

/-- The argmin-valued map `T(y,A)` of the auxiliary problem. -/
noncomputable def auxiliaryMinimizers {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : ExtremalProblem m E) (y : E) (A : ℝ) : Set E :=
  Optimization.argminOn P.Q (auxiliaryFunction P y A)

/-- The two estimates (10) and the post-model inequality required of `T(y,A)`. -/
def HasAuxiliaryMappingEstimates {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : ExtremalProblem m E) (T : E → ℝ → E) : Prop :=
  (∀ y A, T y A ∈ auxiliaryMinimizers P y A) ∧
  (∀ x ∈ P.Q, ∀ y A, 0 ≤ A →
    auxiliaryValue P y A + A * inner ℝ (y - T y A) (x - y) +
      (A / 2) * ‖y - T y A‖ ^ 2 ≤ P.F (WithLp.toLp 2 (fun i => P.f i x)))

/-- The final auxiliary-value inequality, valid when `A ≥ F(Lbar)`. -/
def HasAuxiliaryValueLowerBound {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : ExtremalProblem m E) (T : E → ℝ → E)
    (Lbar : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ y A, P.F Lbar ≤ A →
    P.F (WithLp.toLp 2 (fun i => P.f i (T y A))) ≤ auxiliaryValue P y A

end Nesterov1983
