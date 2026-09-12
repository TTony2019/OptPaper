import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.def_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_2
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_3
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_4
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_thm_3

open scoped InnerProductSpace

open ERealFunction

namespace Nesterov1983

/-- `v` is the attained minimum `Ψ(λ) = min_{x ∈ Q} ⟪λ, fbar x⟫`. -/
def IsDualValue {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExtremalProblem m E) (l : EuclideanSpace ℝ (Fin m)) (v : ℝ) : Prop :=
  ∃ x ∈ P.Q, v = inner ℝ l (WithLp.toLp 2 (fun i => P.f i x)) ∧
    ∀ z ∈ P.Q, v ≤ inner ℝ l (WithLp.toLp 2 (fun i => P.f i z))

/-- The effective domain of the minimum-value function `Ψ`. -/
def dualDomain {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExtremalProblem m E) : Set (EuclideanSpace ℝ (Fin m)) :=
  {l | ∃ v, IsDualValue P l v}

/-- A multiplier is dual-optimal when it maximizes the dual value over `∂F(0)`. -/
def IsDualOptimal {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExtremalProblem m E) (l : EuclideanSpace ℝ (Fin m)) : Prop :=
  l ∈ subdifferential (fun y => (P.F y : EReal)) 0 ∩ dualDomain P ∧
    ∃ v, IsDualValue P l v ∧ ∀ q ∈ subdifferential (fun y => (P.F y : EReal)) 0 ∩ dualDomain P,
      ∀ w, IsDualValue P q w → w ≤ v

/-- The dual maximization problem `max { Ψ(λ) | λ ∈ ∂F(0) ∩ dom Ψ }`. -/
def dualProblem {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExtremalProblem m E) : Set (EuclideanSpace ℝ (Fin m)) :=
  {l | IsDualOptimal P l}

end Nesterov1983
