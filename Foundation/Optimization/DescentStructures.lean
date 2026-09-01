import Mathlib
import Foundation.Convex.Subdifferential
import Foundation.SetValued.Basic
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Descent structures for continuous optimization dynamics

Structural hypotheses used in the convergence analysis of continuous-time
optimization dynamics: damping potentials for second-order inertial systems,
quasi-gradient structures, and the Kurdyka--Łojasiewicz property in its
chain-rule form.  These are reusable mathematical conditions, independent of
any particular algorithm or paper.

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (def_1, def_3,
ext_def_3).
-/

open ERealFunction

/-- The paper's damping-potential conditions, including bounded minimal subgradients on balls. -/
def IsDampingPotential {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → ℝ) : Prop :=
  Continuous φ ∧ ConvexOn ℝ Set.univ φ ∧ (∀ u, 0 ≤ φ u) ∧ φ 0 = 0 ∧
  ∀ R : ℝ, 0 < R → ∃ M : ℝ, ∀ u, ‖u‖ ≤ R →
    ∃ v ∈ subdifferential (fun x => (φ x : EReal)) u,
      (∀ w ∈ subdifferential (fun x => (φ x : EReal)) u, ‖v‖ ≤ ‖w‖) ∧ ‖v‖ ≤ M

/-- A quasi-gradient structure: the angle condition and equivalence of critical and rest points. -/
def HasQuasiGradientStructure {n : Type*} [NormedAddCommGroup n] [InnerProductSpace ℝ n]
    (E : n → ℝ) (gradE F : n → n) (Γ : Set n) (α : ℝ) : Prop :=
  Γ.Nonempty ∧ IsClosed Γ ∧
  (∀ z u, HasDerivAt (fun s : ℝ ↦ E (z + s • u)) (inner ℝ (gradE z) u) 0) ∧
  (∀ z, ∃ U ∈ nhds z, ∃ K, LipschitzOnWith K F U) ∧ 0 < α ∧
  (∀ z ∈ Γ, α * ‖gradE z‖ * ‖F z‖ ≤ inner ℝ (gradE z) (F z)) ∧
    (∀ z ∈ Γ, gradE z = 0 ↔ F z = 0)

/-- The KL property in its chain-rule form around every critical point. -/
def HasKurdykaLojasiewiczProperty {n : Type*} [NormedAddCommGroup n] [InnerProductSpace ℝ n]
    (G : n → ℝ) (gradG : n → n) : Prop :=
  Differentiable ℝ G ∧ ∀ x, gradG x = 0 → ∃ U ∈ nhds x, ∃ η : ℝ, 0 < η ∧ ∃ θ : ℝ → ℝ,
    Continuous θ ∧ ConcaveOn ℝ (Set.Icc 0 η) θ ∧ StrictMonoOn θ (Set.Icc 0 η) ∧ θ 0 = 0 ∧
    (∀ u q, HasDerivAt (fun s : ℝ ↦ G (u + s • q)) (inner ℝ (gradG u) q) 0) ∧
    ∀ u ∈ U, G x < G u → G u < G x + η → 1 ≤ |deriv θ (G u)| * ‖gradG u‖

/-! Source items:
`TheoremLib/Attouch_Adly_Le_Threshold_dry_friction_2023/items/ext_def_4`
(value-drop KL form) and `TheoremLib/Attouch_Adly_Le_Threshold_dry_friction_2023/items/ext_def_5`
(critical points). -/

/-- The Kurdyka--Łojasiewicz property in its value-drop form: a differentiable
`f : H → ℝ` has the (KL) property if near every critical point `x̄` there exist
`η > 0`, a neighborhood `U` of `x̄`, and a desingularizing function `θ` which is
continuous, concave, increasing and `C¹` on `[0,η)` (with `θ(0) = 0`) such that
`θ'(f(x)-f(x̄)) ‖∇f(x)‖ ≥ 1` for `x ∈ U` with `f(x̄) < f(x) < f(x̄)+η`.

Distinct from `HasKurdykaLojasiewiczProperty` (the chain-rule form) above; the
two forms are related but not definitionally equal. -/
def HasKLProperty {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (f : H → ℝ) (grad : H → H) : Prop :=
  Differentiable ℝ f ∧ (∀ x v, fderiv ℝ f x v = inner ℝ (grad x) v) ∧
  ∀ xbar : H, grad xbar = 0 → ∃ η : ℝ, 0 < η ∧ ∃ U : Set H,
    U ∈ nhds xbar ∧ ∃ θ : ℝ → ℝ,
      ContinuousOn θ (Set.Ico (0 : ℝ) η) ∧ ConcaveOn ℝ (Set.Ico (0 : ℝ) η) θ ∧
      MonotoneOn θ (Set.Ico (0 : ℝ) η) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) η, 0 ≤ θ t) ∧ θ 0 = 0 ∧
      ∃ θ' : ℝ → ℝ, (∀ t : Set.Ico (0 : ℝ) η, θ' t = θ t) ∧
      ContDiffOn ℝ 1 θ' (Set.Ioo 0 η) ∧
      ∀ x ∈ U, f xbar < f x → f x < f xbar + η →
        deriv θ' (f x - f xbar) * ‖grad x‖ ≥ 1

/-- A differentiable critical point has zero gradient. -/
def IsCriticalPoint {H : Type*} [Zero H] (grad : H → H) (x : H) : Prop := grad x = 0

/-- Toland criticality: the two convex subdifferentials have a common value. -/
def IsTolandCritical {H V : Type*} [Zero V] (subgradG subgradH : H → Set V) (u : H) : Prop :=
  ∃ v, v ∈ subgradG u ∧ v ∈ subgradH u
