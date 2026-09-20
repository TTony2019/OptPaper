import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1

open Filter
open scoped Topology

namespace BotCsetnek2015

open ERealFunction

/-- Distance from a point to a set, the paper notation `dist(x, A)`. -/
noncomputable def distToSet {m : ℕ} (x : EuclideanSpace m) (A : Set (EuclideanSpace m)) :
    ℝ :=
  Metric.infDist x A

/--
The class `Theta_eta` of desingularizing functions.  This finite-`eta`
formalization records the conditions used later in the paper: concavity,
continuity, value zero at zero, differentiability on `(0, eta)`, and
strictly positive derivative there.
-/
def DesingularizingFunction (eta : ℝ) (phi : ℝ → ℝ) : Prop :=
  0 < eta ∧
    ConcaveOn ℝ (Set.Icc 0 eta) phi ∧
    ContinuousOn phi (Set.Icc 0 eta) ∧
    DifferentiableOn ℝ phi (Set.Ioo 0 eta) ∧
    phi 0 = 0 ∧
    (∀ s ∈ Set.Ioo 0 eta, 0 < deriv phi s)

/-- The Kurdyka-Lojasiewicz property at a limiting-subdifferential domain point. -/
noncomputable def KLPropertyAt {m : ℕ} (f : EuclideanSpace m → EReal)
    (xbar : EuclideanSpace m) : Prop :=
  xbar ∈ limitingSubdifferentialDomain f ∧
    ∃ eta : ℝ, ∃ U : Set (EuclideanSpace m), ∃ phi : ℝ → ℝ,
      0 < eta ∧ U ∈ nhds xbar ∧ DesingularizingFunction eta phi ∧
        ∀ x ∈ U,
          f xbar < f x →
          f x < erealAddReal (f xbar) eta →
          1 ≤ deriv phi ((f x).toReal - (f xbar).toReal) *
            distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x)

/-- A KL function satisfies the KL property at every point in `dom partial f`. -/
noncomputable def KLFunction {m : ℕ} (f : EuclideanSpace m → EReal) : Prop :=
  ∀ x ∈ limitingSubdifferentialDomain f, KLPropertyAt f x

end BotCsetnek2015
