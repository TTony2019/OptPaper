import Mathlib

/-!
# ε-argmin (ε-Approximate Minimizer)

For a function φ : X → ℝ ∪ {+∞} and ε > 0, the set of ε-approximate minimizers is

    ε-argmin_{ξ∈X} φ(ξ) = {x ∈ X : φ(x) ≤ inf_X φ + ε}.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set

/-- The set of ε-approximate minimizers of a function φ : X → ℝ ∪ {+∞}.
    For ε > 0, an element x ∈ X is in ε-argmin φ if and only if
    φ(x) ≤ inf φ + ε. -/
def epsArgmin {X : Type*} (φ : X → EReal) (ε : ℝ) (hε : ε > 0) : Set X :=
  {x | φ x ≤ (⨅ ξ, φ ξ) + (ε : EReal)}
