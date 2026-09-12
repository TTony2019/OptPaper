import Mathlib

/-!
# Support function of a convex set
For a subset $C \subset H$, the support function $\sigma_C: H \to \mathbb{R} \cup \{+\infty\}$
is defined by:
$$\sigma_C(x) = \sup_{z \in C} \langle z, x \rangle.$$
-/
open Set
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- The support function of a set `C`: `σ_C(x) = sup_{z ∈ C} ⟨z, x⟩`. -/
noncomputable def supportFunction (C : Set H) (x : H) : EReal :=
  sSup ((fun z : H => (inner ℝ z x : EReal)) '' C)
