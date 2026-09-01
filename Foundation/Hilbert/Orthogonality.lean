import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Hilbert Orthogonality

Basic orthogonality and norm-square identities in real inner product spaces.
-/

namespace Hilbert.Orthogonality

/-!
# Orthogonal vectors

The paper uses orthogonality of two vectors in a real inner product space as the condition
`inner ℝ x y = 0`.
-/

/-- Two vectors are orthogonal when their real inner product is zero. -/
def OrthogonalVectors {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : Prop :=
  inner ℝ x y = 0

/-!
# Norm squared identity

The paper uses the real inner product identity `‖z‖ ^ 2 = inner ℝ z z`.
-/

/-- The norm squared of a vector equals its real inner product with itself. -/
theorem norm_sq_eq_inner_self {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z : V) : ‖z‖ ^ 2 = inner ℝ z z := by
  exact (real_inner_self_eq_norm_sq z).symm

/-!
# Theorem 1

Pythagoras' identity for two orthogonal vectors in a real inner product space.
-/

/-- If `x` and `y` are orthogonal vectors, then `‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2`. -/
theorem theorem_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y : V} (hxy : OrthogonalVectors x y) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa [pow_two, OrthogonalVectors] using
    norm_add_sq_eq_norm_sq_add_norm_sq_real (x := x) (y := y) hxy

end Hilbert.Orthogonality
