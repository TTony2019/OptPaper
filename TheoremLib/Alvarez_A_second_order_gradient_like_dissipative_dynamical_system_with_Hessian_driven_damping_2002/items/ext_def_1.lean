import Mathlib
namespace Alvarez2002
def argmin {H : Type*} (Φ : H → ℝ) : Set H := {z | ∀ y, Φ z ≤ Φ y}
def argminOn {H : Type*} (C : Set H) (Φ : H → ℝ) : Set H := {z | z ∈ C ∧ ∀ y ∈ C, Φ z ≤ Φ y}
def IsCriticalPoint {H : Type*} [Zero H] (gradΦ : H → H) (a : H) : Prop := gradΦ a = 0
end Alvarez2002
