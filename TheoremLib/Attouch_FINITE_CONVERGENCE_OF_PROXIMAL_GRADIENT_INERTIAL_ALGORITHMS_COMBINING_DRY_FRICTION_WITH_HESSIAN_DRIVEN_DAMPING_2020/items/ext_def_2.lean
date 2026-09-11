import Mathlib

noncomputable section

/-- Fenchel conjugate of a real-valued function. -/
def fenchelConjugate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (u : H) : ℝ := sSup (Set.range fun x ↦ @inner ℝ H _ u x - g x)

/-- Fenchel conjugate of an extended-real-valued function. -/
def fenchelConjugateEReal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (u : H) : EReal :=
  sSup (Set.range fun x ↦ (@inner ℝ H _ u x : EReal) - g x)
