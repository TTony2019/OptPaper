import Mathlib
import Foundation.SetValued.Basic
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Convex.Subdifferential

open scoped InnerProductSpace

open ERealFunction

/-- The convex subdifferential, supplied canonically by Foundation (Bauschke--Combettes
Def 16.1).  For a proper function it is empty outside the effective domain
(Proposition 16.4 (1)). -/
recall ERealFunction.subdifferential

/-- A subgradient can only sit at a point of the effective domain of a proper function. -/
theorem mem_subdifferential_dom_of_mem_subdifferential {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (hProper : ERealFunction.IsProper f)
    {x v : H} (hv : v ∈ subdifferential f x) : x ∈ ERealFunction.dom f := by
  rw [subdifferential] at hv
  rcases hProper.2 with ⟨z, hz⟩
  by_contra hx
  have hx_top : f x = ⊤ := le_antisymm le_top (not_lt.mp hx)
  have hz' := hv z
  rw [hx_top] at hz'
  exact (not_le_of_gt hz) (by simpa [EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] using hz')
