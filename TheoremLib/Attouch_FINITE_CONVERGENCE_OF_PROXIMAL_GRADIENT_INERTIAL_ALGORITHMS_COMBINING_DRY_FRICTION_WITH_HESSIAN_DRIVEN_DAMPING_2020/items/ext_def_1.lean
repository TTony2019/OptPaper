import Foundation.SetValued.Basic
import Mathlib
import Foundation.Convex.Subdifferential

open scoped InnerProductSpace

open ERealFunction

/-! The convex subdifferential of a real-valued function, as a set-valued operator, is supplied
canonically by Foundation (Bauschke--Combettes Def 16.1); real-valued functions are used via the
canonical coercion `H → ℝ → EReal`. -/
recall ERealFunction.subdifferential
