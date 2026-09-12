import Mathlib
import Mathlib.Tactic
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Optimization.Argmin

namespace Nesterov1983

/-- Foundation's effective domain for extended-real-valued functions. -/
recall ERealFunction.dom

/-- The set of minimizers of `g` over `S` is supplied canonically by Foundation. -/
recall Optimization.argminOn

/-- The set of maximizers of `g` over `S`. -/
def argmaxOn {X V : Type*} [Preorder V] (g : X → V) (S : Set X) : Set X :=
  {x | x ∈ S ∧ ∀ z ∈ S, g z ≤ g x}

end Nesterov1983
