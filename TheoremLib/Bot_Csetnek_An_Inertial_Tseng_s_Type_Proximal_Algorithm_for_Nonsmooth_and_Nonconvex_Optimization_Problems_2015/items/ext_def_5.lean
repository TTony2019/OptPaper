import Mathlib
import Mathlib.Tactic
import Foundation.Topology.Sequences

namespace BotCsetnek2015

/-- Foundation sequence-cluster-point predicate recalled for the paper notation `omega`. -/
recall IsSequentialClusterPt

/-- The cluster point set `omega((z_n))` of a sequence. -/
def omega {X : Type*} [TopologicalSpace X] (z : Nat -> X) : Set X :=
  {x | IsSequentialClusterPt z x}

end BotCsetnek2015
