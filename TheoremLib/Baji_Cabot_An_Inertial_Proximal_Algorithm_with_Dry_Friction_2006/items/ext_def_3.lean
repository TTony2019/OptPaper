import Mathlib
import Foundation.Convex.NormalCone

/-!
# Normal cone to a convex set
For a convex subset $C \subset H$ and $x \in C$, the normal cone to $C$ at $x$ is defined by:
$$N_C(x) = \{u \in H \mid \forall y \in C, \langle u, y - x \rangle \leqslant 0\}.$$
For $x \notin C$, $N_C(x) = \emptyset$. For a set $S \subset H$,
$N_C(S) = \bigcup_{\xi \in S} N_C(\xi)$.
-/
open Set

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! The normal cone is supplied canonically by `Foundation.Convex.NormalCone`
(Definition 6.38 of Bauschke–Combettes); recall it here for paper-local use. -/
recall Set.normalCone

/-- The normal cone to a convex set `C` over a set `S`:
`N_C(S) = ⋃_{ξ ∈ S} N_C(ξ)`. -/
def normalConeSet (C S : Set H) : Set H := ⋃ ξ ∈ S, normalCone C ξ
