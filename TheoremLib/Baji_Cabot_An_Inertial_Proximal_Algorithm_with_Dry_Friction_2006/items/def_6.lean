import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_3

/-!
# Set $\mathcal{D}$ of stationary indices
$\mathcal{D} = \{n \in \mathbb{N}, x_{n+1} = x_n\}$, where $(x_n)$ is the sequence
defined by Algorithm $(\mathcal{A})$.
-/
open Set
variable {H : Type _}
/-- The set of stationary indices: `D = {n | x_{n+1} = x_n}`. -/
def stationaryIndices (x : ℕ → H) : Set ℕ := {n | x (n+1) = x n}
