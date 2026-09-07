import Mathlib

namespace AttouchPeypouquetRedont2014

/-- The velocity `ξ_k = u_k - u_{k-1}`, defined for positive indices. -/
def velocity {H : Type*} [Sub H] (u : ℕ → H) (k : ℕ) (_hk : 1 ≤ k) : H := u k - u (k - 1)

/-- The paper's backward-difference formula is asserted only at positive indices. -/
theorem velocity_eq_sub_of_one_le {H : Type*} [Sub H] (u : ℕ → H) (k : ℕ) (_hk : 1 ≤ k) :
    velocity u k _hk = u k - u (k - 1) := rfl

end AttouchPeypouquetRedont2014
