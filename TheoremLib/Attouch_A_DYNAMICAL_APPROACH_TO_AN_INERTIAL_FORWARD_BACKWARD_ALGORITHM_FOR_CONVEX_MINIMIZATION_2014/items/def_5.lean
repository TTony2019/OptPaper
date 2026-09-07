import Mathlib

namespace AttouchPeypouquetRedont2014

/-- The auxiliary difference `ζ_k = y_k - y_{k-1}`, defined for positive indices. -/
def zeta {H : Type*} [Sub H] (y : ℕ → H) (k : ℕ) (_hk : 1 ≤ k) : H := y k - y (k - 1)

/-- The paper's backward-difference formula is asserted only at positive indices. -/
theorem zeta_eq_sub_of_one_le {H : Type*} [Sub H] (y : ℕ → H) (k : ℕ) (_hk : 1 ≤ k) :
    zeta y k _hk = y k - y (k - 1) := rfl

end AttouchPeypouquetRedont2014
