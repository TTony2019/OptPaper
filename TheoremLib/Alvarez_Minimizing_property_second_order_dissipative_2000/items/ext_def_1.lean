import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_2

namespace Alvarez2000

open scoped InnerProductSpace

/-- The mechanical energy of a trajectory solving `(E_gamma; u0, v0)`. -/
noncomputable def dissipativeEnergy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) (t : Set.Ici (0 : ℝ)) : ℝ :=
  (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (t : ℝ) 1‖ ^ 2 + Phi (sys.u (t : ℝ))

end Alvarez2000
