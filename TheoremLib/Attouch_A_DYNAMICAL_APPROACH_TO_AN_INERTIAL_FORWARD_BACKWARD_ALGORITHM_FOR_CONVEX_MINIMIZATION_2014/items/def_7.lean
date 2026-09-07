import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_6

namespace AttouchPeypouquetRedont2014

/-- The auxiliary quantity `G_k(q)` of (3.11). -/
noncomputable def auxiliaryG {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (_hk : 2 ≤ k) : ℝ :=
  inner ℝ (zSequence u y a b lam k (by omega)) (u k - q) -
    ∑ i ∈ (Finset.Icc 2 k).attach,
      inner ℝ (zSequence u y a b lam i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega))
      (velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega))

/-- Equation (3.11) is used in the paper only for `k ≥ 2`. -/
theorem auxiliaryG_defined_of_two_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (_hk : 2 ≤ k) :
    auxiliaryG u y a b lam q k _hk =
      inner ℝ (zSequence u y a b lam k (by omega)) (u k - q) -
        ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega))
          (velocity u i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)) := rfl

end AttouchPeypouquetRedont2014
