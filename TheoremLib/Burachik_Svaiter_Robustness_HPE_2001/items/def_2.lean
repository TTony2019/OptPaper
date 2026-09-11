import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.algo_1

namespace BurachikSvaiterRobustnessHPE2001

/-- Equation (15): the exact extragradient step associated with HPE data. -/
def extragradientStep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) (k : ℕ) : H :=
  A.x k - A.c k • A.v k

end BurachikSvaiterRobustnessHPE2001
