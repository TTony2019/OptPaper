import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_3
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_def_1

namespace BurachikSvaiterRobustnessHPE2001

/-- The closed ball `S` and related operator `U = T + N_S` used in Lemma 3.4. -/
def relatedBall {H : Type*} [NormedAddCommGroup H] (M : ℝ) : Set H :=
  Metric.closedBall 0 (2 * M)

def relatedOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) (M : ℝ) : SetValuedOperator H H :=
  setValuedSum T (normalityOperator (relatedBall (H := H) M))

end BurachikSvaiterRobustnessHPE2001
