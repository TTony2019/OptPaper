import Mathlib
namespace Alvarez2002
open Filter
def omegaLimit {H : Type*} [TopologicalSpace H] (x : Set.Ici (0 : ℝ) → H) : Set H :=
  {a | ∃ t : ℕ → Set.Ici (0 : ℝ), Tendsto (fun n => (t n : ℝ)) atTop atTop ∧
    Tendsto (fun n => x (t n)) atTop (nhds a)}
noncomputable def distanceTo {H : Type*} [PseudoMetricSpace H] (u : H) (A : Set H) (_hA : A.Nonempty) : ℝ := Metric.infDist u A
end Alvarez2002
