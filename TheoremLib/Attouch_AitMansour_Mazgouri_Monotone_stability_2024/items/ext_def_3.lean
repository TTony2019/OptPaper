import Mathlib
import Foundation.Differentiation.ODE
import Foundation.Optimization.Argmin
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_3

open MeasureTheory

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The inertial gradient-like dynamics (DIN):
  ẍ_μ+γẋ_μ+β∇²φ_μ(x_μ)ẋ_μ+∇φ_μ(x_μ)=0 for a.e. t≥0 with the stated initial data.
  x_μ and ẋ_μ are locally absolutely continuous.  Supplied canonically by
  Foundation.

  Representational deviations from the paper (all in Foundation, hence not
  fixable from this directory): Foundation's `DIN` takes `gradφ` and `hessφ`
  as *arbitrary* data (`the φ argument is unused`), so it does not express that
  `hessφ` is the second derivative of `φ` — the paper's hypotheses `φ` of
  class `C²` and `∇²φ` the Hessian must be supplied separately at each call
  site (e.g. `thm_5`'s `hhess`); and the predicate does *not* carry the
  standing assumptions `γ > 0`, `β > 0`, `βγ > 1`, which the paper keeps as
  section hypotheses.  Note also that `DIN`'s derivative conditions hold only
  a.e. on `[0,+∞)` (via `IsLocallyAbsolutelyContinuous`), which does not by
  itself relate `dx` to `x` — consumers that need genuine solutions add the
  a.e. derivative conditions explicitly (e.g. `thm_7`'s `hderiv`/`hddx`). -/
recall DIN

/-- The set of minimizers of `φ`, supplied canonically by Foundation as
  `Optimization.argminSet` (the paper's `argmin`; membership is characterized
  by `Optimization.minimumValue_eq_of_mem_argminSet`, since the minimum value
  `sInf (Set.range φ)` is Foundation's `Optimization.minimumValue`). -/
recall Optimization.argminSet

/-- (PM_μ) denotes the minimization problem min_{x∈H} φ(x,μ).  The paper's
  (PM)/(PM_μ) are *problems*; here `PM φ` is the proposition that the minimum
  of `φ` over `H` is attained, i.e. that the argmin set is nonempty.  The
  paper has no separate notation for the parametrized problem: pass
  `φ := φ(·,μ)` to get (PM_μ). -/
abbrev PM {H : Type*} (φ : H → ℝ) : Prop := (Optimization.argminSet φ).Nonempty

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
