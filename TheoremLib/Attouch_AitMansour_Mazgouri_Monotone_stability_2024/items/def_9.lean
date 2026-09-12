import Mathlib
import Foundation.Differentiation.ODE
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3

/-! Item `def_9`: the stability notions of Definition 6.6.

  The paper gives four notions — Lyapunov stability for (DIN), asymptotic
  stability, Lyapunov uniform `μ̄`-stability, and asymptotic uniform
  `μ̄`-stability — each of which can be cited on its own (Definition 6.6 (1)
  and (2)).  They are formalized below as the four separately usable predicates
  `def_9_lyapunovStable`, `def_9_asymptoticallyStable`,
  `def_9_uniformlyStable`, `def_9_uniformlyAsymptoticallyStable`; the bundled
  conjunction `def_9` is kept for consumers that want all four at once.

  The trajectory family has signature `M → H → ℝ → H`, i.e. it is indexed by
  the parameter `μ` and the initial *position* `u₀`, with `trajectory μ u₀ t`
  standing for the paper's `x_μ(t)`.  Two residual deviations from Definition
  6.6: the initial *velocity* `v₀^μ` of `DIN(φ,μ)` is implicit in the data
  family rather than an explicit argument, and the predicates are stated for an
  arbitrary family of paths, not literally for solutions of `DIN(φ,μ)`
  (`thm_7` is the instantiation: it proves the paper's Theorem 6.7 about the
  DIN solution family with these notions). -/

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- Lyapunov stability of an equilibrium.  Supplied canonically by Foundation;
  the predicate below is definitionally the same notion. -/
recall IsLyapunovStable

/-- Asymptotic stability of an equilibrium.  Supplied canonically by
  Foundation — note that Foundation's predicate contains only the limit
  condition, so the paper's "it is Lyapunov stable *and* ..." needs the
  conjunction made explicit (as in `def_9_asymptoticallyStable` below). -/
recall IsAsymptoticallyStable

/-- Uniform (in the parameter) Lyapunov stability.  Supplied canonically by
  Foundation. -/
recall IsUniformlyStable

/-- Uniform asymptotic stability.  Supplied canonically by Foundation —
  again the convergence condition only; the Lyapunov half is conjoined
  separately in `def_9_uniformlyAsymptoticallyStable`. -/
recall IsUniformlyAsymptoticallyStable

/-- Definition 6.6 (1), first half: `xbar` is Lyapunov stable for (DIN).  For
  every `ε > 0` there is `δ > 0` such that `‖u₀ - xbar‖ < δ` implies
  `‖x(t) - xbar‖ < ε` for every `t ≥ 0`.  Definitionally Foundation's
  `IsLyapunovStable xbar trajectory μbar` (the reference parameter `μbar` only
  enters through the family). -/
def def_9_lyapunovStable {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u₀ : H, ‖u₀ - xbar‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖trajectory μbar u₀ t - xbar‖ < ε

/-- Definition 6.6 (1), second half: `xbar` is asymptotically stable for
  (DIN).  It is Lyapunov stable (see above) and there exists `δ > 0` such that
  `‖x₀ - xbar‖ < δ` implies `lim_{t→∞} ‖x(t) - xbar‖ = 0`.

  Foundation's `IsAsymptoticallyStable` is the second conjunct alone; the
  conjunction is what Definition 6.6 defines. -/
def def_9_asymptoticallyStable {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  def_9_lyapunovStable xbar trajectory μbar ∧ IsAsymptoticallyStable xbar trajectory μbar

/-- Definition 6.6 (2), first half: `xbar` is Lyapunov uniformly `μ̄`-stable for
  the family `DIN(φ,μ)`.  For every `ε > 0` there is `δ > 0` such that
  `‖u₀ - xbar‖ < δ` and `‖μ - μ̄‖ < δ` imply `‖x_μ(t) - xbar‖ < ε` for every
  `t ≥ 0`.  Definitionally Foundation's `IsUniformlyStable xbar trajectory μbar`
  (the paper's `𝒱(μ̄)`-neighbourhood is encoded by the `δ`-ball on the
  parameter). -/
def def_9_uniformlyStable {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : M, ‖μ - μbar‖ < δ →
    ∀ u₀ : H, ‖u₀ - xbar‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖trajectory μ u₀ t - xbar‖ < ε

/-- Definition 6.6 (2), second half: `xbar` is asymptotically uniformly
  `μ̄`-stable.  It is Lyapunov uniformly `μ̄`-stable (see above) and there is
  `δ > 0` such that `‖u₀ - xbar‖ < δ` and `‖μ - μ̄‖ < δ` imply
  `lim_{t→∞} ‖x_μ(t) - xbar‖ = 0`. -/
def def_9_uniformlyAsymptoticallyStable {H M : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup M] (xbar : H) (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  def_9_uniformlyStable xbar trajectory μbar ∧
    IsUniformlyAsymptoticallyStable xbar trajectory μbar

/-- Definition 6.6 as a single proposition: `xbar` is simultaneously Lyapunov
  stable, asymptotically stable, Lyapunov uniformly `μ̄`-stable and
  asymptotically uniformly `μ̄`-stable for the family.  Each of the four
  notions is available separately as `def_9_lyapunovStable`,
  `def_9_asymptoticallyStable`, `def_9_uniformlyStable` and
  `def_9_uniformlyAsymptoticallyStable`. -/
def def_9 {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M] (xbar : H)
    (trajectory : M → H → ℝ → H) (μbar : M) : Prop :=
  def_9_lyapunovStable xbar trajectory μbar ∧
    def_9_asymptoticallyStable xbar trajectory μbar ∧
    def_9_uniformlyStable xbar trajectory μbar ∧
    def_9_uniformlyAsymptoticallyStable xbar trajectory μbar

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
