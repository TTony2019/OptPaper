import Mathlib
import Foundation.Metric.FixedPoint
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_1

/-! Item `ext_thm_6`: [4, Proposition 4(g)] as used in Remark 7.7.

  The paper's Remark 7.7 reads off from [4, Proposition 4(g)] the
  Painlevé–Kuratowski convergence of the set of `ε`-approximate solutions
  `S^ε(A,u₀,v₀)` to the exact solution `x_μ` as `ε → 0`: *any* sequence of
  approximate solutions converges to the exact solution, and *conversely* the
  exact solution can be approached by approximate solutions.

  The contractive fixed-point setting of Section 7 is formalized here:
  Foundation's `epsilon_approximate_fixedPoint_bound` gives the `ε`-ball form
  of the first half, and `ext_thm_6_painleve_kuratowski` below states both
  directions of the Painlevé–Kuratowski convergence (in a metric space, a
  family of sets converges to a point in that sense exactly when every
  selection along `ε → 0` converges to it and the point is approachable by
  selections).  The instantiation to the Volterra map `Γ`, i.e. to
  `S^ε(μ) ⊆ C([0,T];H)`, is `approxSolutions_painleve_kuratowski` in
  `items/thm_10.lean`, where the contraction estimate
  `γT + T²/α < 1` and the map `Γ` are available. -/

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Filter

/-- Convergence of ε-approximate fixed points to the exact contraction fixed
  point (cf. [4, Proposition 4(g)]). For the contractive fixed-point setting
  used in Section 7: if T is a λ-contraction (λ∈[0,1)) with unique fixed
  point x*, then ε-Fix(T) converges in the Painlevé–Kuratowski sense to
  {x*} as ε→0.  Supplied canonically by Foundation as
  `epsilon_approximate_fixedPoint_bound`. -/
recall epsilon_approximate_fixedPoint_bound

/-- The ε-approximate fixed point bound, supplied canonically by Foundation. -/
abbrev ext_thm_6 {X : Type*} [PseudoMetricSpace X] (T : X → X) (c : ℝ) (xstar : X)
    (hc : 0 ≤ c) (hc_lt_one : c < 1)
    (hcontr : ∀ x y : X, dist (T x) (T y) ≤ c * dist x y)
    (hfix : T xstar = xstar) (huniq : ∀ x : X, T x = x → x = xstar) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
      ∀ y : X, dist y (T y) ≤ ε → dist y xstar < η :=
  epsilon_approximate_fixedPoint_bound T c xstar hc hc_lt_one hcontr hfix huniq

/-- Quantitative form of the approximate fixed point bound: an `ε`-approximate
  fixed point of a `c`-contraction (`c < 1`) is at distance at most
  `ε / (1 - c)` from the (given) fixed point.  This is the rate hidden in the
  proof of [4, Proposition 4(g)] / `epsilon_approximate_fixedPoint_bound`. -/
theorem epsilon_fix_dist_le {X : Type*} [PseudoMetricSpace X] (T : X → X) (c : ℝ)
    (xstar : X) (hc_lt_one : c < 1)
    (hcontr : ∀ x y : X, dist (T x) (T y) ≤ c * dist x y)
    (hfix : T xstar = xstar) {y : X} {ε : ℝ} (hy : dist y (T y) ≤ ε) :
    dist y xstar ≤ ε / (1 - c) := by
  have hkey : dist y xstar ≤ ε + c * dist y xstar := by
    calc
      dist y xstar ≤ dist y (T y) + dist (T y) xstar := dist_triangle y (T y) xstar
      _ = dist y (T y) + dist (T y) (T xstar) := by rw [hfix]
      _ ≤ ε + c * dist y xstar := add_le_add hy (hcontr y xstar)
  have hgap : 0 < 1 - c := sub_pos.mpr hc_lt_one
  rw [le_div_iff₀ hgap]
  nlinarith [dist_nonneg (x := y) (y := xstar), hkey]

/-- Painlevé–Kuratowski convergence of the `ε`-approximate fixed points of a
  contraction to its fixed point — the two directions of [4, Proposition 4(g)]
  used in Remark 7.7:

  * every sequence `y_n` of `ε_n`-approximate fixed points with `ε_n → 0`
    (and `ε_n > 0`) converges to `xstar`;
  * conversely `xstar` is an `ε`-approximate fixed point for every `ε ≥ 0`,
    so the exact fixed point is the limit of a sequence of approximate ones
    (take the constant sequence `y_n = xstar`).

  Uniqueness of the fixed point is not needed, `xstar` being given together
  with `hfix`. -/
theorem ext_thm_6_painleve_kuratowski {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (c : ℝ) (xstar : X) (hc_lt_one : c < 1)
    (hcontr : ∀ x y : X, dist (T x) (T y) ≤ c * dist x y)
    (hfix : T xstar = xstar) :
    (∀ (εseq : ℕ → ℝ) (yseq : ℕ → X), (∀ n, 0 < εseq n) →
        Tendsto εseq atTop (nhds 0) →
        (∀ n, dist (yseq n) (T (yseq n)) ≤ εseq n) →
        Tendsto yseq atTop (nhds xstar)) ∧
      (∀ ε : ℝ, 0 ≤ ε → dist xstar (T xstar) ≤ ε) := by
  constructor
  · intro εseq yseq _ hlim hyseq
    have hle : ∀ n, dist (yseq n) xstar ≤ εseq n / (1 - c) := fun n =>
      epsilon_fix_dist_le T c xstar hc_lt_one hcontr hfix (hyseq n)
    have hlim' : Tendsto (fun n => εseq n / (1 - c)) atTop (nhds 0) := by
      simpa using hlim.div_const (1 - c)
    have hdist : Tendsto (fun n => dist (yseq n) xstar) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
        (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall hle)
    exact tendsto_iff_dist_tendsto_zero.mpr hdist
  · intro ε hε
    rw [hfix, dist_self]
    exact hε

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
