import Mathlib

/-!
# Operator distances

Supremal discrepancy distances between two operators on a closed ball,
used by stability and convergence-rate analysis of operator dynamics.

## Main definitions

- `supDiscrepancyOnBall r A B`: the supremal pointwise discrepancy
  `‖A u - B u‖` over the closed ball `‖u‖ ≤ r` (the paper's `d_r`-type
  distance between `A` and `B` on the ball).
- `ratioDistanceOnBall r A B`: the supremal ratio discrepancy
  `‖A u - B v‖ / ‖u - v‖` over distinct points `u ≠ v` in the closed ball
  of radius `r`.

Source paper: Attouch, Ait Mansour, Mazgouri (2024), "Monotone stability of
the damped system" — `items/def_6`, `items/def_8`.
-/

/-- The supremal pointwise discrepancy `‖A u - B u‖` between two operators on
  the closed ball of radius `r` (the paper's `d_r` distance on the ball). -/
noncomputable def supDiscrepancyOnBall {H : Type*} [NormedAddCommGroup H] (r : ℝ)
    (_hr : 0 < r) (A B : H → H) : ℝ :=
  sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A u - B u‖}

/-- The supremal ratio discrepancy `‖A u - B v‖ / ‖u - v‖` between two
  operators, over distinct points `u ≠ v` in the closed ball of radius `r`
  (the paper's `d_r` distance with the distinct-points condition). -/
noncomputable def ratioDistanceOnBall {H : Type*} [NormedAddCommGroup H] (r : ℝ)
    (_hr : 0 < r) (A B : H → H) : ℝ :=
  sSup {q : ℝ | ∃ u v : H, ‖u‖ ≤ r ∧ ‖v‖ ≤ r ∧ u ≠ v ∧
    q = ‖A u - B v‖ / ‖u - v‖}
