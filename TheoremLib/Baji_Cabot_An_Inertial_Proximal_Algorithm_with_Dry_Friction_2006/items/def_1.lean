import Mathlib.Tactic

/-!
# Distance function
Given a subset $A \subset H$, the distance function to $A$ is $d(x, A) = \inf_{y \in A} |x - y|$
for every $x \in H$.
-/
/-- The distance from a point to a set. -/
recall Metric.infDist
