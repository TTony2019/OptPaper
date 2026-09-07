import Mathlib

/-!
# Separately Continuous Function

A function F : X × Y → ℝ on topological spaces X, Y is separately continuous
if for each fixed y, the map x ↦ F(x, y) is continuous, and for each fixed x,
the map y ↦ F(x, y) is continuous.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Topology

/-- A function F : X × Y → ℝ is separately continuous if it is continuous in each
argument when the other is fixed. -/
def IsSeparatelyContinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Y → ℝ) : Prop :=
  (∀ (y : Y), Continuous (fun (x : X) => F x y)) ∧
  (∀ (x : X), Continuous (fun (y : Y) => F x y))

/-- A function F : X × Y → ℝ (in curried form) is separately continuous on
each coordinate. -/
def IsSeparatelyContinuous' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X × Y → ℝ) : Prop :=
  (∀ (y : Y), Continuous (fun (x : X) => F (x, y))) ∧
  (∀ (x : X), Continuous (fun (y : Y) => F (x, y)))
