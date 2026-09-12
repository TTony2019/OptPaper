import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_1

namespace BotCsetnek2015

/-- Problem 3.1 data: minimize the extended-real objective `f + h` on `R^m`. -/
structure ProblemData (m : Nat) where
  m_pos : 1 <= m
  f : EuclideanSpace m -> EReal
  h : EuclideanSpace m -> Real
  Lgrad_h : Real
  f_proper : ERealFunction.IsProper f
  f_lsc : LowerSemicontinuous f
  f_bddBelow : exists c : Real, forall x : EuclideanSpace m, (c : EReal) <= f x
  h_frechet_differentiable : Differentiable Real h
  h_lipschitz_gradient : HasLipschitzContinuousGradient h Lgrad_h

/-- The objective `f + h` of Problem 3.1. -/
noncomputable def ProblemData.objective {m : Nat} (P : ProblemData m) :
    EuclideanSpace m -> EReal :=
  objectiveSum P.f P.h

/-- The formal minimization problem `(P) inf_x (f + h)(x)`. -/
noncomputable def ProblemData.IsSolution {m : Nat} (P : ProblemData m)
    (x : EuclideanSpace m) : Prop :=
  IsMinOn P.objective Set.univ x

end BotCsetnek2015
