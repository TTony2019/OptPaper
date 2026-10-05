import Foundation.OptimalTransport.Discrete

/-!
# A non-executable specification of HELLO

This file formalizes the finite optimal-transport objects used by the
dual-guided hierarchical edge-localization algorithm (HELLO).  The
algorithmic names below are specifications: they describe admissible inputs
and outputs without choosing an implementation of any solver or sampler.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

/-! ### Problems, parameters, and states -/

/-- An edge of an `m` by `n` transport problem. -/
abbrev Edge (m n : ℕ) := Fin m × Fin n

/-- A finite, nonnegative Kantorovich problem. -/
structure HELLOProblem where
  m : ℕ
  n : ℕ
  a : Fin m → ℝ
  b : Fin n → ℝ
  C : Fin m → Fin n → ℝ
  a_prob : IsDiscreteProbabilityVector a
  b_prob : IsDiscreteProbabilityVector b
  cost_nonneg : IsNonnegativeDiscreteCost C

/-- Numerical parameters appearing in Algorithm 1. -/
structure HELLOParameters where
  rho : ℝ
  tau : ℕ
  kappa : ℕ
  gamma : ℕ
  beta : ℕ
  epsilon : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  tau_pos : 0 < tau
  kappa_pos : 0 < kappa
  beta_ge_gamma_add_two : gamma + 2 ≤ beta
  epsilon_nonneg : 0 ≤ epsilon

/-- A set of active edges. -/
abbrev ActiveSupport (m n : ℕ) := Set (Edge m n)

/-- The support of a nonnegative transport matrix. -/
def primalSupport {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : ActiveSupport m n :=
  {e | 0 < X e.1 e.2}

/-- A primal matrix together with two dual potentials. -/
structure HELLOState (P : HELLOProblem) where
  X : Matrix (Fin P.m) (Fin P.n) ℝ
  f : Fin P.m → ℝ
  g : Fin P.n → ℝ

/-- The dual slack (called the dual score in HELLO). -/
def dualScore (P : HELLOProblem) (Z : HELLOState P)
    (i : Fin P.m) (j : Fin P.n) : ℝ :=
  Z.f i + Z.g j - P.C i j

/-- Edges outside `N` whose full dual constraint is violated. -/
def dualViolators (P : HELLOProblem) (Z : HELLOState P)
    (N : ActiveSupport P.m P.n) : ActiveSupport P.m P.n :=
  {e | e ∉ N ∧ 0 < dualScore P Z e.1 e.2}

/-- The matrix objective in the finite Kantorovich problem. -/
def primalObjective (P : HELLOProblem)
    (X : Matrix (Fin P.m) (Fin P.n) ℝ) : ℝ :=
  DiscreteKantorovichCost P.C X

/-- The dual objective in the finite Kantorovich problem. -/
def dualObjective (P : HELLOProblem)
    (f : Fin P.m → ℝ) (g : Fin P.n → ℝ) : ℝ :=
  DiscreteKantorovichDualObjective P.a P.b f g

/-- Exact primal feasibility and full dual feasibility. -/
def IsFullKKT (P : HELLOProblem) (Z : HELLOState P) : Prop :=
  IsDiscreteKantorovichCoupling P.a P.b Z.X ∧
    (∀ i j, Z.f i + Z.g j ≤ P.C i j) ∧
    (∀ i j, 0 < Z.X i j → Z.f i + Z.g j = P.C i j)

/-- A concrete residual useful for approximate HELLO output. -/
def primalResidual (P : HELLOProblem)
    (X : Matrix (Fin P.m) (Fin P.n) ℝ) : ℝ :=
  (∑ i, |∑ j, X i j - P.a i|) + ∑ j, |∑ i, X i j - P.b j|

/-- The positive part of all violations of the dual inequalities. -/
def dualResidual (P : HELLOProblem) (Z : HELLOState P) : ℝ :=
  ∑ i, ∑ j, max 0 (dualScore P Z i j)

/-- The complementarity residual on positive primal entries. -/
noncomputable def complementarityResidual (P : HELLOProblem) (Z : HELLOState P) : ℝ :=
  ∑ i, ∑ j, if 0 < Z.X i j then |dualScore P Z i j| else 0

/-- A finite KKT residual for a HELLO state. -/
noncomputable def kktResidual (P : HELLOProblem) (Z : HELLOState P) : ℝ :=
  primalResidual P Z.X + dualResidual P Z + complementarityResidual P Z

/-- The approximate stopping condition used by the algorithm. -/
def HasKKTResidual (P : HELLOProblem) (Z : HELLOState P) (epsilon : ℝ) : Prop :=
  kktResidual P Z ≤ epsilon

/-- Global primal optimality for the finite transport problem. -/
def IsPrimalOptimal (P : HELLOProblem)
    (X : Matrix (Fin P.m) (Fin P.n) ℝ) : Prop :=
  IsDiscreteKantorovichCoupling P.a P.b X ∧
    ∀ Y, IsDiscreteKantorovichCoupling P.a P.b Y →
      primalObjective P X ≤ primalObjective P Y

/-- Global dual optimality for the finite transport problem. -/
def IsDualOptimal (P : HELLOProblem)
    (f : Fin P.m → ℝ) (g : Fin P.n → ℝ) : Prop :=
  (∀ i j, f i + g j ≤ P.C i j) ∧
    ∀ f' g', (∀ i j, f' i + g' j ≤ P.C i j) →
      dualObjective P f' g' ≤ dualObjective P f g

/-! ### Restricted supports and the elementary subroutines -/

/-- A support contains a feasible transport plan and has basis size at most
`m + n - 1`. -/
def IsFeasibleBasis (P : HELLOProblem)
    (B : ActiveSupport P.m P.n) : Prop :=
  (∃ X, IsDiscreteKantorovichCoupling P.a P.b X ∧ primalSupport X ⊆ B) ∧
    Set.ncard B ≤ P.m + P.n - 1

/-- Specification of the Northwest-corner routine (Algorithm 4). -/
def northwestCornerSpec (P : HELLOProblem)
    (B : ActiveSupport P.m P.n) : Prop :=
  IsFeasibleBasis P B

/-- A primal plan restricted to an active support. -/
def IsRestrictedPrimal (P : HELLOProblem)
    (N : ActiveSupport P.m P.n)
    (X : Matrix (Fin P.m) (Fin P.n) ℝ) : Prop :=
  IsDiscreteKantorovichCoupling P.a P.b X ∧ primalSupport X ⊆ N

/-- Dual feasibility only on the active support. -/
def IsRestrictedDualFeasible (P : HELLOProblem)
    (N : ActiveSupport P.m P.n)
    (f : Fin P.m → ℝ) (g : Fin P.n → ℝ) : Prop :=
  ∀ ⦃i : Fin P.m⦄ ⦃j : Fin P.n⦄, (i, j) ∈ N → f i + g j ≤ P.C i j

/-- Optimality of a restricted primal plan. -/
def IsRestrictedPrimalOptimal (P : HELLOProblem)
    (N : ActiveSupport P.m P.n)
    (X : Matrix (Fin P.m) (Fin P.n) ℝ) : Prop :=
  IsRestrictedPrimal P N X ∧
    ∀ Y, IsRestrictedPrimal P N Y →
      primalObjective P X ≤ primalObjective P Y

/-- Optimality of a restricted dual pair. -/
def IsRestrictedDualOptimal (P : HELLOProblem)
    (N : ActiveSupport P.m P.n)
    (f : Fin P.m → ℝ) (g : Fin P.n → ℝ) : Prop :=
  IsRestrictedDualFeasible P N f g ∧
    ∀ f' g', IsRestrictedDualFeasible P N f' g' →
      dualObjective P f' g' ≤ dualObjective P f g

/-- The specification returned by a restricted LP solve. -/
structure RestrictedSolution (P : HELLOProblem)
    (N : ActiveSupport P.m P.n) (epsilon : ℝ) where
  state : HELLOState P
  primal_feasible : IsRestrictedPrimal P N state.X
  dual_feasible : IsRestrictedDualFeasible P N state.f state.g
  primal_optimal : IsRestrictedPrimalOptimal P N state.X
  dual_optimal : IsRestrictedDualOptimal P N state.f state.g
  residual_le : HasKKTResidual P state epsilon

/-- The `c`-transform of a source potential. -/
noncomputable def cTransform (P : HELLOProblem)
    (f : Fin P.m → ℝ) (j : Fin P.n) : ℝ :=
  sInf (Set.range fun i => P.C i j - f i)

/-- The symmetric transform that completes a source potential from a target
potential. -/
noncomputable def sourceCTransform (P : HELLOProblem)
    (g : Fin P.n → ℝ) (i : Fin P.m) : ℝ :=
  sInf (Set.range fun j => P.C i j - g j)

/-- Pull a coarse source potential to a fine source set. -/
def liftSourcePotential {fine coarse : HELLOProblem}
    (f : Fin coarse.m → ℝ) (sourceMap : Fin fine.m → Fin coarse.m) :
    Fin fine.m → ℝ :=
  fun i => f (sourceMap i)

/-- Pull a coarse target potential to a fine target set. -/
def liftTargetPotential {fine coarse : HELLOProblem}
    (g : Fin coarse.n → ℝ) (targetMap : Fin fine.n → Fin coarse.n) :
    Fin fine.n → ℝ :=
  fun j => g (targetMap j)

/-- A top-score selection from a finite candidate set. -/
def IsTopKByScore {α : Type*}
    (score : α → ℝ) (candidate selected : Set α)
    (k : ℕ) : Prop :=
  candidate.Finite ∧ selected ⊆ candidate ∧
    Set.ncard selected = min k (Set.ncard candidate) ∧
    ∀ ⦃e e' : α⦄, e ∈ candidate → e ∉ selected → e' ∈ selected →
      score e ≤ score e'

/-- A top-score selection of transport edges. -/
def IsTopKSelection {m n : ℕ}
    (score : Edge m n → ℝ) (candidate selected : ActiveSupport m n)
    (k : ℕ) : Prop :=
  IsTopKByScore score candidate selected k

/-- The row-wise and column-wise top-`k` dual assignment used by `Init`. -/
def IsNodewiseDualAssignment (P : HELLOProblem) (Z : HELLOState P)
    (k : ℕ) (A : ActiveSupport P.m P.n) : Prop :=
  ∃ rowChoice : Fin P.m → Set (Fin P.n),
    ∃ colChoice : Fin P.n → Set (Fin P.m),
      (∀ i, IsTopKByScore (fun j => dualScore P Z i j)
        Set.univ (rowChoice i) k) ∧
      (∀ j, IsTopKByScore (fun i => dualScore P Z i j)
        Set.univ (colChoice j) k) ∧
      A = {e | e.2 ∈ rowChoice e.1} ∪ {e | e.1 ∈ colChoice e.2}

/-- Row-wise and column-wise detection of positive dual violations. -/
def IsDualViolationDetection (P : HELLOProblem) (Z : HELLOState P)
    (gamma : ℕ) (V : ActiveSupport P.m P.n) : Prop :=
  (∃ rowChoice : Fin P.m → Set (Fin P.n),
      ∃ colChoice : Fin P.n → Set (Fin P.m),
        (∀ i, IsTopKByScore (fun j => dualScore P Z i j)
          {j | 0 < dualScore P Z i j} (rowChoice i) gamma) ∧
        (∀ j, IsTopKByScore (fun i => dualScore P Z i j)
          {i | 0 < dualScore P Z i j} (colChoice j) gamma) ∧
        V = {e | e.2 ∈ rowChoice e.1} ∪ {e | e.1 ∈ colChoice e.2})

/-- Specification of Algorithm 2 (`Init`).  The maps express the
coarse-to-fine node correspondence; the selected edges are top dual-score
violators and the resulting state is a restricted LP solution. -/
def initSpec {fine coarse : HELLOProblem}
    (coarseState : HELLOState coarse)
    (sourceMap : Fin fine.m → Fin coarse.m)
    (targetMap : Fin fine.n → Fin coarse.n)
    (B : ActiveSupport fine.m fine.n) (kappa : ℕ) (epsilon : ℝ)
    (N : ActiveSupport fine.m fine.n) (Z : HELLOState fine) : Prop :=
  B ⊆ N ∧
    (((∀ j, Z.g j = liftTargetPotential coarseState.g targetMap j) ∧
      (∀ i, Z.f i = sourceCTransform fine Z.g i)) ∨
      ((∀ i, Z.f i = liftSourcePotential coarseState.f sourceMap i) ∧
        (∀ j, Z.g j = cTransform fine Z.f j))) ∧
    ∃ A : ActiveSupport fine.m fine.n,
      IsNodewiseDualAssignment fine Z kappa A ∧ N = A ∪ B ∧
    IsRestrictedPrimalOptimal fine N Z.X ∧
    IsRestrictedDualOptimal fine N Z.f Z.g ∧
    HasKKTResidual fine Z epsilon

/-- Specification of Algorithm 3 (`UpdateSupp`). -/
def mandatorySupport (P : HELLOProblem) (Z : HELLOState P)
    (B V : ActiveSupport P.m P.n) : ActiveSupport P.m P.n :=
  B ∪ primalSupport Z.X ∪ V

/-- Specification of Algorithm 3 (`UpdateSupp`). -/
def admissibleSupportUpdate (P : HELLOProblem)
    (N : ActiveSupport P.m P.n) (Z : HELLOState P)
    (B : ActiveSupport P.m P.n) (beta gamma : ℕ)
    (N' : ActiveSupport P.m P.n) : Prop :=
  B ⊆ N ∧ primalSupport Z.X ⊆ N ∧
    ∃ V : ActiveSupport P.m P.n,
      IsDualViolationDetection P Z gamma V ∧
        V ⊆ dualViolators P Z N ∧
        mandatorySupport P Z B V ⊆ N' ∧
        N' ⊆ mandatorySupport P Z B V ∪ N ∧
        Set.ncard N' ≤ beta * (P.m + P.n) ∧
        IsTopKSelection (fun e => dualScore P Z e.1 e.2)
          (N \ mandatorySupport P Z B V) (N' \ mandatorySupport P Z B V)
          (Set.ncard N') ∧
        (dualViolators P Z N ≠ ∅ → ∃ e, e ∈ N' ∧ e ∈ V)

/-- The restricted LP solver in Algorithms 1--3 is an abstract relation. -/
def solveLPSpec (P : HELLOProblem)
    (N : ActiveSupport P.m P.n) (epsilon : ℝ) (Z : HELLOState P) : Prop :=
  ∃ solution : RestrictedSolution P N epsilon, solution.state = Z

/-! ### Hierarchies -/

/-- One admissible coarsening step.  The two maps aggregate the fine
marginals, and at least one side is strictly reduced while the other may be
shared. -/
def isHierarchyStep (rho : ℝ) (fine coarse : HELLOProblem) : Prop :=
  coarse.m ≤ fine.m ∧ coarse.n ≤ fine.n ∧
    (coarse.m = fine.m ∨ coarse.n = fine.n) ∧
    ((coarse.m < fine.m ∧ (coarse.m : ℝ) ≤ rho * fine.m) ∨
      (coarse.n < fine.n ∧ (coarse.n : ℝ) ≤ rho * fine.n)) ∧
    ∃ sourceMap : Fin fine.m → Fin coarse.m,
      ∃ targetMap : Fin fine.n → Fin coarse.n,
        (∀ i, coarse.a i = ∑ k, if sourceMap k = i then fine.a k else 0) ∧
        (∀ j, coarse.b j = ∑ k, if targetMap k = j then fine.b k else 0)

/-- Adjacent levels in a hierarchy, listed from finest to coarsest. -/
def isHierarchyChain (rho : ℝ) : List HELLOProblem → Prop
  | [] => False
  | [_] => True
  | fine :: coarse :: rest =>
      isHierarchyStep rho fine coarse ∧ isHierarchyChain rho (coarse :: rest)

/-- The final level of a hierarchy is below the coarsest threshold. -/
def isCoarsestWithin (tau : ℕ) : List HELLOProblem → Prop
  | [] => False
  | [P] => P.m ≤ tau ∧ P.n ≤ tau
  | _ :: rest => isCoarsestWithin tau rest

/-- Specification of Algorithm 5 (`BuildHier`). -/
def buildHierSpec (P : HELLOProblem) (params : HELLOParameters)
    (levels : List HELLOProblem) : Prop :=
  (∃ rest, levels = P :: rest) ∧
    isHierarchyChain params.rho levels ∧ isCoarsestWithin params.tau levels

/-! ### Algorithm 1 -/

/-- A finite refinement trace at one hierarchy level.  The sequence is indexed
by `ℕ`, but `terminal` records the finite stopping index; no update function
is chosen. -/
structure HELLORefinementRun (P : HELLOProblem) (params : HELLOParameters) where
  basis : ActiveSupport P.m P.n
  supports : ℕ → ActiveSupport P.m P.n
  states : ℕ → HELLOState P
  terminal : ℕ
  basis_spec : northwestCornerSpec P basis
  initial_basis : basis ⊆ supports 0
  initial_solve : solveLPSpec P (supports 0) params.epsilon (states 0)
  update_step : ∀ k, k < terminal →
    admissibleSupportUpdate P (supports k) (states k) basis params.beta params.gamma
      (supports (k + 1))
  solve_step : ∀ k, k ≤ terminal →
    solveLPSpec P (supports k) params.epsilon (states k)
  terminal_residual : HasKKTResidual P (states terminal) params.epsilon

/-- A complete non-executable HELLO run.  The field `level_solutions` records
the restricted solve supplied at every level, while `refinement` records the
finite refinement trace on the finest level. -/
structure HELLORun (P : HELLOProblem) (params : HELLOParameters) where
  levels : List HELLOProblem
  hierarchy : buildHierSpec P params levels
  level_solutions :
    ∀ ⦃Q : HELLOProblem⦄, Q ∈ levels →
      ∃ N : ActiveSupport Q.m Q.n, ∃ Z : HELLOState Q,
        solveLPSpec Q N params.epsilon Z
  refinement : HELLORefinementRun P params

/-- Specification of Algorithm 1 (`HELLO`). -/
def helloSpec (P : HELLOProblem) (params : HELLOParameters)
    (Z : HELLOState P) : Prop :=
  ∃ run : HELLORun P params, run.refinement.states run.refinement.terminal = Z

end DualGuided2026
