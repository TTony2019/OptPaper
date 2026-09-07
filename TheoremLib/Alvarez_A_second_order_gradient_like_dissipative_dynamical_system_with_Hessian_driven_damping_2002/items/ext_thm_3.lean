import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
-- NB: the second-order paper's own `ext_def_1` is deliberately not imported
-- here: both it and `Alvarez_Optimizing_..._2002.items.ext_def_1` (pulled in
-- transitively by `ext_thm_7` below) declare `Alvarez2002.argmin`/`argminOn`
-- in the shared `Alvarez2002` namespace, so importing both is a name clash.
-- The generic `sInf`-based `argmin`/`argminOn` of the Optimizing paper is
-- therefore what is in scope for this file; a file-local notation (below)
-- re-routes the unqualified `argmin`/`argminOn` of this file to the intended
-- ∀-form definitions, so the statements keep their original meaning.
import TheoremLib.Alvarez_Optimizing_properties_of_an_inertial_dynamical_system_with_geometric_damping_2002.items.ext_def_2
import TheoremLib.Alvarez_Optimizing_properties_of_an_inertial_dynamical_system_with_geometric_damping_2002.items.ext_thm_7

namespace Alvarez2002

open ERealFunction

/-- ∀-form minimizer, matching the real-valued `Alvarez2002.argmin` of the
second-order paper's `ext_def_1` (not importable here, see above). -/
private def argmin_any {X E : Type*} [LE E] (f : X → E) : Set X := {z | ∀ y, f z ≤ f y}

/-- ∀-form restricted minimizer, matching `Alvarez2002.argminOn` of the
second-order paper's `ext_def_1`. -/
private def argminOn_any {X E : Type*} [LE E] (C : Set X) (f : X → E) : Set X :=
  {z | z ∈ C ∧ ∀ y ∈ C, f z ≤ f y}

-- Keep the intended ∀-form meaning for the statements of this file.
local notation "argmin" => argmin_any
local notation "argminOn" => argminOn_any

/-- The ∀-form minimizer agrees with the generic (`sInf`-based) minimizer of
`Alvarez2002.ext_def_1` on complete linear orders (e.g. `EReal`). -/
private theorem forall_min_of_mem_argmin {X E : Type*} [CompleteLinearOrder E]
    (f : X → E) {z : X} (hz : z ∈ Alvarez2002.argmin f) : ∀ y, f z ≤ f y := by
  rw [Alvarez2002.argmin, Alvarez2002.argminOn] at hz
  intro y
  exact hz.2.symm ▸ sInf_le (Set.mem_image_of_mem _ (Set.mem_univ y))

/-- The converse of `forall_min_of_mem_argmin`. -/
private theorem mem_argmin_of_forall {X E : Type*} [CompleteLinearOrder E]
    (f : X → E) {z : X} (hz : ∀ y, f z ≤ f y) : z ∈ Alvarez2002.argmin f := by
  rw [Alvarez2002.argmin, Alvarez2002.argminOn]
  refine ⟨Set.mem_univ z, ?_⟩
  apply le_antisymm
  · exact le_sInf (by intro b hb; rcases hb with ⟨y, hy, rfl⟩; exact hz y)
  · exact sInf_le (Set.mem_image_of_mem _ (Set.mem_univ z))

/-- Bruck's strong-convergence theorem for an even convex gradient flow. -/
theorem bruck_strong_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (E : H → ℝ) (X : ℝ → H) (M : Set H)
    (hconvex : ConvexOn ℝ Set.univ E) (heven : ∀ x, E (-x) = E x)
    (hmin : M = argmin E) (hM : M.Nonempty)
    (hproper : ERealFunction.IsProper fun x => (E x : EReal))
    (hlsc : LowerSemicontinuous fun x => (E x : EReal))
    (hconvexEpi : Convex ℝ (ERealFunction.epigraph fun x => (E x : EReal)))
    (hsol : ∃ uExt : ℝ → H,
      (∀ t : Set.Ici (0 : ℝ), uExt t = X t) ∧
      (∀ t : Set.Ici (0 : ℝ), (0 : ℝ) < t → (E (X t) : EReal) ≠ ⊤) ∧
      (∀ δ : ℝ, 0 < δ → ∃ K : NNReal, LipschitzOnWith K uExt (Set.Ici δ)) ∧
      ContinuousOn uExt (Set.Ici 0) ∧
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        0 ≤ t → -deriv uExt t ∈ subdifferential (fun x => (E x : EReal)) (uExt t)) :
    ∃ m ∈ M, Filter.Tendsto X Filter.atTop (nhds m) := by
  rcases hM with ⟨z, hzM⟩
  rw [hmin] at hzM
  have hminEreal : ∃ z : H, z ∈ argmin (fun x => (E x : EReal)) := by
    refine ⟨z, ?_⟩
    intro y
    exact EReal.coe_le_coe (hzM y)
  have hminEreal' : ∃ z : H, z ∈ Alvarez2002.argmin (fun x => (E x : EReal)) := by
    rcases hminEreal with ⟨w, hw⟩
    exact ⟨w, mem_argmin_of_forall (fun x => (E x : EReal)) hw⟩
  let u : Set.Ici (0 : ℝ) → H := fun t => X t
  have hsol' : ∃ uExt : ℝ → H,
      (∀ t : Set.Ici (0 : ℝ), uExt t = u t) ∧
      (∀ t : Set.Ici (0 : ℝ), (0 : ℝ) < t → (E (u t) : EReal) ≠ ⊤) ∧
      (∀ δ : ℝ, 0 < δ → ∃ K : NNReal, LipschitzOnWith K uExt (Set.Ici δ)) ∧
      ContinuousOn uExt (Set.Ici 0) ∧
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        0 ≤ t → -deriv uExt t ∈ subdifferential (fun x => (E x : EReal)) (uExt t) := by
    simpa [u] using hsol
  rcases bruck_subgradient_flow_convergence (E := H) (fun x => (E x : EReal))
      hproper hlsc hconvexEpi u hminEreal' hsol' with ⟨m, hm, _, hstrong⟩
  have hevenEreal : ∀ x : H, (E (-x) : EReal) = (E x : EReal) := by
    intro x
    exact congrArg (fun r : ℝ => (r : EReal)) (heven x)
  have hu : Filter.Tendsto u Filter.atTop (nhds m) := hstrong hevenEreal
  have hmReal : m ∈ argmin E := by
    intro y
    exact EReal.coe_le_coe_iff.mp (forall_min_of_mem_argmin (fun x => (E x : EReal)) hm y)
  have hmM : m ∈ M := by
    rw [hmin]
    exact hmReal
  have hX : Filter.Tendsto X Filter.atTop (nhds m) := by
    have hg : Filter.Tendsto (fun t : ℝ =>
        (⟨max t (0 : ℝ), le_max_right t (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro a
      refine Filter.eventually_atTop.2 ⟨(max (a : ℝ) (0 : ℝ) : ℝ), ?_⟩
      intro t ht
      change (a : ℝ) ≤ (max t (0 : ℝ) : ℝ)
      exact le_trans (le_trans (le_max_left (a : ℝ) (0 : ℝ)) ht) (le_max_left t (0 : ℝ))
    have hcomp : Filter.Tendsto
        (fun t : ℝ => X (⟨max t (0 : ℝ), le_max_right t (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
        Filter.atTop (nhds m) := hu.comp hg
    refine hcomp.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hmax : max t (0 : ℝ) = t := max_eq_left (le_of_lt ht)
    simp [u, hmax]
  exact ⟨m, hmM, hX⟩

end Alvarez2002
