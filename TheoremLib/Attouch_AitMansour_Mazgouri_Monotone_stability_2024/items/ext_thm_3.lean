import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_6

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter

/-- Alvarez-Attouch-Bolte-Redont Proposition 5.1 (reference [10]), used in the
  paper's Theorem 6.2: under the hypotheses of Section 6 (βγ>1, each φ(⋅,μ)
  differentiable and δ_μ-strongly convex, (9)), every trajectory of (DIN)
  converges strongly to a minimizer of φ.

  Deviations from the paper (the previous proof deduced `Subsingleton H` from
  `int(argmin φ(·,μ)) ≠ ∅` plus strong convexity, which is contradictory on any
  nontrivial `H` and hence made the statement vacuous):

  * the hypothesis `int(argmin φ(·,μ)) ≠ ∅` is dropped — in the *strongly*
    convex setting it is not needed, mere nonemptiness of the argmin set
    suffices (in [10] it is the convex case that requires it, to exclude
    landing on a non-minimizing critical point);
  * convergence is *proved*, not quoted: a minimizer `z` of `φ(·,μ)` is a
    critical point (`grad_eq_zero_of_mem_argminSet`), so it is the equilibrium
    of the first-order reformulation and `din_tendsto_to_critical` gives strong
    convergence, exponentially fast;
  * as for Theorem 6.1, the bridge to the first-order reformulation is taken as
    input: `DINGradientLift` is *constructed* here by `dinGradientLift_of_DIN`
    (from the `DIN` strong-solution conditions, the Hessian being the derivative
    of the gradient, and the gradient being Lipschitz along the trajectory), and
    the energy strong monotonicity is derived by
    `energyStrong_of_strongConvex`. -/
theorem ext_thm_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H) (γ β : ℝ)
    (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1) (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (hargmin : ∀ μ : M, (Optimization.argminSet (φ μ)).Nonempty) :
    ∀ μ : M, ∃ z ∈ Optimization.argminSet (φ μ), Tendsto (x μ) atTop (nhds z) := by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  intro μ
  obtain ⟨z, hz⟩ := hargmin μ
  refine ⟨z, hz, din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ))
    hlift (fun p q => energyStrong_of_strongConvex (μ := μ) hβ hβγ (hstrong μ) (hgrad μ) p q) hβ
    (energyRate_pos hβ hγ (hstrong μ).1 hβγ)
    (grad_eq_zero_of_mem_argminSet (hgrad μ) hz)⟩

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
