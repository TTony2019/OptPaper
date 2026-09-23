import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.prop_3
import Mathlib
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open Filter MeasureTheory

private theorem strong_tendsto_of_kadek_klee
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal))
    (hKadecKlee : ∀ (xSeq : ℕ → H) (z : H),
      Tendsto (fun k ↦ toWeakSpace ℝ H (xSeq k)) atTop
        (nhds (toWeakSpace ℝ H z)) →
      Tendsto (fun k ↦ (Phi (xSeq k) : EReal).toReal) atTop
        (nhds (Phi z : EReal).toReal) →
      Tendsto (fun k ↦ ‖xSeq k - z‖) atTop (nhds 0))
    (x : ℝ → H) (xInf : H)
    (hxWeak : Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
      (nhds (toWeakSpace ℝ H xInf)))
    (hPhiValue : Tendsto (fun t ↦ (Phi (x t) : EReal).toReal) atTop
      (nhds (Phi xInf : EReal).toReal)) :
    Tendsto x atTop (nhds xInf) := by
  apply Filter.tendsto_iff_seq_tendsto.2
  intro t ht
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact hKadecKlee (x ∘ t) xInf (by simpa [Function.comp_def] using hxWeak.comp ht)
    (by simpa [Function.comp_def] using hPhiValue.comp ht)

/-- Remark 2.19: under the Kadek--Klee property, every orbit considered in Proposition 2.16
converges strongly to a point of the solution set. -/
theorem kadek_klee_strong_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x v : ℝ → H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hlam : 0 < lam) (hmu : 0 < mu)
    (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xInf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xInf)))
    (hKadecKlee : ∀ (xSeq : ℕ → H) (z : H),
      Tendsto (fun k ↦ toWeakSpace ℝ H (xSeq k)) atTop
        (nhds (toWeakSpace ℝ H z)) →
      Tendsto (fun k ↦ (Phi (xSeq k) : EReal).toReal) atTop
        (nhds (Phi z : EReal).toReal) →
      Tendsto (fun k ↦ ‖xSeq k - z‖) atTop (nhds 0)) :
    ∃ xInf ∈ S, Tendsto x atTop (nhds xInf) := by
  let z : H := Classical.choose hS
  have hz : z ∈ S := Classical.choose_spec hS
  obtain ⟨_, _, xInf, hxInfS, hxWeak, hPhiValue⟩ :=
    proposition_2_16 S Phi hPhi B x v z lam mu beta hS hz hlam hmu hmu_lam hbeta
      hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2 horbit hsolution hdom hweak
  exact ⟨xInf, hxInfS,
    strong_tendsto_of_kadek_klee Phi hKadecKlee x xInf hxWeak hPhiValue⟩

end AbbasDynamical2015
