import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_5
import Mathlib
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open MeasureTheory

/-- The Bregman gap and its derivative (Lemma 2.13). -/
theorem bregman_gap_properties {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (x v : ℝ → H) (z : H)
    (hz : z ∈ S)
    (hsubgradient : ∀ t, 0 ≤ t →
      v t ∈ ERealFunction.subdifferential Phi (x t))
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ b : ℝ, 0 < b →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ b : ℝ, 0 < b →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt v (deriv v t) t)
    (hvL2 : ∀ b : ℝ, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b : ℝ, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (g : ℝ → ℝ)
    (hg : ∀ t, g t = (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
      inner ℝ (z - x t) (v t)) :
    (∀ t, 0 ≤ t → 0 ≤ g t) ∧
    ∀ᵐ t ∂volume.restrict (Set.Ici 0), deriv g t = inner ℝ (x t - z) (deriv v t) := by
  have hdomPhi := (ERealFunction.isProper_of_mem_gammaZero hPhi).2
  have hzdom : z ∈ ERealFunction.effectiveDomain Phi :=
    ERealFunction.SubdifferentiableAt.mem_effectiveDomain hdomPhi
      ⟨-B z, hsolution z hz⟩
  constructor
  · intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsubgradient t ht) hzdom
    rw [hg t]
    rw [real_inner_comm]
    linarith
  · have hlocal : ∀ n : ℕ,
        ∀ᵐ t ∂volume.restrict (Set.Icc 0 ((n : ℝ) + 1)),
          deriv g t = inner ℝ (x t - z) (deriv v t) := by
      intro n
      let T : ℝ := (n : ℝ) + 1
      have hT : 0 < T := by dsimp [T]; positivity
      have hchain := subgradient_chain_rule Phi hPhi x v T hT (hx_ac T hT)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hsubgradient t ht.1)
        (by
          intro t ht
          exact ERealFunction.SubdifferentiableAt.mem_effectiveDomain hdomPhi
            ⟨v t, hsubgradient t ht.1⟩)
        (hx_deriv T hT)
        (hvL2 T hT) (hdxL2 T hT)
      filter_upwards [hx_deriv T hT, hv_deriv T hT, hchain.2,
        ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae hchain.1.ae_differentiableAt] with
        t hxt hvt hphit ht hphid
      have hphi : HasDerivAt (fun s => (Phi (x s) : EReal).toReal)
          (deriv (fun s => (Phi (x s) : EReal).toReal) t) t :=
        (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
      have hin : HasDerivAt (fun s => inner ℝ (z - x s) (v s))
          (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
        convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1
        simp [inner_sub_left, real_inner_comm]
        ring
      have hraw : HasDerivAt (fun s => (Phi z : EReal).toReal -
          (Phi (x s) : EReal).toReal - inner ℝ (z - x s) (v s))
          (inner ℝ (x t - z) (deriv v t)) t := by
        have h := ((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi).sub hin
        convert h using 1
        simp only [hphit, sub_eq_add_neg, real_inner_comm]
        rw [show x t + -z = -(z + -x t) by abel, inner_neg_right]
        ring
      have hgeq : g = fun s => (Phi z : EReal).toReal -
          (Phi (x s) : EReal).toReal - inner ℝ (z - x s) (v s) := by
        funext s
        exact hg s
      rw [hgeq]
      exact hraw.deriv
    rw [show Set.Ici (0 : ℝ) = ⋃ n : ℕ, Set.Icc 0 ((n : ℝ) + 1) by
      ext t
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_ge t
        exact Set.mem_iUnion.2 ⟨n, ⟨ht, by linarith⟩⟩
      · intro ht
        rcases Set.mem_iUnion.1 ht with ⟨n, hn⟩
        exact hn.1]
    exact (MeasureTheory.ae_restrict_iUnion_iff _ _).2 hlocal

end AbbasDynamical2015
