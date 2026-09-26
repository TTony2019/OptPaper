import Foundation.Convex.InfimalConvolution
import Foundation.Convex.Conjugate
import Foundation.Convex.RelativeInterior
import Foundation.Convex.ArgminExistence

/-!
# Fenchel--Rockafellar duality

This file contains the primal and dual objectives, the algebraic conjugacy identities,
and the Attouch--Brezis proof of conjugate split attainment under the cone condition.
-/

open Set
open Filter
open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## The domain regularity bridge -/

private lemma effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, ?_⟩
  simpa [sub_eq_zero.mp hxy] using hy

/-- A strong-relative-interior domain-difference witness gives the nonempty-domain condition
needed to add two `Γ₀` functions. -/
theorem pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g)) :
    f + g ∈ Γ₀(H) :=
  pointwiseAdd_mem_gammaZero f g hf hg
    (effectiveDomain_inter_nonempty_of_zero_mem_sri_sub_effectiveDomain f g hsri)

/-! ## Owner definitions -/

/-- The pointwise primal objective for a pair of `]-∞,+∞]`-valued functions. -/
noncomputable def primalObjective (f g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  fun x ↦ (f x : EReal) + (g x : EReal)

/-- The primal optimal value, as an extended-real infimum. -/
noncomputable def primalOptimalValue (f g : H → Set.Ioi (⊥ : EReal)) : EReal :=
  ⨅ x : H, primalObjective f g x

/-- The same-space Fenchel dual objective. -/
noncomputable def fenchelDualObjective (f g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  fun u ↦ f.asEReal∗ (-u) + g.asEReal∗ u

@[simp] theorem primalObjective_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    primalObjective f g x = (f x : EReal) + (g x : EReal) :=
  rfl

@[simp] theorem fenchelDualObjective_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (u : H) :
    fenchelDualObjective f g u = f.asEReal∗ (-u) + g.asEReal∗ u :=
  rfl

theorem primalOptimalValue_eq_iInf_primalObjective
    (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g = ⨅ x : H, primalObjective f g x :=
  rfl

/-! ## The unconditional conjugate inequality -/

private lemma affine_defect_add_split
    (f g : H → Set.Ioi (⊥ : EReal)) (x y z : H) :
    (((⟪x, y + z⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g x : EReal))) =
      ((((⟪x, y⟫_ℝ : ℝ) : EReal) - (f x : EReal)) +
        (((⟪x, z⟫_ℝ : ℝ) : EReal) - (g x : EReal))) := by
  have hf_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hg_bot : (g x : EReal) ≠ ⊥ := ne_of_gt (g x).2
  have hinner :
      (((⟪x, y + z⟫_ℝ : ℝ) : EReal)) =
        (((⟪x, y⟫_ℝ : ℝ) : EReal) + ((⟪x, z⟫_ℝ : ℝ) : EReal)) := by
    simp [inner_add_right]
  rw [hinner, sub_eq_add_neg, EReal.neg_add (.inl hf_bot) (.inr hg_bot),
    sub_eq_add_neg, sub_eq_add_neg]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma ereal_realCast_sub_iInf_eq_iSup_sub
    {ι : Sort*} (a : ℝ) (φ : ι → EReal) :
    ((a : EReal) - ⨅ i, φ i) = ⨆ i, ((a : EReal) - φ i) := by
  calc
    ((a : EReal) - ⨅ i, φ i) = ((a : EReal) + -(⨅ i, φ i)) := by
      rw [sub_eq_add_neg]
    _ = ((a : EReal) + ⨆ i, -φ i) := by
      congr 1
      exact OrderIso.map_iInf EReal.negOrderIso φ
    _ = ((⨆ i, -φ i) + (a : EReal)) := by rw [add_comm]
    _ = ⨆ i, (-φ i) + (a : EReal) := by
      apply le_antisymm
      · refine EReal.add_le_of_forall_lt ?_
        intro s hs b hb
        rcases lt_iSup_iff.mp hs with ⟨i, hi⟩
        exact (EReal.add_lt_add hi hb).le.trans
          (le_iSup (fun i ↦ (-φ i) + (a : EReal)) i)
      · refine iSup_le fun i ↦ add_le_add (le_iSup (fun j ↦ -φ j) i) le_rfl
    _ = ⨆ i, ((a : EReal) - φ i) := by
      refine iSup_congr fun i ↦ ?_
      simp [sub_eq_add_neg, add_comm]

private lemma iSup_iSup_add_eq_add_iSup
    {ι κ : Sort*} (a : ι → EReal) (b : κ → EReal) :
    (⨆ i, ⨆ j, a i + b j) = (⨆ i, a i) + (⨆ j, b j) := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    refine iSup_le fun j ↦ ?_
    exact add_le_add (le_iSup a i) (le_iSup b j)
  · refine EReal.add_le_of_forall_lt ?_
    intro a' ha b' hb
    rcases lt_iSup_iff.mp ha with ⟨i, hi⟩
    rcases lt_iSup_iff.mp hb with ⟨j, hj⟩
    exact (EReal.add_lt_add hi hj).le.trans <| le_iSup_of_le i <| le_iSup_of_le j le_rfl

private lemma infimal_convolution_affine_defect_split
    (f g : H → Set.Ioi (⊥ : EReal)) (y z u : H) :
    (((⟪z + y, u⟫_ℝ : ℝ) : EReal) - ((f y : EReal) + (g z : EReal))) =
      ((((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
        (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgz_bot : (g z : EReal) ≠ ⊥ := ne_of_gt (g z).2
  have hinner :
      (((⟪z + y, u⟫_ℝ : ℝ) : EReal)) =
        (((⟪y, u⟫_ℝ : ℝ) : EReal) + ((⟪z, u⟫_ℝ : ℝ) : EReal)) := by
    simpa [add_comm] using congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) (inner_add_left z y u)
  rw [hinner, sub_eq_add_neg, EReal.neg_add (.inl hfy_bot) (.inr hgz_bot),
    sub_eq_add_neg, sub_eq_add_neg]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The conjugate of an infimal convolution is the pointwise sum of the conjugates. -/
theorem conjugate_infimalConvolution_eq
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f □ g)∗ = f.asEReal∗ + g.asEReal∗ := by
  ext u
  rw [conjugate_apply, Pi.add_apply, conjugate_apply, conjugate_apply]
  calc
    (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (f □ g) x)) =
        (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
          ⨅ y : H, ((f y : EReal) + (g (x - y) : EReal)))) := by
            refine iSup_congr fun x ↦ ?_
            exact congrArg
              (fun t : EReal ↦ (((⟪x, u⟫_ℝ : ℝ) : EReal) - t))
              (infimalConvolution_apply f.asEReal g.asEReal x)
    _ = ⨆ x : H, ⨆ y : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
          ((f y : EReal) + (g (x - y) : EReal))) := by
            refine iSup_congr fun x ↦ ?_
            simpa using ereal_realCast_sub_iInf_eq_iSup_sub
              (a := ⟪x, u⟫_ℝ)
              (φ := fun y : H ↦ (f y : EReal) + (g (x - y) : EReal))
    _ = ⨆ y : H, ⨆ z : H, ((((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
          (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
            rw [iSup_comm]
            refine iSup_congr fun y ↦ ?_
            calc
              (⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) -
                  ((f y : EReal) + (g (x - y) : EReal)))) =
                  ⨆ z : H, (((⟪z + y, u⟫_ℝ : ℝ) : EReal) -
                    ((f y : EReal) + (g z : EReal))) := by
                      exact ((Equiv.addRight y).surjective.iSup_congr (Equiv.addRight y)
                        (fun z ↦ by simp)).symm
              _ = ⨆ z : H, ((((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)) +
                    (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal))) := by
                      refine iSup_congr fun z ↦ ?_
                      exact infimal_convolution_affine_defect_split f g y z u
    _ = (⨆ y : H, (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal))) +
        ⨆ z : H, (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal)) := by
          exact iSup_iSup_add_eq_add_iSup
            (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal)))
            (fun z : H ↦ (((⟪z, u⟫_ℝ : ℝ) : EReal) - (g z : EReal)))

/-! ## The unconditional biconjugate bridge -/

section GammaZeroBiconjugate

variable [CompleteSpace H]

/-- The conjugate of the infimal convolution of two packaged `Γ₀` conjugates is the original
pointwise sum.  This is the algebraic Fenchel--Moreau identity and does not use the domain
regularity hypothesis. -/
theorem conjugate_gammaZeroConjugate_infimalConvolution_eq_pointwiseAdd
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗ = (f + g).asEReal := by
  have hconj_f : (gammaZeroConjugate f hf).asEReal = f.asEReal∗ := by
    funext u
    simp
  have hconj_g : (gammaZeroConjugate g hg).asEReal = g.asEReal∗ := by
    funext u
    simp
  calc
    (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗ =
        (gammaZeroConjugate f hf).asEReal∗ +
          (gammaZeroConjugate g hg).asEReal∗ :=
      conjugate_infimalConvolution_eq (gammaZeroConjugate f hf) (gammaZeroConjugate g hg)
    _ = f.asEReal∗∗ + g.asEReal∗∗ := by rw [hconj_f, hconj_g]
    _ = f.asEReal + g.asEReal := by
      rw [biconjugate_eq_of_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hg]
    _ = (f + g).asEReal := by
      funext x
      simp [Function.asEReal_apply]

/-- Equivalently, the conjugate of a pointwise sum is the biconjugate of the infimal convolution
of its packaged conjugates. -/
theorem pointwiseAdd_conjugate_eq_biconjugate_gammaZeroConjugate_infimalConvolution
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (f + g).asEReal∗ =
      (gammaZeroConjugate f hf □ gammaZeroConjugate g hg)∗∗ := by
  simpa using congrArg conjugate
    (conjugate_gammaZeroConjugate_infimalConvolution_eq_pointwiseAdd f g hf hg).symm

end GammaZeroBiconjugate

/-- The Fenchel conjugate of a pointwise sum is bounded above by the infimal convolution
of the two conjugates. -/
theorem conjugate_add_le_infimalConvolution_conjugate
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f.asEReal + g.asEReal)∗ ≤ f.asEReal∗ □ g.asEReal∗ := by
  intro u
  rw [conjugate_apply, infimalConvolution_apply]
  refine le_iInf fun y ↦ ?_
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - ((f x : EReal) + (g x : EReal))) =
        ((((⟪x, y⟫_ℝ : ℝ) : EReal) - (f x : EReal)) +
          (((⟪x, u - y⟫_ℝ : ℝ) : EReal) - (g x : EReal))) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        affine_defect_add_split f g x y (u - y)
    _ ≤ f.asEReal∗ y + g.asEReal∗ (u - y) := by
      refine add_le_add ?_ ?_
      · rw [conjugate_apply]
        exact le_iSup (fun z : H ↦ (((⟪z, y⟫_ℝ : ℝ) : EReal) - (f z : EReal))) x
      · rw [conjugate_apply]
        exact le_iSup (fun z : H ↦ (((⟪z, u - y⟫_ℝ : ℝ) : EReal) - (g z : EReal))) x

/-! ## The zero-slice and exactness bridges -/

/-- The zero slice of the conjugate infimal convolution is the infimum of the Fenchel dual
objective, after the sign change `u = -y`. -/
theorem sInf_range_fenchelDualObjective_eq_infimalConvolution_conjugates_zero
    (f g : H → Set.Ioi (⊥ : EReal)) :
    sInf (Set.range (fenchelDualObjective f g)) =
      (f.asEReal∗ □ g.asEReal∗) (0 : H) := by
  rw [sInf_range, infimalConvolution_apply]
  calc
    (⨅ u : H, fenchelDualObjective f g u) =
        ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (-y) := by
          exact (Equiv.neg H).iInf_congr fun y ↦ by
            simp [fenchelDualObjective_apply]
    _ = ⨅ y : H, f.asEReal∗ y + g.asEReal∗ (0 - y) := by
      refine iInf_congr fun y ↦ ?_
      simp

/-- Exactness at zero supplies a minimizer of the Fenchel dual objective. -/
theorem argmin_fenchelDualObjective_of_exactAt_zero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H))
    (hexact0 :
      infimalConvolution.ExactAt
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (0 : H)) :
    ∃ u ∈ Argmin (fenchelDualObjective f g),
      (f.asEReal∗ □ g.asEReal∗) (0 : H) = fenchelDualObjective f g u := by
  rcases hexact0 with ⟨y, hy⟩
  refine ⟨-y, ?_, ?_⟩
  · rw [mem_argmin_iff_eq_sInf]
    calc
      fenchelDualObjective f g (-y) = (f.asEReal∗ □ g.asEReal∗) (0 : H) := by
        simpa [fenchelDualObjective_apply, gammaZeroConjugate_apply] using hy.symm
      _ = sInf (Set.range (fenchelDualObjective f g)) := by
        symm
        exact sInf_range_fenchelDualObjective_eq_infimalConvolution_conjugates_zero f g
  · simpa [fenchelDualObjective_apply, gammaZeroConjugate_apply] using hy

/-- A split attaining the conjugate of the primal sum at zero is exactly an attained zero slice
of the conjugate infimal convolution.  The reverse inequality is the unconditional Fenchel
weak-duality bound. -/
theorem infimalConvolution_exactAt_zero_of_split_attainment_at_zero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hattain0 : ∃ y : H,
      (f + g).asEReal∗ (0 : H) = f.asEReal∗ y + g.asEReal∗ ((0 : H) - y)) :
    infimalConvolution.ExactAt
      (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) (0 : H) := by
  rcases hattain0 with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  apply le_antisymm
  · rw [infimalConvolution_apply]
    exact iInf_le (fun z : H ↦ f.asEReal∗ z + g.asEReal∗ ((0 : H) - z)) y
  · have hweak :
        (f + g).asEReal∗ (0 : H) ≤
          (f.asEReal∗ □ g.asEReal∗) (0 : H) := by
      simpa [Function.asEReal_apply] using
        (conjugate_add_le_infimalConvolution_conjugate (H := H) f g (0 : H))
    have hweak' :
        f.asEReal∗ y + g.asEReal∗ ((0 : H) - y) ≤
          (f.asEReal∗ □ g.asEReal∗) (0 : H) := by
      rw [← hy]
      exact hweak
    simpa [gammaZeroConjugate_apply] using hweak'

/-- Evaluating the conjugate of the primal pointwise sum at zero gives the negative primal
optimal value. -/
theorem pointwiseAdd_conjugate_zero_eq_neg_primalOptimalValue
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f + g).asEReal∗ (0 : H) = -primalOptimalValue f g := by
  rw [conjugate_apply]
  simp only [inner_zero_right, EReal.coe_zero, zero_sub]
  change (⨆ x : H, -primalObjective f g x) = -primalOptimalValue f g
  rw [primalOptimalValue_eq_iInf_primalObjective]
  exact (OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ primalObjective f g x)).symm

/-! ## The bounded-level-set estimate used by the textbook proof

The next estimate is the elementary affine calculation behind the
Attouch--Brézis argument.  It is kept separate from the attainment theorem so
that the later weak-compactness step can use it without unfolding conjugates
again.
-/

private lemma conjugate_sum_level_inner_le
    (f g : H → Set.Ioi (⊥ : EReal)) {u y x z : H} {ξ : ℝ}
    (hx : x ∈ effectiveDomain f) (hz : z ∈ effectiveDomain g)
    (hy : f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal)) :
    ⟪x - z, y⟫_ℝ ≤
      ξ + (f x : EReal).toReal + (g z : EReal).toReal - ⟪z, u⟫_ℝ := by
  have hfx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hgz_top : g.asEReal z ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hfx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
  have hgz_bot : g.asEReal z ≠ ⊥ := ne_of_gt (g z).2
  have hfy :=
    le_iSup (fun w : H ↦ (((⟪w, y⟫_ℝ : ℝ) : EReal) - f.asEReal w)) x
  have hgy :=
    le_iSup (fun w : H ↦ (((⟪w, u - y⟫_ℝ : ℝ) : EReal) - g.asEReal w)) z
  have hfy' : (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x) ≤ f.asEReal∗ y := by
    simpa [conjugate_apply] using hfy
  have hgy' : (((⟪z, u - y⟫_ℝ : ℝ) : EReal) - g.asEReal z) ≤ g.asEReal∗ (u - y) := by
    simpa [conjugate_apply] using hgy
  have hsum :
      (((⟪x, y⟫_ℝ + ⟪z, u - y⟫_ℝ -
        (f x : EReal).toReal - (g z : EReal).toReal : ℝ) : EReal)) ≤ (ξ : EReal) := by
    have hsum' := add_le_add hfy' hgy'
    have hsum'' := hsum'.trans hy
    rw [← EReal.coe_toReal hfx_top hfx_bot,
      ← EReal.coe_toReal hgz_top hgz_bot] at hsum''
    simpa [sub_eq_add_neg, EReal.coe_add, EReal.coe_sub,
      add_assoc, add_left_comm, add_comm] using hsum''
  have hsum_real :
      ⟪x, y⟫_ℝ + ⟪z, u - y⟫_ℝ -
        (f x : EReal).toReal - (g z : EReal).toReal ≤ ξ :=
    EReal.coe_le_coe_iff.mp hsum
  rw [inner_sub_left]
  rw [inner_sub_right] at hsum_real
  linarith

/-! ## The textbook level-set bound

The cone hypothesis lets every vector in the closed span of the domain difference be
represented, in both signs, by a positive multiple of a domain difference.  The preceding
affine estimate then bounds every dual sublevel set in each such direction.
-/

theorem levelSet_pointwise_bound_on_closedSpan
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (u : H) (ξ : ℝ)
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    ∀ s ∈ ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H),
      ∃ C : ℝ, ∀ y : H,
        f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal) → |⟪s, y⟫_ℝ| ≤ C := by
  let D : Set H := effectiveDomain f - effectiveDomain g
  let S : Set H := ((Submodule.span ℝ D).topologicalClosure : Set H)
  have hD_nonempty : D.Nonempty := by
    rcases hf.2.nonempty with ⟨x, hx⟩
    rcases hg.2.nonempty with ⟨z, hz⟩
    exact ⟨x - z, Set.mem_sub.mpr ⟨x, hx, z, hz, rfl⟩⟩
  have hD_conv : Convex ℝ D := by
    dsimp [D]
    exact hf.2.convex_effectiveDomain.sub hg.2.convex_effectiveDomain
  intro s hs
  have hs_cone : s ∈ Set.cone D := by
    rw [hcone]
    simpa [S] using hs
  have hs_rep : ∃ c : ℝ, 0 < c ∧ ∃ d ∈ D, c • d = s := by
    have hs' : s ∈ (hD_conv.toCone D : Set H) := by
      simpa [Set.cone_def, convexCone_hull_eq_toCone hD_conv] using hs_cone
    exact hD_conv.mem_toCone.mp hs'
  have hneg_cone : -s ∈ Set.cone D := by
    rw [hcone]
    have hs' : s ∈ ((Submodule.span ℝ D).topologicalClosure : Set H) := by
      simpa [S] using hs
    exact Submodule.neg_mem _ hs'
  have hneg_rep : ∃ c : ℝ, 0 < c ∧ ∃ d ∈ D, c • d = -s := by
    have hs' : -s ∈ (hD_conv.toCone D : Set H) := by
      simpa [Set.cone_def, convexCone_hull_eq_toCone hD_conv] using hneg_cone
    exact hD_conv.mem_toCone.mp hs'
  rcases hs_rep with ⟨c, hc, d, hd, hds⟩
  rcases Set.mem_sub.mp hd with ⟨x, hx, z, hz, rfl⟩
  rcases hneg_rep with ⟨c', hc', d', hd', hds'⟩
  rcases Set.mem_sub.mp hd' with ⟨x', hx', z', hz', rfl⟩
  let C₁ : ℝ := c * (ξ + (f x : EReal).toReal + (g z : EReal).toReal - ⟪z, u⟫_ℝ)
  let C₂ : ℝ := c' * (ξ + (f x' : EReal).toReal + (g z' : EReal).toReal - ⟪z', u⟫_ℝ)
  refine ⟨max |C₁| |C₂|, ?_⟩
  intro y hy
  have h₁ := conjugate_sum_level_inner_le f g hx hz hy
  have h₂ := conjugate_sum_level_inner_le f g hx' hz' hy
  have hy₁ : ⟪s, y⟫_ℝ ≤ C₁ := by
    rw [← hds]
    rw [real_inner_smul_left]
    dsimp [C₁]
    gcongr
  have hy₂ : -⟪s, y⟫_ℝ ≤ C₂ := by
    calc
      -⟪s, y⟫_ℝ = ⟪-s, y⟫_ℝ := by simp
      _ = ⟪c' • (x' - z'), y⟫_ℝ := by rw [hds']
      _ = c' * ⟪x' - z', y⟫_ℝ := by rw [real_inner_smul_left]
      _ ≤ C₂ := by
        dsimp [C₂]
        gcongr
  apply (abs_le).2
  constructor
  · have hlow₀ : -max |C₁| |C₂| ≤ -|C₂| :=
      neg_le_neg (le_max_right |C₁| |C₂|)
    have hlow₁ : -|C₂| ≤ -C₂ := neg_le_neg (le_abs_self C₂)
    have hle : -C₂ ≤ ⟪s, y⟫_ℝ := by linarith
    exact hlow₀.trans (hlow₁.trans hle)
  · exact hy₁.trans ((le_abs_self C₁).trans (le_max_left |C₁| |C₂|))

/-! ## Orthogonal-slice invariance

The cone estimate controls only the closed span of the domain difference.  The
orthogonal complement has to be removed before weak compactness can be used.
The following elementary calculation is the textbook translation argument in
the present extended-real notation.
-/

private lemma iSup_add_real_const
    {ι : Sort*} (a : ι → EReal) (c : ℝ) :
    (⨆ i, a i + (c : EReal)) = (⨆ i, a i) + (c : EReal) := by
  calc
    (⨆ i, a i + (c : EReal)) =
        ⨆ i, ⨆ _ : Unit, a i + (c : EReal) := by
          refine iSup_congr fun i ↦ ?_
          simp
    _ = (⨆ i, a i) + (⨆ _ : Unit, (c : EReal)) := by
      exact iSup_iSup_add_eq_add_iSup a (fun _ : Unit ↦ (c : EReal))
    _ = (⨆ i, a i) + (c : EReal) := by simp

private lemma conjugate_add_vector_eq_add_of_inner_const_on_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (w : H) (c : ℝ) (y : H)
    (hc : ∀ x ∈ effectiveDomain f, ⟪x, w⟫_ℝ = c) :
    f.asEReal∗ (y + w) = f.asEReal∗ y + (c : EReal) := by
  rw [conjugate_apply, conjugate_apply]
  calc
    (⨆ x : H, (((⟪x, y + w⟫_ℝ : ℝ) : EReal) - f.asEReal x)) =
        ⨆ x : H, (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x) + (c : EReal) := by
      refine iSup_congr fun x ↦ ?_
      by_cases hx : x ∈ effectiveDomain f
      · have hxtop : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
        have hxeq : f.asEReal x = ((f x : EReal)) := rfl
        have hinner : ⟪x, y + w⟫_ℝ = ⟪x, y⟫_ℝ + c := by
          rw [inner_add_right, hc x hx]
        rw [hinner, EReal.coe_add, hxeq]
        rw [show (((⟪x, y⟫_ℝ : ℝ) : EReal) + (c : EReal)) - f.asEReal x =
          ((((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x) + (c : EReal)) by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]]
      · have hxtop : f.asEReal x = ⊤ := by
          apply le_antisymm le_top
          exact not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx)
        simp [hxtop]
    _ = (⨆ x : H, (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x)) + (c : EReal) :=
      iSup_add_real_const (fun x : H ↦
        (((⟪x, y⟫_ℝ : ℝ) : EReal) - f.asEReal x)) c

theorem fenchelDualObjective_add_orthogonal_eq
    (f g : H → Set.Ioi (⊥ : EReal))
    {D : Set H} {S : Submodule ℝ H} {u w y : H}
    (hD : D = effectiveDomain f - effectiveDomain g)
    (hS : (S : Set H) = ((Submodule.span ℝ D).topologicalClosure : Set H))
    (hw : w ∈ Sᗮ)
    (hfd : (effectiveDomain f).Nonempty)
    (hgd : (effectiveDomain g).Nonempty) :
    f.asEReal∗ (y + w) + g.asEReal∗ (u - (y + w)) =
      f.asEReal∗ y + g.asEReal∗ (u - y) := by
  rcases hfd with ⟨x₀, hx₀⟩
  rcases hgd with ⟨z₀, hz₀⟩
  have hdiff_f (x : H) (hx : x ∈ effectiveDomain f) :
      x - x₀ ∈ (S : Set H) := by
    have h₁ : x - z₀ ∈ (S : Set H) := by
      rw [hS]
      exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
        (s := D) (subset_closure (by
          rw [hD]
          exact Set.mem_sub.mpr ⟨x, hx, z₀, hz₀, rfl⟩))
    have h₂ : x₀ - z₀ ∈ (S : Set H) := by
      rw [hS]
      exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
        (s := D) (subset_closure (by
          rw [hD]
          exact Set.mem_sub.mpr ⟨x₀, hx₀, z₀, hz₀, rfl⟩))
    convert S.sub_mem h₁ h₂ using 1 <;> abel
  have hdiff_g (z : H) (hz : z ∈ effectiveDomain g) :
      z - z₀ ∈ (S : Set H) := by
    have h₁ : x₀ - z₀ ∈ (S : Set H) := by
      rw [hS]
      exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
        (s := D) (subset_closure (by
          rw [hD]
          exact Set.mem_sub.mpr ⟨x₀, hx₀, z₀, hz₀, rfl⟩))
    have h₂ : x₀ - z ∈ (S : Set H) := by
      rw [hS]
      exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
        (s := D) (subset_closure (by
          rw [hD]
          exact Set.mem_sub.mpr ⟨x₀, hx₀, z, hz, rfl⟩))
    convert S.sub_mem h₁ h₂ using 1 <;> abel
  have horth_f (x : H) (hx : x ∈ effectiveDomain f) :
      ⟪x, w⟫_ℝ = ⟪x₀, w⟫_ℝ := by
    have hzero : ⟪x - x₀, w⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hdiff_f x hx) hw
    rw [inner_sub_left] at hzero
    linarith
  have horth_g (z : H) (hz : z ∈ effectiveDomain g) :
      ⟪z, w⟫_ℝ = ⟪z₀, w⟫_ℝ := by
    have hzero : ⟪z - z₀, w⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hdiff_g z hz) hw
    rw [inner_sub_left] at hzero
    linarith
  have hfshift : f.asEReal∗ (y + w) =
      f.asEReal∗ y + (⟪x₀, w⟫_ℝ : EReal) := by
    exact conjugate_add_vector_eq_add_of_inner_const_on_effectiveDomain f w
      ⟪x₀, w⟫_ℝ y horth_f
  have hgshift : g.asEReal∗ (u - (y + w)) =
      g.asEReal∗ (u - y) + ((-⟪z₀, w⟫_ℝ) : EReal) := by
    have harg : u - (y + w) = (u - y) + (-w) := by abel
    rw [harg]
    have hconst : ∀ z ∈ effectiveDomain g, ⟪z, -w⟫_ℝ = -⟪z₀, w⟫_ℝ := by
      intro z hz
      rw [inner_neg_right, horth_g z hz]
    simpa using conjugate_add_vector_eq_add_of_inner_const_on_effectiveDomain
      g (-w) (-⟪z₀, w⟫_ℝ) (u - y) hconst
  rw [hfshift, hgshift]
  have hcancel : ⟪x₀, w⟫_ℝ + -⟪z₀, w⟫_ℝ = 0 := by
    have hzero : ⟪x₀ - z₀, w⟫_ℝ = 0 := by
      have hmem : x₀ - z₀ ∈ (S : Set H) := by
        rw [hS]
        exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
          (s := D) (subset_closure (by
            rw [hD]
            exact Set.mem_sub.mpr ⟨x₀, hx₀, z₀, hz₀, rfl⟩))
      exact Submodule.inner_right_of_mem_orthogonal (K := S) hmem hw
    rw [inner_sub_left] at hzero
    linarith
  calc
    (f.asEReal∗ y + (⟪x₀, w⟫_ℝ : EReal)) +
        (g.asEReal∗ (u - y) + (-⟪z₀, w⟫_ℝ : EReal)) =
        (f.asEReal∗ y + g.asEReal∗ (u - y)) +
          ((⟪x₀, w⟫_ℝ : EReal) + (-⟪z₀, w⟫_ℝ : EReal)) := by
            ac_rfl
    _ = f.asEReal∗ y + g.asEReal∗ (u - y) := by
      have hcast : (⟪x₀, w⟫_ℝ : EReal) + (-⟪z₀, w⟫_ℝ : EReal) =
          ((⟪x₀, w⟫_ℝ + -⟪z₀, w⟫_ℝ : ℝ) : EReal) := by
        rw [← EReal.coe_neg, ← EReal.coe_add]
      rw [hcast, hcancel]
      simp

theorem closedSpan_projection_norm_bound_on_fenchelDual_levelSet
    {S : Submodule ℝ H} [S.HasOrthogonalProjection] [CompleteSpace S]
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (u : H) (ξ : ℝ)
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H))
    (hS : (S : Set H) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    ∃ C : ℝ, ∀ y : H,
      f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal) →
      ‖S.starProjection y‖ ≤ C := by
  let Y : Type u := {y : H // f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal)}
  let T : Y → S →L[ℝ] ℝ := fun y ↦
    (innerSL ℝ y.1).comp S.subtypeL
  have hpointwise : ∀ s : S, ∃ C : ℝ, ∀ y : Y, ‖T y s‖ ≤ C := by
    intro s
    have hs : (s : H) ∈
        ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H) := by
      rw [← hS]
      exact s.property
    rcases levelSet_pointwise_bound_on_closedSpan f g hf hg u ξ hcone
      (s : H) hs with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro y
    have hinner : ⟪(s : H), y.1⟫_ℝ = ⟪y.1, (s : H)⟫_ℝ := real_inner_comm _ _
    have hbound := hC y.1 y.2
    rw [show T y s = ⟪y.1, (s : H)⟫_ℝ by
      change ⟪y.1, (s : H)⟫_ℝ = ⟪y.1, (s : H)⟫_ℝ
      rfl]
    rw [← hinner]
    simpa [Real.norm_eq_abs] using hbound
  obtain ⟨C, hC⟩ :=
    uniform_boundedness_principle (ι := Y) (𝓧 := S) (𝓨 := ℝ) (T := T) hpointwise
  let C₀ : ℝ := max C 0
  have hC₀ : ∀ y : Y, ‖T y‖ ≤ C₀ := by
    intro y
    exact (hC y).trans (le_max_left C 0)
  have hC₀_nonneg : 0 ≤ C₀ := le_max_right C 0
  refine ⟨C₀, ?_⟩
  intro y hy
  let p : H := S.starProjection y
  have hpS : p ∈ (S : Set H) := S.starProjection_apply_mem y
  let ps : S := ⟨p, hpS⟩
  have hTp : ‖T ⟨y, hy⟩ ps‖ ≤ C₀ * ‖ps‖ := by
    calc
      ‖T ⟨y, hy⟩ ps‖ ≤ ‖T ⟨y, hy⟩‖ * ‖ps‖ := (T ⟨y, hy⟩).le_opNorm ps
      _ ≤ C₀ * ‖ps‖ := by
        gcongr
        exact hC₀ ⟨y, hy⟩
  have hproj_orth : y - p ∈ Sᗮ := S.sub_starProjection_mem_orthogonal y
  have hinner_eq : ⟪y, p⟫_ℝ = ‖p‖ ^ 2 := by
    have hz : ⟪y - p, p⟫_ℝ = 0 := by
      exact Submodule.inner_left_of_mem_orthogonal hpS hproj_orth
    rw [inner_sub_left] at hz
    calc
      ⟪y, p⟫_ℝ = ⟪p, p⟫_ℝ := by linarith
      _ = ‖p‖ ^ 2 := real_inner_self_eq_norm_sq p
  have hnorm_sq : ‖T ⟨y, hy⟩ ps‖ = ‖p‖ ^ 2 := by
    rw [show T ⟨y, hy⟩ ps = ⟪y, p⟫_ℝ by
      simp [T, ps, p, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply], hinner_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hps_norm : ‖ps‖ = ‖p‖ := rfl
  have hnorm_le : ‖p‖ ^ 2 ≤ C₀ * ‖p‖ := by
    rw [hnorm_sq, hps_norm] at hTp
    exact hTp
  have hp_nonneg : 0 ≤ ‖p‖ := norm_nonneg _
  have hp_le : ‖p‖ ≤ C₀ := by
    nlinarith [sq_nonneg ‖p‖]
  exact hp_le

/-- Every dual split has an equivalent representative in the closed span of the domain
difference.  On a fixed finite sublevel set these representatives are uniformly bounded. -/
theorem exists_bounded_closedSpan_representative_on_fenchelDual_levelSet
    {S : Submodule ℝ H} [S.HasOrthogonalProjection] [CompleteSpace S]
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (u : H) (ξ : ℝ)
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H))
    (hS : (S : Set H) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    ∃ C : ℝ, ∀ y : H,
      f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal) →
      ∃ z : H, z ∈ S ∧ ‖z‖ ≤ C ∧
        f.asEReal∗ z + g.asEReal∗ (u - z) =
          f.asEReal∗ y + g.asEReal∗ (u - y) := by
  obtain ⟨C, hC⟩ :=
    closedSpan_projection_norm_bound_on_fenchelDual_levelSet
      f g hf hg u ξ hcone hS
  refine ⟨C, fun y hy ↦ ⟨S.starProjection y, S.starProjection_apply_mem y,
    hC y hy, ?_⟩⟩
  have hw : y - S.starProjection y ∈ Sᗮ :=
    S.sub_starProjection_mem_orthogonal y
  have hshift := fenchelDualObjective_add_orthogonal_eq f g
    (D := effectiveDomain f - effectiveDomain g) (S := S)
    (u := u) (y := S.starProjection y) (w := y - S.starProjection y)
    rfl hS hw hf.2.nonempty hg.2.nonempty
  simpa using hshift.symm

/-- The split objective is lower semicontinuous in the splitting variable. -/
theorem lowerSemicontinuous_conjugate_split_objective
    (f g : H → Set.Ioi (⊥ : EReal)) (u : H) :
    LowerSemicontinuous
      (fun y : H ↦ f.asEReal∗ y + g.asEReal∗ (u - y)) := by
  have hf : LowerSemicontinuous f.asEReal∗ :=
    (mem_gamma_iff f.asEReal∗).mp (conjugate_mem_gamma f.asEReal) |>.2
  have hg : LowerSemicontinuous (fun y : H ↦ g.asEReal∗ (u - y)) := by
    have hg' : LowerSemicontinuous g.asEReal∗ :=
      (mem_gamma_iff g.asEReal∗).mp (conjugate_mem_gamma g.asEReal) |>.2
    exact hg'.comp (continuous_const.sub continuous_id)
  rw [lowerSemicontinuous_iff_le_liminf]
  intro y
  calc
    f.asEReal∗ y + g.asEReal∗ (u - y) ≤
        Filter.liminf f.asEReal∗ (nhds y) +
          Filter.liminf (fun z : H ↦ g.asEReal∗ (u - z)) (nhds y) :=
      add_le_add (hf.le_liminf y) (hg.le_liminf y)
    _ ≤ Filter.liminf
        (fun z : H ↦ f.asEReal∗ z + g.asEReal∗ (u - z)) (nhds y) := by
      simpa using (EReal.le_liminf_add :
        Filter.liminf f.asEReal∗ (nhds y) +
          Filter.liminf (fun z : H ↦ g.asEReal∗ (u - z)) (nhds y) ≤
            Filter.liminf
              (f.asEReal∗ + fun z : H ↦ g.asEReal∗ (u - z)) (nhds y))

/-- The split objective is convex in the splitting variable. -/
theorem isConvex_conjugate_split_objective
    (f g : H → Set.Ioi (⊥ : EReal)) (u : H) :
    IsConvex (fun y : H ↦ f.asEReal∗ y + g.asEReal∗ (u - y)) := by
  have hf : IsConvex f.asEReal∗ :=
    (mem_gamma_iff f.asEReal∗).mp (conjugate_mem_gamma f.asEReal) |>.1
  have hg : IsConvex g.asEReal∗ :=
    (mem_gamma_iff g.asEReal∗).mp (conjugate_mem_gamma g.asEReal) |>.1
  intro x y a ha0 ha1
  have harg : u - (a • x + (1 - a) • y) =
      a • (u - x) + (1 - a) • (u - y) := by
    rw [smul_sub, smul_sub, ← add_sub_assoc]
    have hsmul : a • u + (1 - a) • u = u := by
      rw [← add_smul]
      simp
    module
  change f.asEReal∗ (a • x + (1 - a) • y) +
      g.asEReal∗ (u - (a • x + (1 - a) • y)) ≤
      (a : EReal) * (f.asEReal∗ x + g.asEReal∗ (u - x)) +
        ((1 - a : ℝ) : EReal) * (f.asEReal∗ y + g.asEReal∗ (u - y))
  rw [harg]
  calc
    f.asEReal∗ (a • x + (1 - a) • y) +
        g.asEReal∗ (a • (u - x) + (1 - a) • (u - y)) ≤
        ((a : EReal) * f.asEReal∗ x + ((1 - a : ℝ) : EReal) * f.asEReal∗ y) +
          ((a : EReal) * g.asEReal∗ (u - x) +
            ((1 - a : ℝ) : EReal) * g.asEReal∗ (u - y)) :=
      add_le_add (hf ha0 ha1) (hg ha0 ha1)
    _ = (a : EReal) * (f.asEReal∗ x + g.asEReal∗ (u - x)) +
          ((1 - a : ℝ) : EReal) *
            (f.asEReal∗ y + g.asEReal∗ (u - y)) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr ha0) (EReal.coe_ne_top a),
        EReal.left_distrib_of_nonneg_of_ne_top
          (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha1))
          (EReal.coe_ne_top (1 - a))]
      simp [add_assoc, add_left_comm, add_comm]

/-! ## Closedness of the infimal convolution

The following is the sequential form of the textbook closedness argument.  The
only compactness input is the bounded representative lemma above; all values
are kept in the original EReal notation.
-/

private lemma quasiconvexOn_univ_of_isConvex_local
    {F : H → EReal} (hF : IsConvex F) :
    QuasiconvexOn ℝ Set.univ F := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 0 ≤ b := by linarith
  have hb_eq : b = 1 - a := by linarith
  have hconv := hF (x := x) (y := y) (a := a) ha0 (by linarith : a ≤ 1)
  have hmax : (a : EReal) * F x + (b : EReal) * F y ≤ max (F x) (F y) := by
    have haE : (0 : EReal) ≤ (a : EReal) := by exact_mod_cast ha0
    have hbE : (0 : EReal) ≤ (b : EReal) := by exact_mod_cast ha1
    have habE : (a : EReal) + (b : EReal) = 1 := by
      rw [← EReal.coe_add, hab, EReal.coe_one]
    calc
      (a : EReal) * F x + (b : EReal) * F y ≤
          (a : EReal) * max (F x) (F y) +
            (b : EReal) * max (F x) (F y) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
      _ = max (F x) (F y) := by
        rw [← EReal.right_distrib_of_nonneg haE hbE, habE, one_mul]
  have hmax' : (a : EReal) * F x + ((1 - a : ℝ) : EReal) * F y ≤
      max (F x) (F y) := by
    simpa [hb_eq] using hmax
  rw [hb_eq]
  exact hconv.trans hmax'

private theorem levelSet_pointwise_bound_on_closedSpan_of_norm_bound
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (ξ R : ℝ)
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    ∀ s ∈ ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H),
      ∃ C : ℝ, ∀ u : H, ‖u‖ ≤ R → ∀ y : H,
        f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal) →
          |⟪s, y⟫_ℝ| ≤ C := by
  let D : Set H := effectiveDomain f - effectiveDomain g
  let S : Set H := ((Submodule.span ℝ D).topologicalClosure : Set H)
  have hD_nonempty : D.Nonempty := by
    rcases hf.2.nonempty with ⟨x, hx⟩
    rcases hg.2.nonempty with ⟨z, hz⟩
    exact ⟨x - z, Set.mem_sub.mpr ⟨x, hx, z, hz, rfl⟩⟩
  have hD_conv : Convex ℝ D := by
    dsimp [D]
    exact hf.2.convex_effectiveDomain.sub hg.2.convex_effectiveDomain
  intro s hs
  have hs_cone : s ∈ Set.cone D := by
    rw [hcone]
    simpa [S] using hs
  have hs_rep : ∃ c : ℝ, 0 < c ∧ ∃ d ∈ D, c • d = s := by
    have hs' : s ∈ (hD_conv.toCone D : Set H) := by
      simpa [Set.cone_def, convexCone_hull_eq_toCone hD_conv] using hs_cone
    exact hD_conv.mem_toCone.mp hs'
  have hneg_cone : -s ∈ Set.cone D := by
    rw [hcone]
    have hs' : s ∈ ((Submodule.span ℝ D).topologicalClosure : Set H) := by
      simpa [S] using hs
    exact Submodule.neg_mem _ hs'
  have hneg_rep : ∃ c : ℝ, 0 < c ∧ ∃ d ∈ D, c • d = -s := by
    have hs' : -s ∈ (hD_conv.toCone D : Set H) := by
      simpa [Set.cone_def, convexCone_hull_eq_toCone hD_conv] using hneg_cone
    exact hD_conv.mem_toCone.mp hs'
  rcases hs_rep with ⟨c, hc, d, hd, hds⟩
  rcases Set.mem_sub.mp hd with ⟨x, hx, z, hz, rfl⟩
  rcases hneg_rep with ⟨c', hc', d', hd', hds'⟩
  rcases Set.mem_sub.mp hd' with ⟨x', hx', z', hz', rfl⟩
  let A₁ : ℝ := ξ + (f x : EReal).toReal + (g z : EReal).toReal
  let A₂ : ℝ := ξ + (f x' : EReal).toReal + (g z' : EReal).toReal
  let C₁ : ℝ := c * (A₁ + ‖z‖ * R)
  let C₂ : ℝ := c' * (A₂ + ‖z'‖ * R)
  refine ⟨max |C₁| |C₂|, ?_⟩
  intro u hu y hy
  have h₁ := conjugate_sum_level_inner_le f g hx hz hy
  have h₂ := conjugate_sum_level_inner_le f g hx' hz' hy
  have hi₁ : ⟪z, u⟫_ℝ ≤ ‖z‖ * R := by
    exact (real_inner_le_norm z u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg z))
  have hi₂ : ⟪z', u⟫_ℝ ≤ ‖z'‖ * R := by
    exact (real_inner_le_norm z' u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg z'))
  have hi₁' : -⟪z, u⟫_ℝ ≤ ‖z‖ * R := by
    calc
      -⟪z, u⟫_ℝ ≤ |⟪z, u⟫_ℝ| := neg_le_abs _
      _ ≤ ‖z‖ * ‖u‖ := abs_real_inner_le_norm z u
      _ ≤ ‖z‖ * R := mul_le_mul_of_nonneg_left hu (norm_nonneg z)
  have hi₂' : -⟪z', u⟫_ℝ ≤ ‖z'‖ * R := by
    calc
      -⟪z', u⟫_ℝ ≤ |⟪z', u⟫_ℝ| := neg_le_abs _
      _ ≤ ‖z'‖ * ‖u‖ := abs_real_inner_le_norm z' u
      _ ≤ ‖z'‖ * R := mul_le_mul_of_nonneg_left hu (norm_nonneg z')
  have h₁' : ⟪x - z, y⟫_ℝ ≤ A₁ - ⟪z, u⟫_ℝ := by
    simpa [A₁] using h₁
  have h₂' : ⟪x' - z', y⟫_ℝ ≤ A₂ - ⟪z', u⟫_ℝ := by
    simpa [A₂] using h₂
  have hy₁ : ⟪s, y⟫_ℝ ≤ C₁ := by
    rw [← hds, real_inner_smul_left]
    calc
      c * ⟪x - z, y⟫_ℝ ≤ c * (A₁ - ⟪z, u⟫_ℝ) :=
        mul_le_mul_of_nonneg_left h₁' hc.le
      _ ≤ c * (A₁ + ‖z‖ * R) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hi₁']) hc.le
  have hy₂ : -⟪s, y⟫_ℝ ≤ C₂ := by
    calc
      -⟪s, y⟫_ℝ = ⟪-s, y⟫_ℝ := by simp
      _ = ⟪c' • (x' - z'), y⟫_ℝ := by rw [hds']
      _ = c' * ⟪x' - z', y⟫_ℝ := by rw [real_inner_smul_left]
      _ ≤ C₂ := by
        calc
          c' * ⟪x' - z', y⟫_ℝ ≤ c' * (A₂ - ⟪z', u⟫_ℝ) :=
            mul_le_mul_of_nonneg_left h₂' hc'.le
          _ ≤ c' * (A₂ + ‖z'‖ * R) := by
            exact mul_le_mul_of_nonneg_left (by linarith [hi₂']) hc'.le
  apply (abs_le).2
  constructor
  · have hlow₀ : -max |C₁| |C₂| ≤ -|C₂| :=
      neg_le_neg (le_max_right |C₁| |C₂|)
    have hlow₁ : -|C₂| ≤ -C₂ := neg_le_neg (le_abs_self C₂)
    have hle : -C₂ ≤ ⟪s, y⟫_ℝ := by linarith
    exact hlow₀.trans (hlow₁.trans hle)
  · exact hy₁.trans ((le_abs_self C₁).trans (le_max_left |C₁| |C₂|))

theorem closedSpan_projection_norm_bound_on_fenchelDual_levelSet_of_norm_bound
    {S : Submodule ℝ H} [S.HasOrthogonalProjection] [CompleteSpace S]
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (ξ R : ℝ)
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H))
    (hS : (S : Set H) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    ∃ C : ℝ, ∀ u : H, ‖u‖ ≤ R → ∀ y : H,
      f.asEReal∗ y + g.asEReal∗ (u - y) ≤ (ξ : EReal) →
      ‖S.starProjection y‖ ≤ C := by
  let Y : Type u := {p : H × H // ‖p.1‖ ≤ R ∧
      f.asEReal∗ p.2 + g.asEReal∗ (p.1 - p.2) ≤ (ξ : EReal)}
  let T : Y → S →L[ℝ] ℝ := fun p ↦
    (innerSL ℝ p.1.2).comp S.subtypeL
  have hpointwise : ∀ s : S, ∃ C : ℝ, ∀ p : Y, ‖T p s‖ ≤ C := by
    intro s
    have hs : (s : H) ∈
        ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H) := by
      rw [← hS]
      exact s.property
    rcases levelSet_pointwise_bound_on_closedSpan_of_norm_bound f g hf hg ξ R hcone
      (s : H) hs with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro p
    have hinner : ⟪(s : H), p.1.2⟫_ℝ = ⟪p.1.2, (s : H)⟫_ℝ := real_inner_comm _ _
    have hbound := hC p.1.1 p.property.1 p.1.2 p.property.2
    rw [show T p s = ⟪p.1.2, (s : H)⟫_ℝ by
      change ⟪p.1.2, (s : H)⟫_ℝ = ⟪p.1.2, (s : H)⟫_ℝ
      rfl]
    rw [← hinner]
    simpa [Real.norm_eq_abs] using hbound
  obtain ⟨C, hC⟩ :=
    uniform_boundedness_principle (ι := Y) (𝓧 := S) (𝓨 := ℝ) (T := T) hpointwise
  let C₀ : ℝ := max C 0
  have hC₀ : ∀ p : Y, ‖T p‖ ≤ C₀ := fun p ↦
    (hC p).trans (le_max_left C 0)
  have hC₀_nonneg : 0 ≤ C₀ := le_max_right C 0
  refine ⟨C₀, ?_⟩
  intro u hu y hy
  let p : H := S.starProjection y
  have hpS : p ∈ (S : Set H) := S.starProjection_apply_mem y
  let ps : S := ⟨p, hpS⟩
  have hTp : ‖T ⟨(u, y), ⟨hu, hy⟩⟩ ps‖ ≤ C₀ * ‖ps‖ := by
    calc
      ‖T ⟨(u, y), ⟨hu, hy⟩⟩ ps‖ ≤
          ‖T ⟨(u, y), ⟨hu, hy⟩⟩‖ * ‖ps‖ :=
        (T ⟨(u, y), ⟨hu, hy⟩⟩).le_opNorm ps
      _ ≤ C₀ * ‖ps‖ := by
        gcongr
        exact hC₀ ⟨(u, y), ⟨hu, hy⟩⟩
  have hproj_orth : y - p ∈ Sᗮ := S.sub_starProjection_mem_orthogonal y
  have hinner_eq : ⟪y, p⟫_ℝ = ‖p‖ ^ 2 := by
    have hz : ⟪y - p, p⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hpS hproj_orth
    rw [inner_sub_left] at hz
    calc
      ⟪y, p⟫_ℝ = ⟪p, p⟫_ℝ := by linarith
      _ = ‖p‖ ^ 2 := real_inner_self_eq_norm_sq p
  have hnorm_sq : ‖T ⟨(u, y), ⟨hu, hy⟩⟩ ps‖ = ‖p‖ ^ 2 := by
    rw [show T ⟨(u, y), ⟨hu, hy⟩⟩ ps = ⟪y, p⟫_ℝ by
      simp [T, ps, p, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply], hinner_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hnorm_le : ‖p‖ ^ 2 ≤ C₀ * ‖p‖ := by
    rw [hnorm_sq] at hTp
    exact hTp
  have hp_le : ‖p‖ ≤ C₀ := by
    nlinarith [sq_nonneg ‖p‖, norm_nonneg p]
  exact hp_le

theorem lowerSemicontinuous_infimalConvolution_conjugates_of_cone
    {S : Submodule ℝ H} [S.HasOrthogonalProjection] [CompleteSpace S]
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H))
    (hS : (S : Set H) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    LowerSemicontinuous (fun u : H ↦ (f.asEReal∗ □ g.asEReal∗) u) := by
  let h : H → EReal := fun u ↦ (f.asEReal∗ □ g.asEReal∗) u
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro ξ
  rw [← isSeqClosed_iff_isClosed]
  intro uₙ u huₙ hlevel
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ n : ℕ, ‖uₙ n‖ ≤ R := by
    have hbounded : Bornology.IsBounded (Set.range uₙ) :=
      Metric.isBounded_range_of_tendsto uₙ hlevel
    rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨R, hR⟩
    exact ⟨R, fun n ↦ hR _ (Set.mem_range_self n)⟩
  obtain ⟨C, hC⟩ :=
    closedSpan_projection_norm_bound_on_fenchelDual_levelSet_of_norm_bound
      (S := S) f g hf hg (ξ + 1) R hcone hS
  have hchoose : ∀ n : ℕ, ∃ y : H,
      f.asEReal∗ y + g.asEReal∗ (uₙ n - y) <
        ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
    intro n
    have hnlt : h (uₙ n) <
        ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hξlt : (ξ : EReal) <
          ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        exact_mod_cast (by linarith : ξ < ξ + 1 / ((n : ℝ) + 1))
      exact (mem_lowerLevelSet_iff h ξ (uₙ n)).1 (huₙ n) |>.trans_lt hξlt
    change (f.asEReal∗ □ g.asEReal∗) (uₙ n) < _ at hnlt
    rw [infimalConvolution_apply] at hnlt
    exact iInf_lt_iff.mp hnlt
  choose yₙ hyₙ using hchoose
  have hyₙ_level : ∀ n : ℕ,
      f.asEReal∗ (yₙ n) + g.asEReal∗ (uₙ n - yₙ n) ≤ ((ξ + 1 : ℝ) : EReal) := by
    intro n
    have hεle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    exact (hyₙ n).le.trans (by
      exact_mod_cast (by linarith : ξ + 1 / ((n : ℝ) + 1) ≤ ξ + 1))
  let zₙ : ℕ → H := fun n ↦ S.starProjection (yₙ n)
  have hzₙS : ∀ n, zₙ n ∈ S := fun n ↦ S.starProjection_apply_mem _
  have hzₙnorm : ∀ n, ‖zₙ n‖ ≤ C := by
    intro n
    exact hC (uₙ n) (hR n) (yₙ n) (hyₙ_level n)
  have hzₙeq : ∀ n,
      f.asEReal∗ (zₙ n) + g.asEReal∗ (uₙ n - zₙ n) =
        f.asEReal∗ (yₙ n) + g.asEReal∗ (uₙ n - yₙ n) :=
    fun n ↦ by
      have hw : yₙ n - zₙ n ∈ Sᗮ := S.sub_starProjection_mem_orthogonal (yₙ n)
      have hh := fenchelDualObjective_add_orthogonal_eq f g
        (D := effectiveDomain f - effectiveDomain g) (S := S)
        (u := uₙ n) (y := zₙ n) (w := yₙ n - zₙ n)
        rfl hS hw hf.2.nonempty hg.2.nonempty
      simpa [zₙ] using hh.symm
  let Cset : Set H := (S : Set H) ∩ Metric.closedBall (0 : H) C
  have hCset_closed : IsClosed Cset := by
    change IsClosed ((S : Set H) ∩ Metric.closedBall (0 : H) C)
    have hSclosed : IsClosed (S : Set H) := by
      rw [hS]
      exact Submodule.isClosed_topologicalClosure _
    exact hSclosed.inter Metric.isClosed_closedBall
  have hCset_convex : Convex ℝ Cset := by
    exact (S.convex).inter (convex_closedBall (0 : H) C)
  have hCset_bounded : Bornology.IsBounded Cset :=
    Metric.isBounded_closedBall.subset inter_subset_right
  have hzₙ_mem : ∀ n, zₙ n ∈ Cset := by
    intro n
    refine ⟨hzₙS n, ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hzₙnorm n
  obtain ⟨z, hzC, φ, hφ, hzφ⟩ :=
    exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex
      hCset_bounded hCset_closed hCset_convex zₙ hzₙ_mem
  have huφ : Filter.Tendsto (fun n ↦ uₙ (φ n)) Filter.atTop (nhds u) :=
    by simpa [Function.comp] using hlevel.comp hφ.tendsto_atTop
  have huφweak : Tendsto (fun n ↦ toWeakSpace ℝ H (uₙ (φ n))) atTop
      (nhds (toWeakSpace ℝ H u)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto u).comp huφ
  have hdiffweak : Tendsto
      (fun n ↦ toWeakSpace ℝ H (uₙ (φ n) - zₙ (φ n))) atTop
      (nhds (toWeakSpace ℝ H (u - z))) := by
    have hsub := huφweak.sub hzφ
    simpa using hsub
  have hf_lsc : LowerSemicontinuous f.asEReal∗ :=
    (mem_gamma_iff f.asEReal∗).mp (conjugate_mem_gamma f.asEReal) |>.2
  have hg_lsc : LowerSemicontinuous g.asEReal∗ :=
    (mem_gamma_iff g.asEReal∗).mp (conjugate_mem_gamma g.asEReal) |>.2
  have hf_conv : IsConvex f.asEReal∗ :=
    (mem_gamma_iff f.asEReal∗).mp (conjugate_mem_gamma f.asEReal) |>.1
  have hg_conv : IsConvex g.asEReal∗ :=
    (mem_gamma_iff g.asEReal∗).mp (conjugate_mem_gamma g.asEReal) |>.1
  have hf_weak : LowerSemicontinuous (f.asEReal∗ ∘ (toWeakSpace ℝ H).symm) :=
    weaklyLowerSemicontinuous_of_quasiconvexOn_univ
      (quasiconvexOn_univ_of_isConvex_local hf_conv) hf_lsc
  have hg_weak : LowerSemicontinuous (g.asEReal∗ ∘ (toWeakSpace ℝ H).symm) :=
    weaklyLowerSemicontinuous_of_quasiconvexOn_univ
      (quasiconvexOn_univ_of_isConvex_local hg_conv) hg_lsc
  have hf_lim : f.asEReal∗ z ≤
      Filter.liminf (fun n ↦ f.asEReal∗ (zₙ (φ n))) atTop := by
    calc
      f.asEReal∗ z = (f.asEReal∗ ∘ (toWeakSpace ℝ H).symm)
          (toWeakSpace ℝ H z) := by simp
      _ ≤ Filter.liminf (f.asEReal∗ ∘ (toWeakSpace ℝ H).symm)
          (nhds (toWeakSpace ℝ H z)) := hf_weak.le_liminf _
      _ ≤ Filter.liminf (f.asEReal∗ ∘ (toWeakSpace ℝ H).symm)
          (Filter.map (fun n ↦ toWeakSpace ℝ H (zₙ (φ n))) atTop) :=
        Filter.liminf_le_liminf_of_le hzφ
      _ = Filter.liminf (fun n ↦ f.asEReal∗ (zₙ (φ n))) atTop := by
        rw [← Filter.liminf_comp]
        congr 1
  have hg_lim : g.asEReal∗ (u - z) ≤
      Filter.liminf (fun n ↦ g.asEReal∗ (uₙ (φ n) - zₙ (φ n))) atTop := by
    calc
      g.asEReal∗ (u - z) = (g.asEReal∗ ∘ (toWeakSpace ℝ H).symm)
          (toWeakSpace ℝ H (u - z)) := by simp
      _ ≤ Filter.liminf (g.asEReal∗ ∘ (toWeakSpace ℝ H).symm)
          (nhds (toWeakSpace ℝ H (u - z))) := hg_weak.le_liminf _
      _ ≤ Filter.liminf (g.asEReal∗ ∘ (toWeakSpace ℝ H).symm)
          (Filter.map (fun n ↦ toWeakSpace ℝ H
            (uₙ (φ n) - zₙ (φ n))) atTop) :=
        Filter.liminf_le_liminf_of_le hdiffweak
      _ = Filter.liminf (fun n ↦ g.asEReal∗
            (uₙ (φ n) - zₙ (φ n))) atTop := by
        rw [← Filter.liminf_comp]
        congr 1
  have hq_lim : Filter.liminf
      (fun n ↦ f.asEReal∗ (zₙ (φ n)) +
        g.asEReal∗ (uₙ (φ n) - zₙ (φ n))) atTop ≤ (ξ : EReal) := by
    calc
      Filter.liminf
          (fun n ↦ f.asEReal∗ (zₙ (φ n)) +
            g.asEReal∗ (uₙ (φ n) - zₙ (φ n))) atTop ≤
          Filter.liminf (fun n ↦ ((ξ + 1 / ((φ n : ℝ) + 1) : ℝ) : EReal)) atTop := by
        refine Filter.liminf_le_liminf
          (u := fun n ↦ f.asEReal∗ (zₙ (φ n)) +
            g.asEReal∗ (uₙ (φ n) - zₙ (φ n)))
          (v := fun n ↦ ((ξ + 1 / ((φ n : ℝ) + 1) : ℝ) : EReal)) ?_ ?_ ?_
        · filter_upwards [] with n
          rw [hzₙeq (φ n)]
          exact (hyₙ (φ n)).le
        · isBoundedDefault
        · isBoundedDefault
      _ = (ξ : EReal) := by
        have ht_real : Tendsto
            (fun n : ℕ ↦ ξ + 1 / ((n : ℝ) + 1)) atTop (nhds ξ) := by
          simpa using ((tendsto_const_nhds :
              Tendsto (fun _ : ℕ ↦ ξ) atTop (nhds ξ)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1))) atTop (nhds 0)))
        have ht : Tendsto
            (fun n : ℕ ↦ ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal)) atTop
            (nhds (ξ : EReal)) :=
          (continuous_coe_real_ereal.tendsto ξ).comp ht_real
        have htφ := ht.comp hφ.tendsto_atTop
        simpa [Function.comp] using htφ.liminf_eq
  have hsum : h u ≤ (ξ : EReal) := by
    have hlim_obj : f.asEReal∗ z + g.asEReal∗ (u - z) ≤
        Filter.liminf
          (fun n ↦ f.asEReal∗ (zₙ (φ n)) +
            g.asEReal∗ (uₙ (φ n) - zₙ (φ n))) atTop := by
      exact (add_le_add hf_lim hg_lim).trans EReal.le_liminf_add
    exact (iInf_le (fun y : H ↦ f.asEReal∗ y + g.asEReal∗ (u - y)) z).trans
      (hlim_obj.trans hq_lim)
  exact (mem_lowerLevelSet_iff h ξ u).2 hsum

private lemma effectiveDomain_inter_nonempty_of_cone_eq_closure_span
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    (effectiveDomain f ∩ effectiveDomain g).Nonempty := by
  let D : Set H := effectiveDomain f - effectiveDomain g
  have hD_conv : Convex ℝ D := by
    dsimp [D]
    exact hf.2.convex_effectiveDomain.sub hg.2.convex_effectiveDomain
  have hzero_cone : (0 : H) ∈ Set.cone D := by
    rw [hcone]
    exact Submodule.zero_mem _
  have hzero_toCone : (0 : H) ∈ (hD_conv.toCone D : Set H) := by
    simpa [Set.cone_def, convexCone_hull_eq_toCone hD_conv] using hzero_cone
  rcases hD_conv.mem_toCone.mp hzero_toCone with ⟨c, hc, d, hd, hcd⟩
  have hd_zero : d = 0 :=
    (smul_eq_zero.mp hcd).resolve_left (ne_of_gt hc)
  rcases Set.mem_sub.mp hd with ⟨x, hx, z, hz, hxd⟩
  have hcd_zero : c • (x - z) = 0 := by simpa [hxd] using hcd
  have hxz : x - z = 0 :=
    (smul_eq_zero.mp hcd_zero).resolve_left (ne_of_gt hc)
  refine ⟨x, hx, ?_⟩
  simpa [sub_eq_zero.mp hxz] using hz

private lemma ereal_mul_coe_strict
    {r : ℝ} {s t : EReal} (hr : 0 < r) (hs : s ≠ ⊥) (ht : t ≠ ⊤)
    (hst : s < t) : (r : EReal) * s < (r : EReal) * t := by
  have hs_top : s ≠ ⊤ := ne_top_of_lt hst
  have ht_bot : t ≠ ⊥ := ne_bot_of_le_ne_bot hs hst.le
  lift s to ℝ using ⟨hs_top, hs⟩
  lift t to ℝ using ⟨ht, ht_bot⟩
  norm_cast at hst ⊢
  exact mul_lt_mul_of_pos_left hst hr

private theorem isConvex_infimalConvolution_of_isConvex
    (F G : H → EReal) (hF : IsConvex F) (hG : IsConvex G)
    (hbot : ∀ u : H, (⨅ y : H, F y + G (u - y)) ≠ ⊥) :
    IsConvex (fun u : H ↦ ⨅ y : H, F y + G (u - y)) := by
  intro x y a ha0 ha1
  let b : ℝ := 1 - a
  by_cases ha_zero : a = 0
  · subst a
    norm_num [sub_eq_add_neg]
  by_cases ha_one : a = 1
  · subst a
    dsimp
    have hsub : (1 : EReal) - 1 = 0 := by
      apply EReal.sub_self
      · exact EReal.coe_ne_top 1
      · exact EReal.coe_ne_bot 1
    rw [hsub]
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha_zero)
  have hb_pos : 0 < b := by
    dsimp [b]
    exact sub_pos.mpr (lt_of_le_of_ne ha1 ha_one)
  let hxv : EReal := ⨅ z : H, F z + G (x - z)
  let hyv : EReal := ⨅ z : H, F z + G (y - z)
  have hxv_bot : hxv ≠ ⊥ := hbot x
  have hyv_bot : hyv ≠ ⊥ := hbot y
  have harg : a • x + b • y = a • x + (1 - a) • y := by rfl
  change (⨅ z : H, F z + G (a • x + b • y - z)) ≤
    (a : EReal) * hxv + (b : EReal) * hyv
  by_cases hx_top : hxv = ⊤
  · have hmul : (a : EReal) * hxv = ⊤ := by
      rw [hx_top, EReal.coe_mul_top_of_pos ha_pos]
    have hother : (b : EReal) * hyv ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, hb_pos.ne', hb_pos.le, hyv_bot]
    rw [hmul, EReal.top_add_of_ne_bot hother]
    exact le_top
  by_cases hy_top : hyv = ⊤
  · have hmul : (b : EReal) * hyv = ⊤ := by
      rw [hy_top, EReal.coe_mul_top_of_pos hb_pos]
    have hother : (a : EReal) * hxv ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, ha_pos.ne', ha_pos.le, hxv_bot]
    rw [hmul, EReal.add_top_of_ne_bot hother]
    exact le_top
  have hR_top : (a : EReal) * hxv + (b : EReal) * hyv ≠ ⊤ := by
    apply EReal.add_ne_top
    · rw [EReal.mul_ne_top]
      simp [hx_top, EReal.coe_ne_bot, EReal.coe_ne_top, ha_pos.le, hxv_bot]
    · rw [EReal.mul_ne_top]
      simp [hy_top, EReal.coe_ne_bot, EReal.coe_ne_top, hb_pos.le, hyv_bot]
  have hR_bot : (a : EReal) * hxv + (b : EReal) * hyv ≠ ⊥ := by
    exact EReal.add_ne_bot_iff.mpr ⟨by
      rw [EReal.mul_ne_bot]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, ha_pos.le, hxv_bot], by
      rw [EReal.mul_ne_bot]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, hb_pos.le, hyv_bot]⟩
  have hRcoe :
      (((a : EReal) * hxv + (b : EReal) * hyv).toReal : EReal) =
        (a : EReal) * hxv + (b : EReal) * hyv :=
    EReal.coe_toReal hR_top hR_bot
  have hconv' :
      (⨅ z : H, F z + G (a • x + b • y - z)) ≤
        (((a : EReal) * hxv + (b : EReal) * hyv).toReal : EReal) := by
    refine (EReal.le_of_forall_lt_iff_le
      (x := ((a : EReal) * hxv + (b : EReal) * hyv).toReal)
      (y := (⨅ z : H, F z + G (a • x + b • y - z)))).1 ?_
    intro r hr
    let δ : ℝ := (r - (a * hxv.toReal + b * hyv.toReal)) / 2
    have hA_top : (a : EReal) * hxv ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, ha_pos.le, hxv_bot, hx_top]
    have hA_bot : (a : EReal) * hxv ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, ha_pos.le, hxv_bot]
    have hB_top : (b : EReal) * hyv ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, hb_pos.le, hyv_bot, hy_top]
    have hB_bot : (b : EReal) * hyv ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      simp [EReal.coe_ne_bot, EReal.coe_ne_top, hb_pos.le, hyv_bot]
    have hRreal :
        ((a : EReal) * hxv + (b : EReal) * hyv).toReal =
          a * hxv.toReal + b * hyv.toReal := by
      rw [EReal.toReal_add hA_top hA_bot hB_top hB_bot,
        EReal.toReal_mul, EReal.toReal_mul]
      simp
    have hR_lt : a * hxv.toReal + b * hyv.toReal < r := by
      rw [← hRreal]
      exact EReal.coe_lt_coe_iff.mp hr
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hx_lt : hxv < hxv + (δ : EReal) :=
      by
        rw [← EReal.coe_toReal hx_top hxv_bot, ← EReal.coe_add]
        exact_mod_cast (lt_add_of_pos_right hxv.toReal hδ)
    have hy_lt : hyv < hyv + (δ : EReal) :=
      by
        rw [← EReal.coe_toReal hy_top hyv_bot, ← EReal.coe_add]
        exact_mod_cast (lt_add_of_pos_right hyv.toReal hδ)
    obtain ⟨p, hp⟩ : ∃ p : H, F p + G (x - p) < hxv + (δ : EReal) := by
      apply iInf_lt_iff.mp
      exact hx_lt
    obtain ⟨q, hq⟩ : ∃ q : H, F q + G (y - q) < hyv + (δ : EReal) := by
      apply iInf_lt_iff.mp
      exact hy_lt
    have hp_bot : F p + G (x - p) ≠ ⊥ := by
      apply EReal.add_ne_bot_iff.mpr
      constructor
      · intro hFp
        apply hxv_bot
        apply le_bot_iff.mp
        calc
          hxv ≤ F p + G (x - p) := iInf_le _ p
          _ = ⊥ := by rw [hFp, EReal.bot_add]
      · intro hGp
        apply hxv_bot
        apply le_bot_iff.mp
        calc
          hxv ≤ F p + G (x - p) := iInf_le _ p
          _ = ⊥ := by rw [hGp, EReal.add_bot]
    have hq_bot : F q + G (y - q) ≠ ⊥ := by
      apply EReal.add_ne_bot_iff.mpr
      constructor
      · intro hFq
        apply hyv_bot
        apply le_bot_iff.mp
        calc
          hyv ≤ F q + G (y - q) := iInf_le _ q
          _ = ⊥ := by rw [hFq, EReal.bot_add]
      · intro hGq
        apply hyv_bot
        apply le_bot_iff.mp
        calc
          hyv ≤ F q + G (y - q) := iInf_le _ q
          _ = ⊥ := by rw [hGq, EReal.add_bot]
    have hp_top : F p + G (x - p) ≠ ⊤ := by
      apply ne_top_of_lt
      exact lt_trans hp (lt_top_iff_ne_top.mpr
        (EReal.add_ne_top hx_top (EReal.coe_ne_top δ)))
    have hq_top : F q + G (y - q) ≠ ⊤ := by
      apply ne_top_of_lt
      exact lt_trans hq (lt_top_iff_ne_top.mpr
        (EReal.add_ne_top hy_top (EReal.coe_ne_top δ)))
    have hweighted :
        (a : EReal) * (F p + G (x - p)) +
          (b : EReal) * (F q + G (y - q)) <
          (a : EReal) * (hxv + (δ : EReal)) +
            (b : EReal) * (hyv + (δ : EReal)) := by
      exact EReal.add_lt_add
        (ereal_mul_coe_strict ha_pos hp_bot
          (EReal.add_ne_top hx_top (EReal.coe_ne_top δ)) hp)
        (ereal_mul_coe_strict hb_pos hq_bot
          (EReal.add_ne_top hy_top (EReal.coe_ne_top δ)) hq)
    have hsplit :
        F (a • p + b • q) + G (a • x + b • y - (a • p + b • q)) ≤
          (a : EReal) * (F p + G (x - p)) +
            (b : EReal) * (F q + G (y - q)) := by
      have harg' : a • x + b • y - (a • p + b • q) =
          a • (x - p) + b • (y - q) := by
        rw [smul_sub, smul_sub]
        module
      rw [harg']
      calc
        F (a • p + b • q) + G (a • (x - p) + b • (y - q)) ≤
            ((a : EReal) * F p + (b : EReal) * F q) +
              ((a : EReal) * G (x - p) + (b : EReal) * G (y - q)) :=
          add_le_add (hF ha0 ha1) (hG ha0 ha1)
        _ = (a : EReal) * (F p + G (x - p)) +
            (b : EReal) * (F q + G (y - q)) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top
            (EReal.coe_nonneg.mpr ha0) (EReal.coe_ne_top a),
            EReal.left_distrib_of_nonneg_of_ne_top
            (EReal.coe_nonneg.mpr hb_pos.le) (EReal.coe_ne_top b)]
          ac_rfl
    have htarget :
        (a : EReal) * (hxv + (δ : EReal)) +
            (b : EReal) * (hyv + (δ : EReal)) < (r : EReal) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr ha0) (EReal.coe_ne_top a),
        EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr hb_pos.le) (EReal.coe_ne_top b)]
      have hδ' :
          (a : EReal) * (δ : EReal) + (b : EReal) * (δ : EReal) =
            ((a * δ + b * δ : ℝ) : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      calc
        (a : EReal) * hxv + (a : EReal) * (δ : EReal) +
            ((b : EReal) * hyv + (b : EReal) * (δ : EReal)) =
            ((a : EReal) * hxv + (b : EReal) * hyv) +
              ((a : EReal) * (δ : EReal) + (b : EReal) * (δ : EReal)) := by
                ac_rfl
        _ = ((a : EReal) * hxv + (b : EReal) * hyv) +
              ((a * δ + b * δ : ℝ) : EReal) := by rw [hδ']
        _ < (r : EReal) := by
          rw [← hRcoe, hRreal, ← EReal.coe_add]
          have hab : a + b = 1 := by
            dsimp [b]
            linarith
          have habδ : a * δ + b * δ = δ := by
            rw [← add_mul, hab]
            norm_num
          have hreal :
              a * hxv.toReal + b * hyv.toReal + (a * δ + b * δ) < r := by
            rw [habδ]
            dsimp [δ]
            linarith
          exact_mod_cast hreal
    exact (iInf_le (fun z : H ↦ F z + G (a • x + b • y - z))
      (a • p + b • q)).trans_lt
      (lt_of_le_of_lt hsplit (lt_trans hweighted htarget)) |>.le
  exact hconv'.trans_eq hRcoe

/-! ## Reduction to finite conjugate values -/

/-- The textbook Attouch--Brézis construction attains every finite value of the conjugate
of the primal sum.  The proof uses the closed-span projection bound above and a weakly convergent
subsequence of projected approximate minimizers. -/
theorem attouchBrezis_finite_conjugate_split_attainment
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H))
    {u : H} (hu : (f + g).asEReal∗ u ≠ ⊤) :
    ∃ y : H,
      (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y) := by
  let S : Submodule ℝ H :=
    (Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure
  let h : H → EReal := fun v ↦ (f.asEReal∗ □ g.asEReal∗) v
  have hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty :=
    effectiveDomain_inter_nonempty_of_cone_eq_closure_span f g hf hg hcone
  have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom
  have hfg_proper : IsProper (f + g).asEReal := isProper_of_mem_gammaZero hfg
  have hbot : ∀ v : H, h v ≠ ⊥ := by
    intro v hv
    apply conjugate_ne_bot_of_isProper hfg_proper v
    have hweak := conjugate_add_le_infimalConvolution_conjugate f g v
    change (f.asEReal∗ □ g.asEReal∗) v = ⊥ at hv
    exact le_bot_iff.mp (hweak.trans_eq hv)
  have hconv_f : IsConvex f.asEReal∗ :=
    (mem_gamma_iff f.asEReal∗).mp (conjugate_mem_gamma f.asEReal) |>.1
  have hconv_g : IsConvex g.asEReal∗ :=
    (mem_gamma_iff g.asEReal∗).mp (conjugate_mem_gamma g.asEReal) |>.1
  have hconv : IsConvex h := by
    simpa [h] using
      (isConvex_infimalConvolution_of_isConvex f.asEReal∗ g.asEReal∗
        hconv_f hconv_g hbot)
  have hlsc : LowerSemicontinuous h := by
    simpa [h, S] using
      (lowerSemicontinuous_infimalConvolution_conjugates_of_cone
        (S := S) f g hf hg hcone (by rfl))
  have hfinite : ∃ v : H, h v ≠ ⊤ := by
    rcases dom_conjugate_nonempty_of_mem_gammaZero hf with ⟨y, hy⟩
    rcases dom_conjugate_nonempty_of_mem_gammaZero hg with ⟨z, hz⟩
    have hy_top : f.asEReal∗ y ≠ ⊤ := mem_dom_iff_ne_top.mp hy
    have hz_top : g.asEReal∗ z ≠ ⊤ := mem_dom_iff_ne_top.mp hz
    have hsum_top : f.asEReal∗ y + g.asEReal∗ z ≠ ⊤ :=
      EReal.add_ne_top hy_top hz_top
    have hle : h (y + z) ≤ f.asEReal∗ y + g.asEReal∗ z := by
      change (f.asEReal∗ □ g.asEReal∗) (y + z) ≤ _
      rw [infimalConvolution_apply]
      simpa using
        (iInf_le (fun w : H ↦ f.asEReal∗ w + g.asEReal∗ (y + z - w)) y)
    exact ⟨y + z, ne_top_of_le_ne_top hsum_top hle⟩
  have hproper : IsProper h := ⟨hbot, by
    rcases hfinite with ⟨v, hv⟩
    exact ⟨v, (mem_dom_iff_ne_top).2 hv⟩⟩
  have hgamma : h ∈ Γ(H) := (mem_gamma_iff h).2 ⟨hconv, hlsc⟩
  have hbiconj : h∗∗ = h :=
    (mem_gamma_iff_eq_biconjugate_of_is_proper hproper).mp hgamma
  have hstar : h∗ = (f + g).asEReal := by
    simpa [h, gammaZeroConjugate_apply, Function.asEReal_apply] using
      (conjugate_gammaZeroConjugate_infimalConvolution_eq_pointwiseAdd f g hf hg)
  have hstarstar : h∗∗ = (f + g).asEReal∗ := by
    simpa using congrArg conjugate hstar
  have heq : h = (f + g).asEReal∗ := by
    funext v
    calc
      h v = h∗∗ v := (congrFun hbiconj v).symm
      _ = (f + g).asEReal∗ v := congrFun hstarstar v
  have hu_top : h u ≠ ⊤ := by
    intro hv
    apply hu
    calc
      (f + g).asEReal∗ u = h u := (congrFun heq u).symm
      _ = ⊤ := hv
  have hu_bot : h u ≠ ⊥ := hbot u
  let ξ : ℝ := (h u).toReal
  have hu_coe : h u = (ξ : EReal) := by
    dsimp [ξ]
    exact (EReal.coe_toReal hu_top hu_bot).symm
  have hchoose : ∀ n : ℕ, ∃ y : H,
      f.asEReal∗ y + g.asEReal∗ (u - y) <
        ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
    intro n
    have hlt : h u <
        ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
      rw [hu_coe]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact_mod_cast (by linarith : ξ < ξ + 1 / ((n : ℝ) + 1))
    change (f.asEReal∗ □ g.asEReal∗) u < _ at hlt
    rw [infimalConvolution_apply] at hlt
    exact iInf_lt_iff.mp hlt
  choose yₙ hyₙ using hchoose
  have hyₙ_level : ∀ n : ℕ,
      f.asEReal∗ (yₙ n) + g.asEReal∗ (u - yₙ n) ≤ ((ξ + 1 : ℝ) : EReal) := by
    intro n
    have hεle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    exact (hyₙ n).le.trans (by
      exact_mod_cast (by linarith : ξ + 1 / ((n : ℝ) + 1) ≤ ξ + 1))
  obtain ⟨C, hC⟩ :=
    exists_bounded_closedSpan_representative_on_fenchelDual_levelSet
      (S := S) f g hf hg u (ξ + 1) hcone (by rfl)
  have hrep : ∀ n : ℕ, ∃ z : H, z ∈ S ∧ ‖z‖ ≤ C ∧
      f.asEReal∗ z + g.asEReal∗ (u - z) =
        f.asEReal∗ (yₙ n) + g.asEReal∗ (u - yₙ n) := by
    intro n
    exact hC (yₙ n) (hyₙ_level n)
  choose zₙ hzₙS hzₙnorm hzₙeq using hrep
  let Cset : Set H := (S : Set H) ∩ Metric.closedBall (0 : H) C
  have hCset_closed : IsClosed Cset := by
    change IsClosed ((S : Set H) ∩ Metric.closedBall (0 : H) C)
    have hSclosed : IsClosed (S : Set H) := by
      change IsClosed
        ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)
      exact Submodule.isClosed_topologicalClosure _
    exact hSclosed.inter Metric.isClosed_closedBall
  have hCset_convex : Convex ℝ Cset := by
    exact (S.convex).inter (convex_closedBall (0 : H) C)
  have hCset_bounded : Bornology.IsBounded Cset :=
    Metric.isBounded_closedBall.subset inter_subset_right
  have hzₙ_mem : ∀ n, zₙ n ∈ Cset := by
    intro n
    refine ⟨hzₙS n, ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hzₙnorm n
  obtain ⟨z, hzC, φ, hφ, hzφ⟩ :=
    exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex
      hCset_bounded hCset_closed hCset_convex zₙ hzₙ_mem
  let k : H → EReal := fun y ↦ f.asEReal∗ y + g.asEReal∗ (u - y)
  have hk_lsc : LowerSemicontinuous k := by
    simpa [k] using lowerSemicontinuous_conjugate_split_objective f g u
  have hk_conv : IsConvex k := by
    simpa [k] using isConvex_conjugate_split_objective f g u
  have hk_weak : LowerSemicontinuous (k ∘ (toWeakSpace ℝ H).symm) :=
    weaklyLowerSemicontinuous_of_quasiconvexOn_univ
      (quasiconvexOn_univ_of_isConvex_local hk_conv) hk_lsc
  have hk_lim : k z ≤ Filter.liminf (fun n ↦ k (zₙ (φ n))) atTop := by
    calc
      k z = (k ∘ (toWeakSpace ℝ H).symm)
          (toWeakSpace ℝ H z) := by simp
      _ ≤ Filter.liminf (k ∘ (toWeakSpace ℝ H).symm)
          (nhds (toWeakSpace ℝ H z)) := hk_weak.le_liminf _
      _ ≤ Filter.liminf (k ∘ (toWeakSpace ℝ H).symm)
          (Filter.map (fun n ↦ toWeakSpace ℝ H (zₙ (φ n))) atTop) :=
        Filter.liminf_le_liminf_of_le hzφ
      _ = Filter.liminf (fun n ↦ k (zₙ (φ n))) atTop := by
        rw [← Filter.liminf_comp]
        congr 1
  have hq_lim : Filter.liminf (fun n ↦ k (zₙ (φ n))) atTop ≤ (ξ : EReal) := by
    calc
      Filter.liminf (fun n ↦ k (zₙ (φ n))) atTop ≤
          Filter.liminf (fun n ↦ ((ξ + 1 / ((φ n : ℝ) + 1) : ℝ) : EReal)) atTop := by
        refine Filter.liminf_le_liminf
          (u := fun n ↦ k (zₙ (φ n)))
          (v := fun n ↦ ((ξ + 1 / ((φ n : ℝ) + 1) : ℝ) : EReal)) ?_ ?_ ?_
        · filter_upwards [] with n
          change f.asEReal∗ (zₙ (φ n)) + g.asEReal∗ (u - zₙ (φ n)) ≤ _
          rw [hzₙeq]
          exact (hyₙ (φ n)).le
        · isBoundedDefault
        · isBoundedDefault
      _ = (ξ : EReal) := by
        have ht_real : Tendsto
            (fun n : ℕ ↦ ξ + 1 / ((n : ℝ) + 1)) atTop (nhds ξ) := by
          simpa using ((tendsto_const_nhds :
              Tendsto (fun _ : ℕ ↦ ξ) atTop (nhds ξ)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1))) atTop (nhds 0)))
        have ht : Tendsto
            (fun n : ℕ ↦ ((ξ + 1 / ((n : ℝ) + 1) : ℝ) : EReal)) atTop
            (nhds (ξ : EReal)) :=
          (continuous_coe_real_ereal.tendsto ξ).comp ht_real
        have htφ := ht.comp hφ.tendsto_atTop
        simpa [Function.comp] using htφ.liminf_eq
  have hobj_le : k z ≤ h u := by
    rw [hu_coe]
    exact hk_lim.trans hq_lim
  have hobj_ge : h u ≤ k z := by
    change (f.asEReal∗ □ g.asEReal∗) u ≤ _
    rw [infimalConvolution_apply]
    exact iInf_le (fun y : H ↦ f.asEReal∗ y + g.asEReal∗ (u - y)) z
  have hobj_eq : h u = k z := le_antisymm hobj_ge hobj_le
  refine ⟨z, ?_⟩
  calc
    (f + g).asEReal∗ u = h u := (congrFun heq u).symm
    _ = k z := hobj_eq
    _ = f.asEReal∗ z + g.asEReal∗ (u - z) := rfl

/-- At an infinite conjugate value, every dual split has value `+∞` by weak duality. -/
theorem split_attainment_of_conjugate_eq_top
    (f g : H → Set.Ioi (⊥ : EReal)) {u : H}
    (htop : (f + g).asEReal∗ u = ⊤) (y : H) :
    (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y) := by
  have hweak :
      (f + g).asEReal∗ u ≤ f.asEReal∗ y + g.asEReal∗ (u - y) := by
    calc
      (f + g).asEReal∗ u ≤ (f.asEReal∗ □ g.asEReal∗) u :=
        conjugate_add_le_infimalConvolution_conjugate f g u
      _ ≤ f.asEReal∗ y + g.asEReal∗ (u - y) := by
        rw [infimalConvolution_apply]
        exact iInf_le (fun z : H ↦ f.asEReal∗ z + g.asEReal∗ (u - z)) y
  exact htop.trans (top_unique (htop ▸ hweak)).symm

/-- To establish split attainment everywhere, it suffices to prove it at finite conjugate values.
The `+∞` branch follows from weak duality and needs no regularity hypothesis. -/
theorem split_attainment_of_finite_conjugate_split
    (f g : H → Set.Ioi (⊥ : EReal))
    (hfinite : ∀ u : H, (f + g).asEReal∗ u ≠ ⊤ →
      ∃ y : H,
        (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y)) :
    ∀ u : H, ∃ y : H,
      (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y) := by
  intro u
  by_cases htop : (f + g).asEReal∗ u = ⊤
  · exact ⟨0, split_attainment_of_conjugate_eq_top f g htop 0⟩
  · exact hfinite u htop

/-- The cone condition gives a split attaining the conjugate of the primal sum at every point.
The finite branch is the textbook Attouch--Brézis construction above; the infinite branch is the
elementary weak-duality argument. -/
theorem attouchBrezis_split_attainment
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    ∀ u : H, ∃ y : H,
      (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y) := by
  exact split_attainment_of_finite_conjugate_split f g (fun u hu ↦
    attouchBrezis_finite_conjugate_split_attainment f g hf hg hcone hu)

/-! ## Conjugate formula and exactness -/

theorem conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_split_attainment
    (f g : H → Set.Ioi (⊥ : EReal))
    (hattain : ∀ u : H, ∃ y : H,
      (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y)) :
    (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ := by
  ext u
  apply le_antisymm
  · exact conjugate_add_le_infimalConvolution_conjugate f g u
  · rcases hattain u with ⟨y, hy⟩
    calc
      (f.asEReal∗ □ g.asEReal∗) u ≤
          f.asEReal∗ y + g.asEReal∗ (u - y) := by
            rw [infimalConvolution_apply]
            exact iInf_le (fun z : H ↦ f.asEReal∗ z + g.asEReal∗ (u - z)) y
      _ = (f + g).asEReal∗ u := hy.symm

theorem infimalConvolution_exact_gammaZeroConjugates_of_split_attainment
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hattain : ∀ u : H, ∃ y : H,
      (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := by
  have hformula :=
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_split_attainment f g hattain
  intro u hu
  rcases hattain u with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [← hformula]
  simpa [gammaZeroConjugate_apply] using hy

/-- The algebraic Fenchel--Rockafellar conclusion once the analytic split-attainment input has
been supplied.  The first component is the conjugate formula and the second records exactness of
the packaged `Γ₀` infimal convolution on every finite slice. -/
theorem fenchelRockafellar_of_split_attainment
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hattain : ∀ u : H, ∃ y : H,
      (f + g).asEReal∗ u = f.asEReal∗ y + g.asEReal∗ (u - y)) :
    (f + g).asEReal∗ = (f.asEReal∗ □ g.asEReal∗) ∧
    infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := by
  exact ⟨
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_split_attainment f g hattain,
    infimalConvolution_exact_gammaZeroConjugates_of_split_attainment f g hf hg hattain⟩

/-- Full Attouch--Brézis/Fenchel--Rockafellar conclusion under the cone hypothesis. -/
theorem fenchelRockafellar_of_cone
    [CompleteSpace H]
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcone : Set.cone (effectiveDomain f - effectiveDomain g) =
      ((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure : Set H)) :
    (f + g).asEReal∗ = (f.asEReal∗ □ g.asEReal∗) ∧
      infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := by
  exact fenchelRockafellar_of_split_attainment f g hf hg
    (attouchBrezis_split_attainment f g hf hg hcone)

end ERealFunction
