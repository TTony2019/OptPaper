import Mathlib
import Foundation.Convex.InfimalConvolution
import Foundation.Convex.Conjugate
import Foundation.Convex.FenchelRockafellar

/-!
# Fiberwise product-space bridges

The Chapter 25 Fitzpatrick argument lifts two functions on `H × K` to
`(H × K) × K`.  This file contains the coordinate maps and the elementary
effective-domain identity used by that lift.
-/

open Set
open scoped InnerProductSpace Pointwise
open WithLp

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

noncomputable abbrev prod_pseudoMetricSpace_l2 : PseudoMetricSpace (H × K) :=
  WithLp.pseudoMetricSpaceToProd (p := 2) (α := H) (β := K)

noncomputable abbrev prod_completeSpace_l2 : CompleteSpace (H × K) := by
  letI : PseudoMetricSpace (H × K) := prod_pseudoMetricSpace_l2 (H := H) (K := K)
  exact (WithLp.uniformEquivProd (p := 2) H K).completeSpace_iff.1 inferInstance

noncomputable abbrev prod_seminormedAddCommGroup_l2 : SeminormedAddCommGroup (H × K) :=
  WithLp.seminormedAddCommGroupToProd (p := 2) (α := H) (β := K)

noncomputable abbrev prod_normedAddCommGroup_l2 : NormedAddCommGroup (H × K) :=
  WithLp.normedAddCommGroupToProd (p := 2) (α := H) (β := K)

noncomputable abbrev prod_normedSpace_l2 :
    @NormedSpace ℝ (H × K) _ (prod_seminormedAddCommGroup_l2 (H := H) (K := K)) := by
  letI : SeminormedAddCommGroup (H × K) := prod_seminormedAddCommGroup_l2 (H := H) (K := K)
  letI : NormedAddCommGroup (H × K) := prod_normedAddCommGroup_l2 (H := H) (K := K)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) (α := H) (β := K) (R := ℝ)

noncomputable abbrev prod_innerProductSpace_l2 :
    @InnerProductSpace ℝ (H × K) _ (prod_seminormedAddCommGroup_l2 (H := H) (K := K)) := by
  letI : SeminormedAddCommGroup (H × K) := prod_seminormedAddCommGroup_l2 (H := H) (K := K)
  letI : NormedAddCommGroup (H × K) := prod_normedAddCommGroup_l2 (H := H) (K := K)
  letI : NormedSpace ℝ (H × K) := prod_normedSpace_l2 (H := H) (K := K)
  exact
    { inner x y := inner ℝ x.1 y.1 + inner ℝ x.2 y.2
      norm_sq_eq_re_inner x := by
        have hnorm :
            @Norm.norm (H × K) (prod_seminormedAddCommGroup_l2 (H := H) (K := K)).toNorm x =
              ‖WithLp.toLp 2 x‖ := by
          exact WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := K) x
        have hnorm_sq :
            @Norm.norm (H × K) (prod_seminormedAddCommGroup_l2 (H := H) (K := K)).toNorm x ^ 2 =
              ‖WithLp.toLp 2 x‖ ^ 2 := by
          simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
        exact hnorm_sq.trans <| by
          simpa [sq, real_inner_self_eq_norm_sq] using
            (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 x))
      conj_inner_symm x y := by simp [real_inner_comm]
      add_left x y z := by simp [inner_add_left, add_assoc, add_left_comm]
      smul_left x y r := by simp [inner_smul_left, mul_add] }

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_completeSpace_l2
attribute [local instance] prod_seminormedAddCommGroup_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_innerProductSpace_l2

@[simp] theorem prod_inner_l2_apply (p q : H × K) :
    inner ℝ p q = inner ℝ p.1 q.1 + inner ℝ p.2 q.2 := by
  rfl

/-- The pullback `(x, y, z) ↦ (x, z)`. -/
abbrev firstLastPullbackMap : ((H × K) × K) →L[ℝ] (H × K) :=
  (((ContinuousLinearMap.fst ℝ H K).comp
      (ContinuousLinearMap.fst ℝ (H × K) K)).prod
    (ContinuousLinearMap.snd ℝ (H × K) K))

/-- The pullback `(x, y, z) ↦ (x, y - z)`. -/
abbrev firstDifferencePullbackMap : ((H × K) × K) →L[ℝ] (H × K) :=
  (((ContinuousLinearMap.fst ℝ H K).comp
      (ContinuousLinearMap.fst ℝ (H × K) K)).prod
    ((ContinuousLinearMap.snd ℝ H K).comp
      (ContinuousLinearMap.fst ℝ (H × K) K) -
      ContinuousLinearMap.snd ℝ (H × K) K))

@[simp] theorem firstLastPullbackMap_apply (q : (H × K) × K) :
    firstLastPullbackMap q = (q.1.1, q.2) := by
  rfl

@[simp] theorem firstDifferencePullbackMap_apply (q : (H × K) × K) :
    firstDifferencePullbackMap q = (q.1.1, q.1.2 - q.2) := by
  rfl

private theorem comp_continuousLinearMap_mem_gammaZero_of_range_meets_domain
    {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(F))
    (L : E →L[ℝ] F)
    (hdom : (Set.range L ∩ effectiveDomain f).Nonempty) :
    f ∘ L ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨by simpa using hf.1.comp L.continuous, ?_⟩
  refine ⟨?_, subset_rfl, ?_⟩
  · rcases hdom with ⟨y, ⟨x, rfl⟩, hy⟩
    exact ⟨x, by simpa [Function.comp, mem_effectiveDomain_iff] using hy⟩
  · intro x hx y hy a ha0 ha1
    have hx' : L x ∈ effectiveDomain f := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain f := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using
      hf.2.ineq hx' hy' ha0 ha1

/-- Pulling a `Γ₀` function back along the first-last coordinate map preserves `Γ₀`. -/
theorem firstLastPullback_mem_gammaZero
    (φ : H × K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H × K)) :
    φ ∘ firstLastPullbackMap ∈ Γ₀((H × K) × K) := by
  refine comp_continuousLinearMap_mem_gammaZero_of_range_meets_domain
    φ hφ firstLastPullbackMap ?_
  rcases hφ.2.nonempty with ⟨p, hp⟩
  refine ⟨p, ⟨((p.1, (0 : K)), p.2), rfl⟩, hp⟩

/-- Pulling a `Γ₀` function back along the first-difference map preserves `Γ₀`. -/
theorem firstDifferencePullback_mem_gammaZero
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(H × K)) :
    ψ ∘ firstDifferencePullbackMap ∈ Γ₀((H × K) × K) := by
  refine comp_continuousLinearMap_mem_gammaZero_of_range_meets_domain
    ψ hψ firstDifferencePullbackMap ?_
  rcases hψ.2.nonempty with ⟨p, hp⟩
  refine ⟨p, ⟨((p.1, p.2), (0 : K)), ?_⟩, hp⟩
  simp

/-- The two lifted effective domains have a free `K` factor in each remaining coordinate. -/
theorem lifted_effectiveDomain_difference_eq_firstProjection_product_univ
    (φ ψ : H × K → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (φ ∘ firstLastPullbackMap) -
        effectiveDomain (ψ ∘ firstDifferencePullbackMap) =
      ((((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
          (Set.univ : Set K)) : Set (H × K)) ×ˢ (Set.univ : Set K)) := by
  ext q
  constructor
  · intro hq
    rcases Set.mem_sub.mp hq with ⟨p, hp, r, hr, hpr⟩
    have hp_dom : (p.1.1, p.2) ∈ effectiveDomain φ := by
      simpa [Function.comp, firstLastPullbackMap_apply, mem_effectiveDomain_iff] using hp
    have hr_dom : (r.1.1, r.1.2 - r.2) ∈ effectiveDomain ψ := by
      simpa [Function.comp, firstDifferencePullbackMap_apply, mem_effectiveDomain_iff] using hr
    have hfirst : p.1.1 - r.1.1 = q.1.1 := by
      simpa using congrArg (fun s : (H × K) × K ↦ s.1.1) hpr
    refine ⟨?_, by simp⟩
    refine ⟨?_, by simp⟩
    refine ⟨(p.1.1, p.2) - (r.1.1, r.1.2 - r.2), ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨(p.1.1, p.2), hp_dom, (r.1.1, r.1.2 - r.2), hr_dom, rfl⟩
    · simp [hfirst]
  · intro hq
    have hfirst : q.1.1 ∈ Prod.fst '' (effectiveDomain φ - effectiveDomain ψ) := by
      simpa using hq
    rcases hfirst with ⟨d, hd, hdq⟩
    rcases Set.mem_sub.mp hd with ⟨u, hu, v, hv, huv⟩
    let p : (H × K) × K := ((u.1, q.1.2 + v.2 + u.2 - q.2), u.2)
    let r : (H × K) × K := ((v.1, v.2 + u.2 - q.2), u.2 - q.2)
    have hp_dom : p ∈ effectiveDomain (φ ∘ firstLastPullbackMap) := by
      simpa [p, Function.comp, firstLastPullbackMap_apply, mem_effectiveDomain_iff] using hu
    have hr_dom : r ∈ effectiveDomain (ψ ∘ firstDifferencePullbackMap) := by
      simpa [r, Function.comp, firstDifferencePullbackMap_apply, mem_effectiveDomain_iff] using hv
    have hcoord : u.1 - v.1 = q.1.1 := by
      calc
        u.1 - v.1 = Prod.fst d := by simpa using congrArg Prod.fst huv
        _ = q.1.1 := hdq
    refine Set.mem_sub.mpr ⟨p, hp_dom, r, hr_dom, ?_⟩
    ext <;> simp [p, r, hcoord]

set_option maxHeartbeats 2000000 in
-- The raw-product cone equality requires elaborating nested product Hilbert structures.
/-- A free product factor preserves strong relative interior at the origin. -/
theorem zero_mem_sri_prod_univ_of_zero_mem_sri
    {S : Set H} (hconv : Convex ℝ S)
    (hsri : (0 : H) ∈ Set.strongRelativeInterior S) :
    (0 : H × K) ∈ Set.strongRelativeInterior (S ×ˢ (Set.univ : Set K)) := by
  have hzero : (0 : H) ∈ S := (Set.mem_strongRelativeInterior_iff.mp hsri).1
  have hconeS :
      Set.cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
    simpa [Set.sub_singleton_zero_eq_self] using
      (Set.mem_strongRelativeInterior_iff.mp hsri).2
  have hcone_prod :
      Set.cone (S ×ˢ (Set.univ : Set K)) =
        Set.cone S ×ˢ (Set.univ : Set K) := by
    ext p
    constructor
    · intro hp
      rcases (ConvexCone.mem_hull_of_convex (hconv.prod convex_univ)).1 hp with
        ⟨a, ha, q, hq, rfl⟩
      refine ⟨?_, by simp⟩
      exact (ConvexCone.mem_hull_of_convex hconv).2 ⟨a, ha, q.1, hq.1, rfl⟩
    · rintro ⟨hp, -⟩
      rcases (ConvexCone.mem_hull_of_convex hconv).1 hp with
        ⟨a, ha, x, hx, hax⟩
      refine (ConvexCone.mem_hull_of_convex (hconv.prod convex_univ)).2
        ⟨a, ha, (x, a⁻¹ • p.2), ⟨hx, by simp⟩, ?_⟩
      ext <;> simp [hax, ha.ne', smul_smul]
  have hspan_le :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) ≤
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    simpa [Submodule.span_univ] using
      (Submodule.span_prod_le (R := ℝ) S (Set.univ : Set K))
  have hspan_ge :
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) ≤
        Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := by
    have hsubset :
        LinearMap.inl ℝ H K '' S ∪ LinearMap.inr ℝ H K '' (Set.univ : Set K) ⊆
          S ×ˢ (Set.univ : Set K) := by
      intro p hp
      rcases hp with ⟨x, hx, rfl⟩ | ⟨y, _, rfl⟩
      · exact ⟨hx, by simp⟩
      · exact ⟨hzero, by simp⟩
    calc
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) =
          Submodule.span ℝ
            (LinearMap.inl ℝ H K '' S ∪
              LinearMap.inr ℝ H K '' (Set.univ : Set K)) := by
        symm
        simpa [Submodule.span_univ] using
          (LinearMap.span_inl_union_inr (R := ℝ) (M := H) (M₂ := K)
            (s := S) (t := (Set.univ : Set K)))
      _ ≤ Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) :=
        Submodule.span_mono hsubset
  have hspan_eq :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) =
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) :=
    le_antisymm hspan_le hspan_ge
  have hclosure_prod :
      ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure :
          Set (H × K)) =
        (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ
          (Set.univ : Set K)) := by
    rw [hspan_eq]
    change closure (((Submodule.span ℝ S).prod
        (⊤ : Submodule ℝ K) : Set (H × K))) = _
    rw [show (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) :
        Submodule ℝ (H × K)) : Set (H × K)) =
          ((Submodule.span ℝ S : Set H) ×ˢ (Set.univ : Set K)) by rfl]
    rw [closure_prod_eq]
    simp
  apply Set.mem_strongRelativeInterior_iff.mpr
  constructor
  · exact ⟨hzero, by simp⟩
  · simpa [Set.sub_singleton_zero_eq_self, hcone_prod, hconeS] using hclosure_prod.symm

/-- Projected strong-relative-interior regularity lifts to the two pullback domains. -/
theorem zero_mem_sri_lifted_effectiveDomain_difference
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hconv : Convex ℝ
      (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)))
    (hsri : (0 : H) ∈
      Set.strongRelativeInterior
        (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))) :
    (0 : (H × K) × K) ∈
      Set.strongRelativeInterior
        (effectiveDomain (φ ∘ firstLastPullbackMap) -
          effectiveDomain (ψ ∘ firstDifferencePullbackMap)) := by
  have hsri_prod :
      (0 : H × K) ∈
        Set.strongRelativeInterior
          ((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
            (Set.univ : Set K)) :=
    zero_mem_sri_prod_univ_of_zero_mem_sri hconv hsri
  have hsri_lifted :
      (0 : (H × K) × K) ∈
        Set.strongRelativeInterior
          (((Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) ×ˢ
            (Set.univ : Set K)) ×ˢ (Set.univ : Set K)) :=
    zero_mem_sri_prod_univ_of_zero_mem_sri
      (hconv.prod convex_univ) hsri_prod
  rw [lifted_effectiveDomain_difference_eq_firstProjection_product_univ]
  exact hsri_lifted

/-- The projected regularity condition for two `Γ₀` functions is the regularity condition for
their lifted pullbacks. -/
theorem zero_mem_sri_lifted_effectiveDomain_difference_of_gammaZero
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈
      Set.strongRelativeInterior
        (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))) :
    (0 : (H × K) × K) ∈
      Set.strongRelativeInterior
        (effectiveDomain (φ ∘ firstLastPullbackMap) -
          effectiveDomain (ψ ∘ firstDifferencePullbackMap)) := by
  have hconv :
      Convex ℝ (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)) := by
    exact
      (hφ.2.convex_effectiveDomain.sub hψ.2.convex_effectiveDomain).linear_image
        (ContinuousLinearMap.fst ℝ H K).toLinearMap
  exact zero_mem_sri_lifted_effectiveDomain_difference φ ψ hconv hsri

/-- The lifted pointwise sum is a proper lower-semicontinuous convex function under the
projected strong-relative-interior condition. -/
theorem liftedPullbackSum_mem_gammaZero_of_zero_mem_sri
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (hsri : (0 : H) ∈
      Set.strongRelativeInterior
        (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ))) :
    (φ ∘ firstLastPullbackMap) + (ψ ∘ firstDifferencePullbackMap) ∈
      Γ₀((H × K) × K) := by
  exact pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
    (φ ∘ firstLastPullbackMap) (ψ ∘ firstDifferencePullbackMap)
    (firstLastPullback_mem_gammaZero φ hφ)
    (firstDifferencePullback_mem_gammaZero ψ hψ)
    (zero_mem_sri_lifted_effectiveDomain_difference_of_gammaZero φ ψ hφ hψ hsri)

/-- On the zero middle dual slice, the first-last pullback conjugate is the original conjugate. -/
theorem conjugate_firstLastPullback_zeroSlice
    (φ : H × K → Set.Ioi (⊥ : EReal)) (u : H) (v : K) :
    ERealFunction.conjugate (φ ∘ firstLastPullbackMap).asEReal
        (((u, (0 : K)), v)) =
      ERealFunction.conjugate φ.asEReal (u, v) := by
  rw [conjugate_apply, conjugate_apply]
  apply le_antisymm
  · refine iSup_le fun r ↦ ?_
    have hinner :
        inner ℝ r (((u, (0 : K)), v)) =
          inner ℝ (r.1.1, r.2) (u, v) := by
      simp [prod_inner_l2_apply]
    simpa [Function.asEReal_apply, Function.comp, hinner] using
      (le_iSup
        (fun p : H × K ↦
          ((inner ℝ p (u, v) : ℝ) : EReal) - φ.asEReal p)
        (r.1.1, r.2))
  · refine iSup_le fun p ↦ ?_
    have hinner :
        inner ℝ (((p.1, (0 : K)), p.2)) (((u, (0 : K)), v)) =
          inner ℝ p (u, v) := by
      simp [prod_inner_l2_apply]
    simpa [Function.asEReal_apply, Function.comp, hinner] using
      (le_iSup
        (fun r : (H × K) × K ↦
          ((inner ℝ r (((u, (0 : K)), v)) : ℝ) : EReal) -
            (φ ∘ firstLastPullbackMap).asEReal r)
        ((p.1, (0 : K)), p.2))

/-- On the opposite last dual slice, the first-difference pullback conjugate is the original
conjugate. -/
theorem conjugate_firstDifferencePullback_negSlice
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (u : H) (b : K) :
    ERealFunction.conjugate (ψ ∘ firstDifferencePullbackMap).asEReal
        (((u, b), -b)) =
      ERealFunction.conjugate ψ.asEReal (u, b) := by
  rw [conjugate_apply, conjugate_apply]
  apply le_antisymm
  · refine iSup_le fun r ↦ ?_
    have hinner :
        inner ℝ r (((u, b), -b)) =
          inner ℝ (r.1.1, r.1.2 - r.2) (u, b) := by
      simp [prod_inner_l2_apply, inner_sub_left]
      ring
    simpa [Function.asEReal_apply, Function.comp, hinner] using
      (le_iSup
        (fun p : H × K ↦
          ((inner ℝ p (u, b) : ℝ) : EReal) - ψ.asEReal p)
        (r.1.1, r.1.2 - r.2))
  · refine iSup_le fun p ↦ ?_
    have hinner :
        inner ℝ (((p.1, p.2), (0 : K))) (((u, b), -b)) =
          inner ℝ p (u, b) := by
      simp [prod_inner_l2_apply]
    simpa [Function.asEReal_apply, Function.comp, hinner] using
      (le_iSup
        (fun r : (H × K) × K ↦
          ((inner ℝ r (((u, b), -b)) : ℝ) : EReal) -
            (ψ ∘ firstDifferencePullbackMap).asEReal r)
        ((p.1, p.2), (0 : K)))

private theorem iSup_inner_add_real_eq_top
    (b : K) (hb : b ≠ 0) (c : ℝ) :
    (⨆ y : K, ((inner ℝ y b + c : ℝ) : EReal)) = ⊤ := by
  have hb_sq : 0 < ‖b‖ ^ 2 := by
    have hb_norm : 0 < ‖b‖ := norm_pos_iff.mpr hb
    positivity
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  let t : ℝ := (M - c + 1) / ‖b‖ ^ 2
  have hreal : M < inner ℝ (t • b) b + c := by
    have heq : inner ℝ (t • b) b + c = M + 1 := by
      dsimp [t]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hb_sq.ne']
      ring
    linarith
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hreal)
    (le_iSup (fun y : K ↦ ((inner ℝ y b + c : ℝ) : EReal)) (t • b))

/-- A nonzero middle dual coordinate makes the first-last pullback conjugate infinite. -/
theorem conjugate_firstLastPullback_top_of_ne_zero
    (φ : H × K → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H × K))
    (u : H) (b v : K) (hb : b ≠ 0) :
    ERealFunction.conjugate (φ ∘ firstLastPullbackMap).asEReal
      (((u, b), v)) = ⊤ := by
  rcases hφ.2.nonempty with ⟨⟨x, z⟩, hp⟩
  have htop : (φ (x, z) : EReal) ≠ ⊤ :=
    (mem_effectiveDomain_iff.mp hp).ne
  have hbot : (φ (x, z) : EReal) ≠ ⊥ :=
    ne_of_gt (φ (x, z)).2
  let a : ℝ := (φ (x, z) : EReal).toReal
  have hφval : (φ (x, z) : EReal) = (a : EReal) :=
    (EReal.coe_toReal htop hbot).symm
  let c : ℝ := inner ℝ x u + inner ℝ z v - a
  have hsup := iSup_inner_add_real_eq_top b hb c
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  have hM : (M : EReal) <
      ⨆ y : K, ((inner ℝ y b + c : ℝ) : EReal) := by
    rw [hsup]
    exact EReal.coe_lt_top M
  rcases lt_iSup_iff.mp hM with ⟨y, hy⟩
  have hterm :
      ((inner ℝ y b + c : ℝ) : EReal) =
        ((inner ℝ (((x, y), z)) (((u, b), v)) : ℝ) : EReal) -
          (φ (x, z) : EReal) := by
    rw [hφval, prod_inner_l2_apply, prod_inner_l2_apply, ← EReal.coe_sub]
    congr 1
    dsimp [c]
    ring
  calc
    (M : EReal) < ((inner ℝ y b + c : ℝ) : EReal) := hy
    _ = ((inner ℝ (((x, y), z)) (((u, b), v)) : ℝ) : EReal) -
          (φ (x, z) : EReal) := hterm
    _ ≤ _ := by
      simpa [Function.asEReal_apply, Function.comp] using
        (le_iSup
          (fun r : (H × K) × K ↦
            ((inner ℝ r (((u, b), v)) : ℝ) : EReal) -
              (φ ∘ firstLastPullbackMap).asEReal r)
          ((x, y), z))

/-- Away from the opposite last dual slice, the first-difference pullback conjugate is infinite. -/
theorem conjugate_firstDifferencePullback_top_of_ne_neg
    (ψ : H × K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(H × K))
    (u : H) (b c : K) (hc : c ≠ -b) :
    ERealFunction.conjugate (ψ ∘ firstDifferencePullbackMap).asEReal
      (((u, b), c)) = ⊤ := by
  rcases hψ.2.nonempty with ⟨⟨x, z⟩, hp⟩
  have htop : (ψ (x, z) : EReal) ≠ ⊤ :=
    (mem_effectiveDomain_iff.mp hp).ne
  have hbot : (ψ (x, z) : EReal) ≠ ⊥ :=
    ne_of_gt (ψ (x, z)).2
  let a : ℝ := (ψ (x, z) : EReal).toReal
  have hψval : (ψ (x, z) : EReal) = (a : EReal) :=
    (EReal.coe_toReal htop hbot).symm
  have hbc : b + c ≠ 0 := by
    intro h
    apply hc
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h)
  let d : ℝ := inner ℝ x u + inner ℝ z b - a
  have hsup := iSup_inner_add_real_eq_top (b + c) hbc d
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  have hM : (M : EReal) <
      ⨆ y : K, ((inner ℝ y (b + c) + d : ℝ) : EReal) := by
    rw [hsup]
    exact EReal.coe_lt_top M
  rcases lt_iSup_iff.mp hM with ⟨y, hy⟩
  have hterm :
      ((inner ℝ y (b + c) + d : ℝ) : EReal) =
        ((inner ℝ (((x, z + y), y)) (((u, b), c)) : ℝ) : EReal) -
          (ψ (x, z) : EReal) := by
    rw [hψval, prod_inner_l2_apply, prod_inner_l2_apply, ← EReal.coe_sub]
    congr 1
    dsimp [d]
    rw [inner_add_left, inner_add_right]
    ring
  calc
    (M : EReal) < ((inner ℝ y (b + c) + d : ℝ) : EReal) := hy
    _ = ((inner ℝ (((x, z + y), y)) (((u, b), c)) : ℝ) : EReal) -
          (ψ (x, z) : EReal) := hterm
    _ ≤ _ := by
      simpa [Function.asEReal_apply, Function.comp] using
        (le_iSup
          (fun r : (H × K) × K ↦
            ((inner ℝ r (((u, b), c)) : ℝ) : EReal) -
              (ψ ∘ firstDifferencePullbackMap).asEReal r)
          ((x, z + y), y))

theorem conjugate_apply_prod_zeroSecond
    (F : (H × K) × K → EReal) (u : H × K) :
    ERealFunction.conjugate F (u, (0 : K)) =
      ⨆ p : (H × K) × K, (((inner ℝ p.1 u : ℝ) : EReal) - F p) := by
  rw [ERealFunction.conjugate_apply]
  congr with p
  congr 1
  simpa using (prod_inner_l2_apply p (u, (0 : K)))

omit [CompleteSpace H] [CompleteSpace K] in
theorem infimalPostcomposition_fst_apply
    (F : (H × K) × K → EReal) (x : H × K) :
    ERealFunction.infimalPostcomposition Prod.fst F x = ⨅ y : K, F (x, y) := by
  change sInf (F '' (Prod.fst ⁻¹' ({x} : Set (H × K)))) = _
  rw [show F '' (Prod.fst ⁻¹' ({x} : Set (H × K))) =
      Set.range (fun y : K ↦ F (x, y)) by
    ext z
    constructor
    · rintro ⟨⟨a, b⟩, ha, rfl⟩
      refine ⟨b, ?_⟩
      simp at ha
      simp [ha]
    · rintro ⟨y, rfl⟩
      exact ⟨(x, y), by simp, rfl⟩]
  exact sInf_range

theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond
    (F : (H × K) × K → EReal) :
    ERealFunction.conjugate (ERealFunction.infimalPostcomposition Prod.fst F) =
      fun u : H × K ↦ ERealFunction.conjugate F (u, (0 : K)) := by
  funext u
  rw [ERealFunction.conjugate_apply]
  simp_rw [infimalPostcomposition_fst_apply]
  rw [conjugate_apply_prod_zeroSecond]
  calc
    (⨆ x : H × K, (((inner ℝ x u : ℝ) : EReal) - ⨅ y : K, F (x, y))) =
        (⨆ x : H × K, ⨆ y : K, (((inner ℝ x u : ℝ) : EReal) - F (x, y))) := by
      refine iSup_congr fun x ↦ ?_
      let a : EReal := ((inner ℝ x u : ℝ) : EReal)
      have hupper :
          (⨆ y : K, a - F (x, y)) ≤ a - ⨅ y : K, F (x, y) := by
        apply Antitone.le_map_iInf
        intro s t hst
        exact EReal.sub_le_sub le_rfl hst
      have hlower : a - ⨅ y : K, F (x, y) ≤ ⨆ y : K, a - F (x, y) := by
        rw [show (⨅ y : K, F (x, y)) = sInf (Set.range (fun y : K ↦ F (x, y))) by
          symm
          exact sInf_range]
        refine le_of_forall_lt fun c hc ↦ ?_
        have hc' : c < a - (⨅ y : K, F (x, y)) := by
          simpa [sInf_range] using hc
        have hne_top : (⨅ y : K, F (x, y)) ≠ ⊤ := by
          intro htop
          have hcbot : c < (⊥ : EReal) := by simpa [htop] using hc'
          exact (not_lt_of_ge bot_le) hcbot
        obtain ⟨y, hy, hyc⟩ := (sInf_lt_iff).1 <| by
          have hadd : (⨅ y : K, F (x, y)) + c < a := by
            have htmp : c + (⨅ y : K, F (x, y)) < a :=
              (EReal.lt_sub_iff_add_lt (a := a) (b := (⨅ y : K, F (x, y))) (c := c)
                (Or.inr hc'.ne_top) (Or.inl hne_top)).1 hc'
            simpa [add_comm] using htmp
          exact
            (EReal.lt_sub_iff_add_lt (a := a) (b := c)
              (c := (⨅ y : K, F (x, y))) (Or.inr hne_top) (Or.inl hc'.ne_top)).2 hadd
        rcases hy with ⟨y, rfl⟩
        have hlt : c < a - F (x, y) := by
          apply (EReal.lt_sub_iff_add_lt (a := a) (b := F (x, y)) (c := c)
            (Or.inr hc'.ne_top) (Or.inl (ne_top_of_lt hyc))).2
          simpa [add_comm] using EReal.add_lt_of_lt_sub hyc
        exact lt_of_lt_of_le hlt (le_iSup (fun y : K ↦ a - F (x, y)) y)
      exact le_antisymm hlower hupper
    _ = ⨆ p : (H × K) × K, (((inner ℝ p.1 u : ℝ) : EReal) - F p) := by
      rw [iSup_prod']

theorem secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted
    (φ ψ : H × K → Set.Ioi (⊥ : EReal)) :
    (fun p : H × K ↦
      (ERealFunction.infimalConvolution
        (fun z : K ↦ (φ (p.1, z) : EReal))
        (fun z : K ↦ (ψ (p.1, z) : EReal)) p.2)) =
      ERealFunction.infimalPostcomposition Prod.fst
        (fun q : (H × K) × K ↦
          (φ (q.1.1, q.2) : EReal) + (ψ (q.1.1, q.1.2 - q.2) : EReal)) := by
  funext p
  rw [infimalPostcomposition_fst_apply]
  rfl

/-- A fixed split of the first dual coordinate bounds the conjugate of a fiberwise infimal
convolution. No regularity or attainment hypothesis is needed for this weak-duality direction. -/
theorem conjugate_secondVariableFiberwiseInfimalConvolution_le_split
    (φ ψ : H × K → Set.Ioi (⊥ : EReal)) (q : H × K) (v : H) :
    ERealFunction.conjugate
        (fun p : H × K ↦ ⨅ z : K,
          (φ (p.1, z) : EReal) + (ψ (p.1, p.2 - z) : EReal)) q ≤
      ERealFunction.conjugate φ.asEReal (v, q.2) +
        ERealFunction.conjugate ψ.asEReal (q.1 - v, q.2) := by
  let Φ : ((H × K) × K) → Set.Ioi (⊥ : EReal) := φ ∘ firstLastPullbackMap
  let Ψ : ((H × K) × K) → Set.Ioi (⊥ : EReal) := ψ ∘ firstDifferencePullbackMap
  have hrepr :
      (fun p : H × K ↦ ⨅ z : K,
        (φ (p.1, z) : EReal) + (ψ (p.1, p.2 - z) : EReal)) =
        ERealFunction.infimalPostcomposition Prod.fst
          (Φ.asEReal + Ψ.asEReal) := by
    simpa [Φ, Ψ, Function.asEReal_apply, Pi.add_apply, Function.comp] using
      (secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted φ ψ)
  have hΦ :
      ERealFunction.conjugate Φ.asEReal (((v, (0 : K)), q.2)) ≤
        ERealFunction.conjugate φ.asEReal (v, q.2) := by
    rw [conjugate_apply, conjugate_apply]
    refine iSup_le fun r ↦ ?_
    have hinner :
        inner ℝ r (((v, (0 : K)), q.2)) =
          inner ℝ (r.1.1, r.2) (v, q.2) := by
      simp [prod_inner_l2_apply]
    simpa [Φ, Function.asEReal_apply, Function.comp, hinner] using
      (le_iSup
        (fun s : H × K ↦
          ((inner ℝ s (v, q.2) : ℝ) : EReal) - φ.asEReal s)
        (r.1.1, r.2))
  have hΨ :
      ERealFunction.conjugate Ψ.asEReal (((q.1 - v, q.2), -q.2)) ≤
        ERealFunction.conjugate ψ.asEReal (q.1 - v, q.2) := by
    rw [conjugate_apply, conjugate_apply]
    refine iSup_le fun r ↦ ?_
    have hinner :
        inner ℝ r (((q.1 - v, q.2), -q.2)) =
          inner ℝ (r.1.1, r.1.2 - r.2) (q.1 - v, q.2) := by
      simp [prod_inner_l2_apply, inner_sub_left]
      ring
    simpa [Ψ, Function.asEReal_apply, Function.comp, hinner] using
      (le_iSup
        (fun s : H × K ↦
          ((inner ℝ s (q.1 - v, q.2) : ℝ) : EReal) - ψ.asEReal s)
        (r.1.1, r.1.2 - r.2))
  rw [hrepr, conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond]
  have hsplit :
      ((q, (0 : K)) : (H × K) × K) -
          (((v, (0 : K)), q.2) : (H × K) × K) =
        ((q.1 - v, q.2), -q.2) := by
    ext <;> simp
  calc
    ERealFunction.conjugate (Φ.asEReal + Ψ.asEReal) (q, (0 : K)) ≤
        (ERealFunction.conjugate Φ.asEReal □
          ERealFunction.conjugate Ψ.asEReal) (q, (0 : K)) := by
      simpa [Function.asEReal_apply] using
        (conjugate_add_le_infimalConvolution_conjugate Φ Ψ (q, (0 : K)))
    _ ≤ ERealFunction.conjugate Φ.asEReal (((v, (0 : K)), q.2)) +
          ERealFunction.conjugate Ψ.asEReal (((q.1 - v, q.2), -q.2)) := by
      rw [infimalConvolution_apply]
      simpa [hsplit] using
        (iInf_le
          (fun s : (H × K) × K ↦
            ERealFunction.conjugate Φ.asEReal s +
              ERealFunction.conjugate Ψ.asEReal ((q, (0 : K)) - s))
          (((v, (0 : K)), q.2)))
    _ ≤ ERealFunction.conjugate φ.asEReal (v, q.2) +
          ERealFunction.conjugate ψ.asEReal (q.1 - v, q.2) :=
      add_le_add hΦ hΨ

/-- Under an attained Fenchel split for the lifted pointwise sum, the zero-second slice of its
conjugate is the first-variable infimal convolution of the original conjugate slices. -/
theorem conjugate_secondVariableFiberwiseInfimalConvolution_eq_firstVariableInfimalConvolution_of_split_attainment
    (φ ψ : H × K → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H × K)) (hψ : ψ ∈ Γ₀(H × K))
    (_hsri : (0 : H) ∈ Set.strongRelativeInterior
      (Prod.fst '' (effectiveDomain φ - effectiveDomain ψ)))
    (hattain : ∀ q : (H × K) × K, ∃ r : (H × K) × K,
      ERealFunction.conjugate
          ((φ ∘ firstLastPullbackMap) + (ψ ∘ firstDifferencePullbackMap)).asEReal q =
        ERealFunction.conjugate (φ ∘ firstLastPullbackMap).asEReal r +
          ERealFunction.conjugate (ψ ∘ firstDifferencePullbackMap).asEReal (q - r)) :
    (fun p : H × K ↦
      (ERealFunction.infimalConvolution
        (fun z : K ↦ (φ (p.1, z) : EReal))
        (fun z : K ↦ (ψ (p.1, z) : EReal)) p.2))∗ =
      fun q : H × K ↦
        ((fun v : H ↦ φ.asEReal∗ (v, q.2)) □
          fun v ↦ ψ.asEReal∗ (v, q.2)) q.1 := by
  let Φ : (H × K) × K → Set.Ioi (⊥ : EReal) := φ ∘ firstLastPullbackMap
  let Ψ : (H × K) × K → Set.Ioi (⊥ : EReal) := ψ ∘ firstDifferencePullbackMap
  have hΦ : Φ ∈ Γ₀((H × K) × K) :=
    firstLastPullback_mem_gammaZero φ hφ
  have hΨ : Ψ ∈ Γ₀((H × K) × K) :=
    firstDifferencePullback_mem_gammaZero ψ hψ
  have hsum :
      (Φ + Ψ).asEReal∗ = Φ.asEReal∗ □ Ψ.asEReal∗ :=
    (fenchelRockafellar_of_split_attainment Φ Ψ hΦ hΨ hattain).1
  have hrepr :
      (fun p : H × K ↦
        (ERealFunction.infimalConvolution
          (fun z : K ↦ (φ (p.1, z) : EReal))
          (fun z : K ↦ (ψ (p.1, z) : EReal)) p.2)) =
        ERealFunction.infimalPostcomposition Prod.fst
          (Φ.asEReal + Ψ.asEReal) := by
    simpa [Φ, Ψ, Function.asEReal_apply, Pi.add_apply, Function.comp] using
      (secondVariableFiberwiseInfimalConvolution_eq_infimalPostcomposition_lifted φ ψ)
  funext q
  rw [hrepr, conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond]
  have hsum' :
      (Φ.asEReal + Ψ.asEReal)∗ = Φ.asEReal∗ □ Ψ.asEReal∗ := by
    simpa [Function.asEReal_apply, Pi.add_apply] using hsum
  rw [hsum']
  rw [infimalConvolution_apply]
  apply le_antisymm
  · refine le_iInf fun v ↦ ?_
    refine iInf_le_of_le (((v, (0 : K)), q.2)) ?_
    change ERealFunction.conjugate Φ.asEReal ((v, (0 : K)), q.2) +
        ERealFunction.conjugate Ψ.asEReal ((q, (0 : K)) - ((v, (0 : K)), q.2)) ≤ _
    have hΦv : ERealFunction.conjugate Φ.asEReal ((v, (0 : K)), q.2) =
        ERealFunction.conjugate φ.asEReal (v, q.2) := by
      simpa [Φ] using conjugate_firstLastPullback_zeroSlice φ v q.2
    have harg : (q, (0 : K)) - ((v, (0 : K)), q.2) =
        ((q.1 - v, q.2), -q.2) := by
      ext <;> simp
    have hΨv : ERealFunction.conjugate Ψ.asEReal
          ((q, (0 : K)) - ((v, (0 : K)), q.2)) =
        ERealFunction.conjugate ψ.asEReal (q.1 - v, q.2) := by
      rw [harg]
      simpa [Ψ] using conjugate_firstDifferencePullback_negSlice ψ (q.1 - v) q.2
    rw [hΦv, hΨv]
  · refine le_iInf fun r ↦ ?_
    rcases r with ⟨⟨v, b⟩, c⟩
    change (⨅ y : H, φ.asEReal∗ (y, q.2) + ψ.asEReal∗ (q.1 - y, q.2)) ≤
      ERealFunction.conjugate Φ.asEReal ((v, b), c) +
        ERealFunction.conjugate Ψ.asEReal ((q, (0 : K)) - ((v, b), c))
    by_cases hb : b = 0
    · subst b
      by_cases hc : c = q.2
      · subst c
        have hΦv : ERealFunction.conjugate Φ.asEReal ((v, (0 : K)), q.2) =
            ERealFunction.conjugate φ.asEReal (v, q.2) := by
          simpa [Φ] using conjugate_firstLastPullback_zeroSlice φ v q.2
        have harg : (q, (0 : K)) - ((v, (0 : K)), q.2) =
            ((q.1 - v, q.2), -q.2) := by
          ext <;> simp
        have hΨv : ERealFunction.conjugate Ψ.asEReal
              ((q, (0 : K)) - ((v, (0 : K)), q.2)) =
            ERealFunction.conjugate ψ.asEReal (q.1 - v, q.2) := by
          rw [harg]
          simpa [Ψ] using conjugate_firstDifferencePullback_negSlice ψ (q.1 - v) q.2
        rw [hΦv, hΨv]
        exact iInf_le (fun v' : H ↦
          φ.asEReal∗ (v', q.2) + ψ.asEReal∗ (q.1 - v', q.2)) v
      · have htop :
            ERealFunction.conjugate Ψ.asEReal
                ((q.1 - v, q.2), -c) = ⊤ := by
          simpa [Ψ] using conjugate_firstDifferencePullback_top_of_ne_neg ψ hψ
            (q.1 - v) q.2 (-c) (by
              intro heq
              apply hc
              simpa using congrArg Neg.neg heq)
        have hΦv : ERealFunction.conjugate Φ.asEReal ((v, (0 : K)), c) =
            ERealFunction.conjugate φ.asEReal (v, c) := by
          simpa [Φ] using conjugate_firstLastPullback_zeroSlice φ v c
        have harg : (q, (0 : K)) - ((v, (0 : K)), c) =
            ((q.1 - v, q.2), -c) := by
          ext <;> simp
        rw [hΦv, harg, htop]
        rw [EReal.add_top_of_ne_bot
          (conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hφ) (v, c))]
        exact le_top
    · have htop :
          ERealFunction.conjugate Φ.asEReal (((v, b), c)) = ⊤ :=
        by simpa [Φ] using conjugate_firstLastPullback_top_of_ne_zero φ hφ v b c hb
      rw [htop]
      rw [EReal.top_add_of_ne_bot
        (conjugate_ne_bot_of_isProper (isProper_of_mem_gammaZero hΨ)
          ((q, (0 : K)) - ((v, b), c)))]
      exact le_top

end ERealFunction
