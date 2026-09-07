import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_8
namespace Alvarez2002
open Filter
open scoped Topology

private theorem contDiffOn_two_of_hasDerivAt_of_contDiffOn_one {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {f f' : ℝ → H}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hderiv : ∀ t, t ∈ s → HasDerivAt f (f' t) t)
    (hf' : ContDiffOn ℝ 1 f' s) :
    ContDiffOn ℝ 2 f s := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro h
    simp at h
  · have heq : ∀ t, t ∈ s → derivWithin f s t = f' t := by
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (hs t ht)
    exact hf'.congr (fun t ht => heq t ht)

/--
Theorem 6.1: (human checked)
Equivalence of `(DIN)` and `(g-DIN)` under `a = α - 1/β`, `b = 1/β`,
with compatible initial data.
-/
theorem din_iff_gdin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (Φ : H → ℝ) (α β a b : ℝ) (x : ℝ → H)
  (x₀ y₀ : H)
  (hΦ : ContDiff ℝ 2 Φ)
  (hx : ContDiff ℝ 2 x)
  (hαpos : 0 < α) (hβpos : 0 < β)
  (ha : a = α - 1 / β) (hb : b = 1 / β)
  (hx₀ : x 0 = x₀)
  (hy₀ : y₀ = -(β • deriv x 0 + (β ^ 2) • gradient Φ (x 0) + (β * a) • x 0)) :
  (IsDINTrajectory H Φ α β x) ↔
  ∃ y : ℝ → H, (ContDiffOn ℝ 2 y (Set.Ici 0)) ∧ IsSolution_gDIN Φ β a b x₀ y₀ x y := by
  have hβ : β ≠ 0 := ne_of_gt hβpos
  have hba : β * a = β * α - 1 := by
    rw [ha]
    field_simp [hβ]
  have hab : a + b = α := by
    rw [ha, hb]
    ring
  have hbβ : b * β = 1 := by
    rw [hb]
    field_simp [hβ]
  have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by simpa using hΦ)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgradDeriv : ∀ z, HasFDerivAt (gradient Φ)
      (fderiv ℝ (gradient Φ) z) z := by
    intro z
    exact (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  have hxDeriv : ∀ t, HasDerivAt x (deriv x t) t := by
    intro t
    exact (hx.differentiable (by norm_num) t).hasDerivAt
  have hvDeriv : ∀ t, HasDerivAt (deriv x) (deriv (deriv x) t) t := by
    intro t
    exact (hx.differentiable_deriv_two t).hasDerivAt
  have hvC1 : ContDiff ℝ 1 (deriv x) := by
    exact (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) x by simpa using hx)).2.2
  have hgradCompC1 : ContDiff ℝ 1 (fun t => gradient Φ (x t)) := by
    simpa [Function.comp_def] using
      hgradC1.comp (hx.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  constructor
  · rintro ⟨_, _, hEq⟩
    let y : ℝ → H := fun t =>
      -(β • deriv x t + (β ^ 2) • gradient Φ (x t) + (β * a) • x t)
    let dy : ℝ → H := fun t => deriv x t + β • gradient Φ (x t)
    have hgradx : ∀ t, HasDerivAt (fun s => gradient Φ (x s))
        ((fderiv ℝ (gradient Φ) (x t)) (deriv x t)) t := by
      intro t
      simpa [Function.comp_def] using
        (hgradDeriv (x t)).comp_hasDerivAt t (hxDeriv t)
    have hfirst : ∀ t, 0 ≤ t →
        deriv x t + β • gradient Φ (x t) + a • x t + b • y t = 0 := by
      intro t ht
      dsimp [y]
      rw [hb]
      simp only [smul_neg, smul_add, smul_smul]
      rw [show (1 / β) * β = 1 by field_simp [hβ],
        show (1 / β) * β ^ 2 = β by field_simp [hβ],
        show (1 / β) * (β * a) = a by field_simp [hβ]]
      module
    have hdy : ∀ t, 0 ≤ t → HasDerivAt y (dy t) t := by
      intro t ht
      have hyraw : HasDerivAt y
          (-(β • deriv (deriv x) t + (β ^ 2) •
            (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            (β * a) • deriv x t)) t := by
        dsimp [y]
        have hsum := ((hvDeriv t).const_smul β).add
          ((hgradx t).const_smul (β ^ 2))
        have hsum' := hsum.add ((hxDeriv t).const_smul (β * a))
        exact hsum'.neg
      have hacc : deriv (deriv x) t =
          -(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            gradient Φ (x t)) := by
        exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hEq t ht)
      convert hyraw using 1
      rw [hacc]
      dsimp [dy]
      simp only [smul_neg, smul_add, smul_smul]
      rw [hba]
      module
    have hdyC1 : ContDiff ℝ 1 dy := by
      dsimp [dy]
      exact hvC1.add (hgradCompC1.const_smul β)
    have hyC2 : ContDiffOn ℝ 2 y (Set.Ici 0) :=
      contDiffOn_two_of_hasDerivAt_of_contDiffOn_one (uniqueDiffOn_Ici 0) hdy
        hdyC1.contDiffOn
    refine ⟨y, hyC2, ?_⟩
    dsimp [IsSolution_gDIN]
    refine ⟨hfirst, ?_, hx₀, ?_⟩
    · intro t ht
      rw [(hdy t ht).deriv]
      simpa [dy] using hfirst t ht
    · simpa [y] using hy₀.symm
  · rintro ⟨y, hyC2, hgDIN⟩
    rcases hgDIN with ⟨hfirst, hsecond, hx0, hy0⟩
    refine ⟨hαpos, hβpos, ?_⟩
    have hDIN_pos : ∀ t, 0 < t →
        deriv (deriv x) t + α • deriv x t +
          β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            gradient Φ (x t) = 0 := by
      intro t ht
      have hdyEq : deriv y t = deriv x t + β • gradient Φ (x t) := by
        have hsub : deriv x t + β • gradient Φ (x t) - deriv y t = 0 := by
          calc
            deriv x t + β • gradient Φ (x t) - deriv y t =
                (deriv x t + β • gradient Φ (x t) + a • x t + b • y t) -
                  (deriv y t + a • x t + b • y t) := by module
            _ = 0 := by rw [hfirst t ht.le, hsecond t ht.le]; module
        exact (sub_eq_zero.mp hsub).symm
      have hgradx : HasDerivAt (fun s => gradient Φ (x s))
          ((fderiv ℝ (gradient Φ) (x t)) (deriv x t)) t := by
        simpa [Function.comp_def] using
          (hgradDeriv (x t)).comp_hasDerivAt t (hxDeriv t)
      have hyAt : HasDerivAt y (deriv y t) t := by
        exact (hyC2.differentiableOn (by norm_num)).hasDerivAt (Ici_mem_nhds ht)
      have hR : HasDerivAt (fun s =>
          -(β • gradient Φ (x s) + a • x s + b • y s))
          (-(β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            a • deriv x t + b • deriv y t)) t := by
        exact (((hgradx.const_smul β).add ((hxDeriv t).const_smul a)).add
          (hyAt.const_smul b)).neg
      have hxEq : (fun s => deriv x s) =ᶠ[𝓝 t] (fun s =>
          -(β • gradient Φ (x s) + a • x s + b • y s)) := by
        filter_upwards [Ici_mem_nhds ht] with s hs
        exact eq_neg_iff_add_eq_zero.mpr
          (by simpa [add_assoc] using hfirst s hs)
      have hvraw : HasDerivAt (deriv x)
          (-(β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            a • deriv x t + b • deriv y t)) t :=
        hR.congr_of_eventuallyEq hxEq
      have hsecondDeriv := hvraw.deriv
      rw [hsecondDeriv, hdyEq]
      simp only [smul_add, smul_smul]
      rw [← hab, add_smul, hbβ, one_smul]
      module
    let res : ℝ → H := fun t =>
      deriv (deriv x) t + α • deriv x t +
        β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t)
    have hresCont : Continuous res := by
      have hclm : Continuous (fun t =>
          (fderiv ℝ (gradient Φ) (x t)) (deriv x t)) := by
        exact (hgradC1.continuous_fderiv one_ne_zero).comp hx.continuous |>.clm_apply
          (hx.continuous_deriv (by norm_num))
      dsimp [res]
      have hc1 := (hvC1.continuous_deriv_one).add
        ((hx.continuous_deriv (by norm_num)).const_smul α)
      have hc2 := hc1.add (hclm.const_smul β)
      have hc3 := hc2.add hgradCompC1.continuous
      simpa only [Pi.add_apply] using hc3
    have hresOn : Set.EqOn res (fun _ => (0 : H)) (Set.Ioi 0) := by
      intro t ht
      exact hDIN_pos t ht
    have hresClosure := hresOn.closure hresCont continuous_const
    have hzero : res 0 = 0 := by
      have h := hresClosure (show (0 : ℝ) ∈ closure (Set.Ioi 0) by
        rw [closure_Ioi]
        exact Set.self_mem_Ici)
      exact h
    intro t ht
    by_cases ht0 : t = 0
    · simpa [res, ht0] using hzero
    · exact hDIN_pos t (lt_of_le_of_ne ht (Ne.symm ht0))
end Alvarez2002
