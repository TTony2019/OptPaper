import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_6
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_6
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter

/-- The operator distance `def_6` is symmetric in its two arguments. -/
theorem def_6_comm {H : Type*} [NormedAddCommGroup H] (r : ℝ) (hr : 0 < r)
    (A B : H → H) : def_6 r hr A B = def_6 r hr B A := by
  simp only [def_6, supDiscrepancyOnBall]
  congr 1
  ext q
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by rw [norm_sub_rev]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by rw [norm_sub_rev]⟩

/-- On the ball of radius `r`, the discrepancy of two operators is bounded by
  the paper's distance `def_6 r`, which is the supremum of that discrepancy
  (`hbdd` records the finiteness of that supremum). -/
theorem le_def_6 {H : Type*} [NormedAddCommGroup H] {r : ℝ} (hr : 0 < r) {A B : H → H}
    (hbdd : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A u - B u‖})
    {u : H} (hu : ‖u‖ ≤ r) : ‖A u - B u‖ ≤ def_6 r hr A B := by
  simp only [def_6, supDiscrepancyOnBall]
  exact le_csSup hbdd ⟨u, hu, rfl⟩

/-- The operator distance `def_6` is nonnegative (it is a supremum of norms). -/
theorem def_6_nonneg {H : Type*} [NormedAddCommGroup H] (r : ℝ) (hr : 0 < r)
    (A B : H → H) : 0 ≤ def_6 r hr A B := by
  rw [def_6, supDiscrepancyOnBall]
  exact Real.sSup_nonneg fun q hq => by
    obtain ⟨u, _, rfl⟩ := hq
    exact norm_nonneg _

/-- Corollary 6.5, corrected: For each μ, let x_μ be the unique solution of
  DIN(φ,μ).  Assume βγ>1, each φ(⋅,μ) is differentiable and δ_μ-strongly convex,
  and for given r,T>0, x_μ(t)∈B(0,r) a.e.  Then the D_r estimate holds,
  x_μ(t) strongly converges to the unique x̄_μ of (PM_μ), and
  `‖x̄_μ−x̄_{μ′}‖ ≤ c⁻¹ D_r(∇φ_μ,∇φ_μ′)` with the sharp energy rate
  `c = max (energyRate β γ δ_μ) (energyRate β γ δ_μ')`.

  Deviations from the paper (the previous proof deduced `Subsingleton H` from
  `int(argmin φ(·,μ)) ≠ ∅` and strong convexity, which is contradictory on any
  nontrivial `H`, trivializing every conclusion):

  * `int(argmin φ(·,μ)) ≠ ∅` is dropped; `x̄_μ` is identified by the first-order
    condition `∇φ(·,μ) x̄_μ = 0`, from which membership in `Optimization.argminSet`
    is *derived*;
  * the finiteness of `D_r` is made explicit (`hbdd`), since `def_6` is a
    supremum and the estimate is false for an infinite discrepancy;
  * the rate is the sharp `energyRate` rather than the paper's `δ`, and the
    energy strong monotonicity is *derived* from strong convexity
    (`energyStrong_of_strongConvex`), not assumed;
  * the ball hypothesis is assumed for every `T > 0` (not a single one): this is
    what the paper's asymptotic conclusion `‖x̄_μ - x̄_μ'‖ ≤ δ⁻¹D_r` requires,
    since it is obtained by letting `t → ∞` in the estimate;
  * consequently the estimate below is available for *every* `t ∈ [0,T]`. -/
theorem cor_4 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M)
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (xbar : M → H) (u₀ v₀ : M → H)
    (β γ : ℝ) (δ : M → ℝ) (r T : ℝ)
    (hβγ : β * γ > 1) (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 0 < r) (hT : 0 < T)
    (hdiff : ∀ μ ∈ V, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ ∈ V, ∀ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ ∈ V, IsStronglyConvex (φ μ) (δ μ))
    (hDIN : ∀ μ, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (hball : ∀ μ ∈ V, ∀ T' > 0, ∀ᵐ t ∂ MeasureTheory.volume,
      t ∈ Set.Icc (0 : ℝ) T' → ‖x μ t‖ ≤ r)
    (hbdd : ∀ μ ∈ V, ∀ μ' ∈ V,
      BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖gradφ μ u - gradφ μ' u‖})
    (hcrit : ∀ μ ∈ V, gradφ μ (xbar μ) = 0) :
    (∀ μ ∈ V, ∀ μ' ∈ V, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤ Real.exp (-cmax * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          β * cmax⁻¹ * (1 - Real.exp (-cmax * t)) * def_6 r hr (gradφ μ) (gradφ μ')) ∧
    (∀ μ ∈ V, Tendsto (x μ) atTop (nhds (xbar μ)) ∧ xbar μ ∈ Optimization.argminSet (φ μ)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ‖xbar μ - xbar μ'‖ ≤ β * cmax⁻¹ * def_6 r hr (gradφ μ) (gradφ μ')) := by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  -- Pointwise, oriented estimate on the whole half-line: the discrepancy of the
  -- two gradient fields is bounded by `β D_r` along the ball-constrained trajectory.
  have key (a b : M) (ha : a ∈ V) (hb : b ∈ V) : ∀ t, 0 ≤ t →
      ‖x a t - x b t‖ ≤ Real.exp (-(energyRate β γ (δ b)) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        (energyRate β γ (δ b))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ b)) * t)) *
          (β * def_6 r hr (gradφ a) (gradφ b)) := by
    intro t ht
    have hT : 0 < t + 1 := by linarith
    refine din_oriented_comparison gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) a b
      hlift (fun p q => energyStrong_of_strongConvex (μ := b) hβ hβγ (hstrong b hb) (hgrad b hb) p q)
      (energyRate_pos hβ hγ (hstrong b hb).1 hβγ) (β * def_6 r hr (gradφ a) (gradφ b))
      (mul_nonneg hβ.le (def_6_nonneg r hr (gradφ a) (gradφ b))) (t + 1) hT ?_
      t ht (by linarith)
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (hball a ha (t + 1) hT)] with s hs
    have hfst : (DINGradientField gradφ β γ a (hlift.X a s)).1 -
        (DINGradientField gradφ β γ b (hlift.X a s)).1 =
        β • (gradφ a (hlift.X a s).1 - gradφ b (hlift.X a s).1) := by
      dsimp [DINGradientField]
      module
    have hsnd : (DINGradientField gradφ β γ a (hlift.X a s)).2 -
        (DINGradientField gradφ β γ b (hlift.X a s)).2 = 0 := by
      dsimp [DINGradientField]
      simp
    rw [hfst, hsnd, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), norm_smul,
      Real.norm_of_nonneg hβ.le]
    have hxr : ‖(hlift.X a s).1‖ ≤ r := by
      simpa [hlift.fst_eq a s] using hs
    exact mul_le_mul_of_nonneg_left (le_def_6 hr (hbdd a ha b hb) hxr) hβ.le
  -- The symmetric `max` form, valid for every `t ≥ 0`.
  have hbound (a b : M) (ha : a ∈ V) (hb : b ∈ V) : ∀ t, 0 ≤ t →
      ‖x a t - x b t‖ ≤
        Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        β * (max (energyRate β γ (δ a)) (energyRate β γ (δ b)))⁻¹ *
          (1 - Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t)) *
            def_6 r hr (gradφ a) (gradφ b) := by
    by_cases hc : energyRate β γ (δ a) ≤ energyRate β γ (δ b)
    · intro t ht
      calc ‖x a t - x b t‖ ≤ Real.exp (-(energyRate β γ (δ b)) * t) *
            Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
              dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
          (energyRate β γ (δ b))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ b)) * t)) *
            (β * def_6 r hr (gradφ a) (gradφ b)) := key a b ha hb t ht
        _ = Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t) *
              Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
                dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
            β * (max (energyRate β γ (δ a)) (energyRate β γ (δ b)))⁻¹ *
              (1 - Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t)) *
                def_6 r hr (gradφ a) (gradφ b) := by
          rw [max_eq_right hc]
          ring
    · have hc' : energyRate β γ (δ b) ≤ energyRate β γ (δ a) := le_of_not_ge hc
      intro t ht
      calc ‖x a t - x b t‖ = ‖x b t - x a t‖ := by rw [norm_sub_rev]
        _ ≤ Real.exp (-(energyRate β γ (δ a)) * t) *
              Real.sqrt (‖u₀ b - u₀ a‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ b -
                dinAuxInitial gradφ β γ u₀ v₀ a‖ ^ 2) +
            (energyRate β γ (δ a))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ a)) * t)) *
              (β * def_6 r hr (gradφ b) (gradφ a)) := key b a hb ha t ht
        _ = Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t) *
              Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
                dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
            β * (max (energyRate β γ (δ a)) (energyRate β γ (δ b)))⁻¹ *
              (1 - Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t)) *
                def_6 r hr (gradφ a) (gradφ b) := by
          rw [max_eq_left hc', norm_sub_rev (u₀ b) (u₀ a),
            norm_sub_rev (dinAuxInitial gradφ β γ u₀ v₀ b) (dinAuxInitial gradφ β γ u₀ v₀ a),
            def_6_comm r hr (gradφ b) (gradφ a)]
          ring
  refine ⟨?_, ?_, ?_⟩
  · -- the D_r estimate on [0,T]
    intro μ hμ μ' hμ'
    dsimp only
    exact Filter.Eventually.of_forall fun t ht => hbound μ μ' hμ hμ' t ht.1
  · intro μ hμ
    exact ⟨din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
        (fun p q => energyStrong_of_strongConvex (μ := μ) hβ hβγ (hstrong μ hμ) (hgrad μ hμ) p q) hβ
        (energyRate_pos hβ hγ (hstrong μ hμ).1 hβγ) (hcrit μ hμ),
      mem_argminSet_of_grad_eq_zero (hstrong μ hμ) (hgrad μ hμ) (hcrit μ hμ)⟩
  · -- minimizer gap: let t → ∞ in the estimate
    intro μ hμ μ' hμ'
    dsimp only
    have hpt := hbound μ μ' hμ hμ'
    have hconv : Tendsto (fun t : ℝ => ‖x μ t - x μ' t‖) atTop (nhds ‖xbar μ - xbar μ'‖) :=
      (((din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
          (fun p q => energyStrong_of_strongConvex (μ := μ) hβ hβγ (hstrong μ hμ) (hgrad μ hμ) p q) hβ
          (energyRate_pos hβ hγ (hstrong μ hμ).1 hβγ) (hcrit μ hμ)).sub
        (din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
          (fun p q => energyStrong_of_strongConvex (μ := μ') hβ hβγ (hstrong μ' hμ') (hgrad μ' hμ') p q) hβ
          (energyRate_pos hβ hγ (hstrong μ' hμ').1 hβγ) (hcrit μ' hμ')))).norm
    have hlim : Tendsto (fun t : ℝ =>
        Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t)) *
              def_6 r hr (gradφ μ) (gradφ μ')) atTop
        (nhds (β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ *
          def_6 r hr (gradφ μ) (gradφ μ'))) := by
      have hc : 0 < max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) :=
        lt_max_of_lt_left (energyRate_pos hβ hγ (hstrong μ hμ).1 hβγ)
      have hexp : Tendsto (fun t : ℝ =>
          Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      have h1 : Tendsto (fun t : ℝ =>
          Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t)) *
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
            dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2)) atTop (nhds 0) := by
        simpa using hexp.mul tendsto_const_nhds
      have h2 : Tendsto (fun t : ℝ =>
          β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) *
            def_6 r hr (gradφ μ) (gradφ μ')) atTop
          (nhds (β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ * (1 - 0) *
            def_6 r hr (gradφ μ) (gradφ μ'))) :=
        ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)).mul tendsto_const_nhds)
      simpa using h1.add h2
    refine le_of_tendsto_of_tendsto hconv hlim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hpt t ht

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
