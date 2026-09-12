import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter

/-! ### The stationary point of the first-order reformulation

`DIN` is equivalent (for `βγ > 1`) to the gradient system `Ẋ = -∇ε(X)` with
`ε(x,z) = βφ(x) + 1/(2β)‖√(γβ-1) x + z‖²`.  A critical point `x̄` of `φ`
therefore becomes the stationary point `(x̄, -√(γβ-1) x̄)` of that system. -/

/-- The auxiliary coordinate `z̄ = -√(γβ-1) x̄` making `(x̄, z̄)` a stationary
point of the first-order reformulation whenever `∇φ x̄ = 0`. -/
noncomputable def DINStationaryAux {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (β γ : ℝ) (xbar : H) : H :=
  -(Real.sqrt (γ * β - 1) • xbar)

/-- Scalar identity underlying `DINGradientField_stationary`. -/
theorem sqrt_one_div_mul_sqrt_gammaBeta_sub_one {β γ : ℝ} (hβ : 0 < β) :
    Real.sqrt (1 / β) * Real.sqrt (γ * β - 1) = Real.sqrt (γ - 1 / β) := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 / β) (γ * β - 1)]
  congr 1
  field_simp

/-- At a critical point of `φ`, the gradient field of the first-order
reformulation vanishes at `(x̄, DINStationaryAux β γ x̄)`. -/
theorem DINGradientField_stationary {H M : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {gradφ : M → H → H} {β γ : ℝ} (hβ : 0 < β) {μ : M} {xbar : H}
    (hcrit : gradφ μ xbar = 0) :
    DINGradientField gradφ β γ μ (xbar, DINStationaryAux β γ xbar) = 0 := by
  have hinner : Real.sqrt (γ - 1 / β) • xbar +
      Real.sqrt (1 / β) • DINStationaryAux β γ xbar = 0 := by
    dsimp [DINStationaryAux]
    rw [smul_neg, ← mul_smul, sqrt_one_div_mul_sqrt_gammaBeta_sub_one hβ,
      ← neg_smul, ← add_smul, add_neg_cancel, zero_smul]
  refine Prod.ext ?_ ?_
  · dsimp [DINGradientField]
    rw [hinner, hcrit]
    simp
  · dsimp [DINGradientField]
    rw [hinner]
    simp

/-! ### Convergence of `DIN` trajectories to critical points -/

/-- Comparing a `DIN` trajectory with the constant trajectory sitting at the
stationary point `(x̄, DINStationaryAux β γ x̄)` of the first-order
reformulation gives exponential decay towards the critical point `x̄`, at the
sharp energy rate `c`. -/
theorem din_exponential_decay_to_critical {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (gradφ : M → H → H) (x : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ) (c : M → ℝ)
    (hlift : DINGradientLift gradφ x u₀ v₀ β γ) {μ : M} {xbar : H}
    (henergyStrong : ∀ (p q : H × H),
      c μ * (‖p.1 - q.1‖ ^ 2 + ‖p.2 - q.2‖ ^ 2) ≤
        inner ℝ ((DINGradientField gradφ β γ μ p).1 -
          (DINGradientField gradφ β γ μ q).1) (p.1 - q.1) +
        inner ℝ ((DINGradientField gradφ β γ μ p).2 -
          (DINGradientField gradφ β γ μ q).2) (p.2 - q.2))
    (hβ : 0 < β) (hc : 0 < c μ) (hcrit : gradφ μ xbar = 0) :
    ∀ t, 0 ≤ t → ‖x μ t - xbar‖ ≤
      Real.exp (-(c μ) * t) *
        Real.sqrt (‖u₀ μ - xbar‖ ^ 2 +
          ‖dinAuxInitial gradφ β γ u₀ v₀ μ - DINStationaryAux β γ xbar‖ ^ 2) := by
  intro t ht
  have hfield : DINGradientField gradφ β γ μ (xbar, DINStationaryAux β γ xbar) = 0 :=
    DINGradientField_stationary (β := β) (γ := γ) hβ hcrit
  have hT : 0 < t + 1 := by linarith
  have hraw := two_component_flow_estimate (X := hlift.X μ)
    (Y := fun _ : ℝ => (xbar, DINStationaryAux β γ xbar))
    (F := DINGradientField gradφ β γ μ) (G := DINGradientField gradφ β γ μ)
    (u₀ μ) (dinAuxInitial gradφ β γ u₀ v₀ μ) xbar (DINStationaryAux β γ xbar)
    (c μ) 0 (t + 1) hc le_rfl hT
    (hlift.initial μ) rfl (hlift.locally_ac μ (t + 1) hT)
    (((contDiff_const : ContDiff ℝ 1
      (fun _ : ℝ => (xbar, DINStationaryAux β γ xbar))).contDiffOn).absolutelyContinuousOnInterval)
    (hlift.flow μ (t + 1) hT)
    (by
      filter_upwards with s
      simpa [hfield] using hasDerivAt_const s (xbar, DINStationaryAux β γ xbar))
    (by intro p q; simpa using henergyStrong p q)
    (by filter_upwards with s; simp)
    t ht (by linarith)
  simpa [hlift.fst_eq μ t] using hraw

/-- `DIN` trajectories converge strongly to every critical point of `φ`. -/
theorem din_tendsto_to_critical {H M : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (gradφ : M → H → H) (x : M → ℝ → H) (u₀ v₀ : M → H) (β γ : ℝ) (c : M → ℝ)
    (hlift : DINGradientLift gradφ x u₀ v₀ β γ) {μ : M} {xbar : H}
    (henergyStrong : ∀ (p q : H × H),
      c μ * (‖p.1 - q.1‖ ^ 2 + ‖p.2 - q.2‖ ^ 2) ≤
        inner ℝ ((DINGradientField gradφ β γ μ p).1 -
          (DINGradientField gradφ β γ μ q).1) (p.1 - q.1) +
        inner ℝ ((DINGradientField gradφ β γ μ p).2 -
          (DINGradientField gradφ β γ μ q).2) (p.2 - q.2))
    (hβ : 0 < β) (hc : 0 < c μ) (hcrit : gradφ μ xbar = 0) :
    Tendsto (x μ) atTop (nhds xbar) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hdecay := din_exponential_decay_to_critical gradφ x u₀ v₀ β γ c hlift henergyStrong
    hβ hc hcrit
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(c μ * t))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
  have hg : Tendsto (fun t : ℝ =>
      Real.sqrt (‖u₀ μ - xbar‖ ^ 2 +
          ‖dinAuxInitial gradφ β γ u₀ v₀ μ - DINStationaryAux β γ xbar‖ ^ 2) *
        Real.exp (-(c μ * t))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  calc ‖x μ t - xbar‖ ≤
      Real.exp (-(c μ) * t) *
        Real.sqrt (‖u₀ μ - xbar‖ ^ 2 +
          ‖dinAuxInitial gradφ β γ u₀ v₀ μ - DINStationaryAux β γ xbar‖ ^ 2) :=
        hdecay t ht
    _ = Real.sqrt (‖u₀ μ - xbar‖ ^ 2 +
          ‖dinAuxInitial gradφ β γ u₀ v₀ μ - DINStationaryAux β γ xbar‖ ^ 2) *
        Real.exp (-(c μ * t)) := by
      ring_nf

/-! ### Critical points of strongly convex functions are minimizers -/

/-- A critical point of a strongly convex function is a global minimizer. -/
theorem mem_argminSet_of_grad_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → ℝ} {g : H → H} {δ : ℝ}
    (hsc : IsStronglyConvex f δ) (hg : ∀ q, HasGradientAt f (g q) q) {xbar : H}
    (hcrit : g xbar = 0) : xbar ∈ Optimization.argminSet f := by
  rw [Optimization.mem_argminSet_iff]
  intro w
  have h := strong_convex_gradient_gap hsc (hg xbar) (q := w)
  rw [hcrit] at h
  simp only [inner_zero_left] at h
  have hδ : 0 < δ := hsc.1
  have hnonneg : 0 ≤ δ / 2 * ‖xbar - w‖ ^ 2 := by positivity
  linarith

/-- At a minimizer of a differentiable function the gradient vanishes (Fermat's
  rule; the converse of `mem_argminSet_of_grad_eq_zero`). -/
theorem grad_eq_zero_of_mem_argminSet {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → ℝ} {g : H → H}
    (hg : ∀ q, HasGradientAt f (g q) q) {z : H}
    (hz : z ∈ Optimization.argminSet f) : g z = 0 := by
  have hloc : IsLocalMin f z := Filter.Eventually.of_forall fun y => hz y
  have hzero : InnerProductSpace.toDual ℝ H (g z) = 0 :=
    hloc.hasFDerivAt_eq_zero (hg z).hasFDerivAt
  have h1 : inner ℝ (g z) (g z) = 0 := by
    simpa [InnerProductSpace.toDual_apply_apply] using
      congrArg (fun L : H →L[ℝ] ℝ => L (g z)) hzero
  exact inner_self_eq_zero.mp h1

/-- Minimizers of a strongly convex function are unique. -/
theorem argminSet_subsingleton_of_strongConvex {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → ℝ} {δ : ℝ} (hsc : IsStronglyConvex f δ) :
    (Optimization.argminSet f).Subsingleton := by
  intro y hy z hz
  by_contra hne
  have hyz : f y = f z := le_antisymm (hy z) (hz y)
  have hmid : f y ≤ f ((1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • z) := hy _
  have hineq := hsc.2 y z (1 / 2) (by norm_num) (by norm_num)
  rw [hyz] at hineq
  ring_nf at hineq
  have hnorm : 0 < ‖y - z‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  nlinarith [hsc.1, hnorm]

/-- Theorem 6.2: For each μ, let x_μ be the unique solution of DIN(φ,μ) and
  suppose that argmin φ(⋅,μ)≠∅. Under the hypotheses of Theorem 6.1,
  (x_μ(t)) converges strongly to the unique solution x̄_μ of (PM_μ), and the
  minimizer distance bound (23) holds for δ=max(δ_μ,δ_μ′).

  Deviations from the paper: the paper additionally assumes
  `int(argmin φ(·,μ)) ≠ ∅`, which together with δ_μ-strong convexity forces
  `Subsingleton H` and hence makes the statement vacuous on any nontrivial `H`;
  it is dropped here.  Instead, `x̄_μ` is identified by the first-order
  optimality condition `∇φ(·,μ) x̄_μ = 0`, from which membership in
  `Optimization.argminSet (φ μ)` (and thus the paper's existence assumption) is
  *derived*.  Strong convergence is proved by the exponential energy estimate of
  `din_exponential_decay_to_critical` rather than by quoting [10, Prop. 5.1],
  and (23) follows by passing to the limit `t → ∞` in Theorem 6.1's estimate. -/
theorem thm_6 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (xbar : M → H)
    (β γ : ℝ) (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (hcrit : ∀ μ : M, gradφ μ (xbar μ) = 0) :
    (∀ μ : M, Tendsto (x μ) atTop (nhds (xbar μ))) ∧
    (∀ μ : M, xbar μ ∈ Optimization.argminSet (φ μ)) ∧
    (∀ μ μ' : M, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ‖xbar μ - xbar μ'‖ ≤ (β * k₁ / cmax) * ‖μ - μ'‖ ^ γ₁) := by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  have hconv : ∀ μ : M, Tendsto (x μ) atTop (nhds (xbar μ)) := fun μ =>
    din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
      (fun p q => energyStrong_of_strongConvex hβ hβγ (hstrong μ) (hgrad μ) p q)
      hβ (energyRate_pos hβ hγ (hstrong μ).1 hβγ) (hcrit μ)
  refine ⟨hconv, fun μ => mem_argminSet_of_grad_eq_zero (hstrong μ) (hgrad μ) (hcrit μ), ?_⟩
  intro μ μ'
  dsimp only
  have hpt : ∀ t, 0 ≤ t → ‖x μ t - x μ' t‖ ≤
      Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t) *
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
            dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
        (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t)) *
            ‖μ - μ'‖ ^ γ₁ := fun t ht =>
    thm_5_estimate_all φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ hdiff hgrad
      hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μ' t ht
  have hlim2 : Tendsto (fun t : ℝ =>
      Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t) *
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
            dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
        (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t)) *
            ‖μ - μ'‖ ^ γ₁) atTop
      (nhds ((β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
        ‖μ - μ'‖ ^ γ₁)) := by
    have hc : 0 < max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) :=
      lt_max_of_lt_left (energyRate_pos hβ hγ (hstrong μ).1 hβγ)
    have hexp : Tendsto (fun t : ℝ =>
        Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
    have h1 : Tendsto (fun t : ℝ =>
        Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t)) *
        Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
          dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2)) atTop (nhds 0) := by
      simpa using hexp.mul tendsto_const_nhds
    have h2 : Tendsto (fun t : ℝ =>
        (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
        (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) *
          ‖μ - μ'‖ ^ γ₁) atTop
        (nhds ((β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
          (1 - 0) * ‖μ - μ'‖ ^ γ₁)) :=
      ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)).mul tendsto_const_nhds)
    simpa using h1.add h2
  refine le_of_tendsto_of_tendsto ((hconv μ).sub (hconv μ')).norm hlim2 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hpt t ht

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
