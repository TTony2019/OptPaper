import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_3
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_lem_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_thm_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

/-- A cocoercive force field generates a global classical solution of the
associated damped second-order system. -/
private theorem exists_damped_solution_of_cocoercive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → H) (γ : ℝ) (u₀ v₀ : H) (α : ℝ)
    (hγ : 0 < γ) (hα : 0 < α)
    (hco : ∀ u v : H,
      α * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v)) :
    ∃ x dx ddx : ℝ → H, ext_def_2 A γ u₀ v₀ x dx ddx := by
  let F : H × H → H × H := fun p => (p.2, -γ • p.2 - A p.1)
  let L : ℝ := 1 + |γ| + α⁻¹
  have hL : 0 < L := by
    dsimp [L]
    have hinv : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
    linarith [abs_nonneg γ]
  have hAlip : ∀ u v : H, ‖A u - A v‖ ≤ α⁻¹ * ‖u - v‖ :=
    cocoercive_lipschitz hα hco
  have hFlip : ∀ p q : H × H, ‖F p - F q‖ ≤ L * ‖p - q‖ := by
    intro p q
    have hfst : ‖p.1 - q.1‖ ≤ ‖p - q‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    have hsnd : ‖p.2 - q.2‖ ≤ ‖p - q‖ := by
      rw [Prod.norm_def]
      exact le_max_right _ _
    have hsecond :
        ‖(-γ • p.2 - A p.1) - (-γ • q.2 - A q.1)‖ ≤
          (|γ| + α⁻¹) * ‖p - q‖ := by
      rw [show (-γ • p.2 - A p.1) - (-γ • q.2 - A q.1) =
          -γ • (p.2 - q.2) - (A p.1 - A q.1) by module]
      calc
        ‖-γ • (p.2 - q.2) - (A p.1 - A q.1)‖ ≤
            ‖-γ • (p.2 - q.2)‖ + ‖A p.1 - A q.1‖ := norm_sub_le _ _
        _ ≤ |γ| * ‖p - q‖ + α⁻¹ * ‖p - q‖ := by
          apply add_le_add
          · rw [norm_smul, Real.norm_eq_abs, abs_neg]
            exact mul_le_mul_of_nonneg_left hsnd (abs_nonneg γ)
          · exact (hAlip p.1 q.1).trans
              (mul_le_mul_of_nonneg_left hfst (inv_nonneg.mpr hα.le))
        _ = (|γ| + α⁻¹) * ‖p - q‖ := by ring
    rw [show F p - F q =
        (p.2 - q.2, (-γ • p.2 - A p.1) - (-γ • q.2 - A q.1)) by
          ext <;> simp [F], Prod.norm_def]
    apply max_le
    · calc
        ‖p.2 - q.2‖ ≤ ‖p - q‖ := hsnd
        _ ≤ L * ‖p - q‖ := by
          calc
            ‖p - q‖ = 1 * ‖p - q‖ := by ring
            _ ≤ L * ‖p - q‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              dsimp [L]
              have hinv : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
              linarith [abs_nonneg γ]
    · exact hsecond.trans (by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [L]
        linarith)
  obtain ⟨Z, hZ, hZuniq⟩ := ext_thm_5 F L hL hFlip (u₀, v₀)
  let x : ℝ → H := fun t => (Z t).1
  let dx : ℝ → H := fun t => (Z t).2
  let ddx : ℝ → H := fun t => (F (Z t)).2
  have hZderiv (t : ℝ) : HasDerivAt Z (F (Z t)) t := by
    have hz := (hZ.1 t).hasDerivAt
    rw [(hZ.2.2 t).1] at hz
    exact hz
  have hxderiv (t : ℝ) : HasDerivAt x (dx t) t := by
    simpa [x, dx, F] using
      (hasDerivAt_const t (ContinuousLinearMap.fst ℝ H H)).clm_apply (hZderiv t)
  have hdxderiv (t : ℝ) : HasDerivAt dx (ddx t) t := by
    simpa [dx, ddx] using
      (hasDerivAt_const t (ContinuousLinearMap.snd ℝ H H)).clm_apply (hZderiv t)
  have hZcontDiff : ContDiff ℝ 1 Z :=
    contDiff_one_iff_deriv.mpr ⟨hZ.1, hZ.2.1⟩
  have hlac : IsLocallyAbsolutelyContinuous x dx := by
    intro T hT
    constructor
    · simpa [x] using hZcontDiff.fst.contDiffOn.absolutelyContinuousOnInterval
    · simpa [dx] using hZcontDiff.snd.contDiffOn.absolutelyContinuousOnInterval
  have hx0 : x 0 = u₀ := by
    simpa [x] using congrArg Prod.fst (hZ.2.2 0).2
  have hdx0 : dx 0 = v₀ := by
    simpa [dx] using congrArg Prod.snd (hZ.2.2 0).2
  have hode (t : ℝ) : ddx t + γ • dx t + A (x t) = 0 := by
    dsimp [ddx, dx, x, F]
    module
  have hdef : def_3 A γ u₀ v₀ x dx ddx := by
    refine ⟨hlac, hx0, hdx0, ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun t => hxderiv t
    · exact Filter.Eventually.of_forall fun t => hdxderiv t
    · exact Filter.Eventually.of_forall fun t => hode t
  exact ⟨x, dx, ddx, hγ, hdef⟩

/-- Stability of two damped trajectories under a uniform discrepancy bound on
their force fields. -/
theorem damped_solution_stability
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H → H) (γ : ℝ) (u₀ v₀ u₀' v₀' : H) (α α' D : ℝ)
    (hα : 0 < α) (hα' : 0 < α')
    (hA : ∀ u v : H,
      α * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v))
    (hB : ∀ u v : H,
      α' * ‖B u - B v‖ ^ 2 ≤ inner ℝ (B u - B v) (u - v))
    (hD0 : 0 ≤ D) (hD : ∀ u : H, ‖A u - B u‖ ≤ D)
    {x dx ddx x' dx' ddx' : ℝ → H}
    (hsol : ext_def_2 A γ u₀ v₀ x dx ddx)
    (hsol' : ext_def_2 B γ u₀' v₀' x' dx' ddx') :
    ∀ t, 0 ≤ t →
      let m := max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2))
        (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α' ^ 2))
      ‖x t - x' t‖ ≤
        Real.exp (m * t) *
          Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
        m⁻¹ * (Real.exp (m * t) - 1) * D := by
  intro t ht
  dsimp only
  rcases hsol with ⟨_, hdef⟩
  rcases hsol' with ⟨_, hdef'⟩
  rcases hdef with ⟨hlac, hx0, hdx0, hxderiv, hdxderiv, hode⟩
  rcases hdef' with ⟨hlac', hx0', hdx0', hxderiv', hdxderiv', hode'⟩
  have hxderiv_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderiv
  have hdxderiv_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderiv
  have hode_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hode
  have hxderiv_ae' := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderiv'
  have hdxderiv_ae' := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderiv'
  have hode_ae' := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hode'
  let T : ℝ := t + 1
  have hT : 0 < T := by
    dsimp [T]
    linarith
  obtain ⟨hxAC, hdxAC⟩ := hlac T hT
  obtain ⟨hxAC', hdxAC'⟩ := hlac' T hT
  let y : ℝ → H := fun s => x s - x' s
  let z : ℝ → H := fun s => dx s - dx' s
  let w : ℝ → ℝ := fun s => ‖y s‖ ^ 2 + ‖z s‖ ^ 2
  have hyAC : AbsolutelyContinuousOnInterval y 0 T := by
    simpa [y] using hxAC.fun_sub hxAC'
  have hzAC : AbsolutelyContinuousOnInterval z 0 T := by
    simpa [z] using hdxAC.fun_sub hdxAC'
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := by
    simpa [w] using (ac_norm_sq hyAC).fun_add (ac_norm_sq hzAC)
  have hw_nonneg (s : ℝ) : 0 ≤ w s := by
    dsimp [w]
    positivity
  have hw0 : w 0 = ‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2 := by
    simp only [w, y, z, hx0, hx0', hdx0, hdx0']
  have hwDeriv : ∀ᵐ s ∂MeasureTheory.volume, 0 ≤ s →
      HasDerivAt w
        (2 * inner ℝ (y s) (z s) +
          2 * inner ℝ (z s) (ddx s - ddx' s)) s := by
    filter_upwards [hxderiv_ae, hxderiv_ae', hdxderiv_ae, hdxderiv_ae'] with
      s hxs hxs' hdxs hdxs'
    intro hs
    have hyD : HasDerivAt y (z s) s := by
      simpa [y, z] using (hxs hs).sub (hxs' hs)
    have hzD : HasDerivAt z (ddx s - ddx' s) s := by
      simpa [z] using (hdxs hs).sub (hdxs' hs)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  let m : ℝ := max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2))
    (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α' ^ 2))
  have hmone : 1 ≤ m := by
    apply le_trans ?_ (le_max_right _ _)
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hsq : 0 ≤ γ ^ 2 := sq_nonneg _
    have hinv : 0 ≤ 2 / α' ^ 2 := by positivity
    linarith
  have hm0 : 0 ≤ m := by linarith
  have hm : 0 < m := by linarith
  have hfixed_pair (s : ℝ) :
      inner ℝ (y s) (z s) + inner ℝ (z s)
          (-γ • z s - (B (x s) - B (x' s))) ≤ m * w s := by
    have hbase := first_order_sq_bound (alpha := α') (gamma := γ) hα' hB
      (x s) (x' s) (dx s) (dx' s)
    have hbase' : ‖z s‖ ^ 2 + ‖-γ • z s - (B (x s) - B (x' s))‖ ^ 2 ≤
        (1 + 2 * γ ^ 2 + 2 / α' ^ 2) * w s := by
      rw [show -γ • dx s - B (x s) - (-γ • dx' s - B (x' s)) =
          -γ • (dx s - dx' s) - (B (x s) - B (x' s)) by module] at hbase
      simpa [z, w] using hbase
    have hcoef : 1 + 2 * γ ^ 2 + 2 / α' ^ 2 ≤ m ^ 2 := by
      have hnon : 0 ≤ 1 + 2 * γ ^ 2 + 2 / α' ^ 2 := by positivity
      have hsqrtle : Real.sqrt (1 + 2 * γ ^ 2 + 2 / α' ^ 2) ≤ m :=
        le_max_right _ _
      rw [← Real.sq_sqrt hnon]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hm0).mpr hsqrtle
    have hsq : ‖z s‖ ^ 2 + ‖-γ • z s - (B (x s) - B (x' s))‖ ^ 2 ≤
        m ^ 2 * w s :=
      hbase'.trans (mul_le_mul_of_nonneg_right hcoef (hw_nonneg s))
    have hpair := two_pairing_le (y s) (z s) (z s)
      (-γ • z s - (B (x s) - B (x' s)))
    have hsqrt : Real.sqrt (‖z s‖ ^ 2 +
        ‖-γ • z s - (B (x s) - B (x' s))‖ ^ 2) ≤
        m * Real.sqrt (w s) := by
      have hs := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs, abs_of_nonneg hm0] at hs
      exact hs
    have hwrt : Real.sqrt (w s) ^ 2 = w s := Real.sq_sqrt (hw_nonneg s)
    calc
      inner ℝ (y s) (z s) + inner ℝ (z s)
          (-γ • z s - (B (x s) - B (x' s))) ≤
          Real.sqrt (‖y s‖ ^ 2 + ‖z s‖ ^ 2) *
            Real.sqrt (‖z s‖ ^ 2 +
              ‖-γ • z s - (B (x s) - B (x' s))‖ ^ 2) := hpair
      _ ≤ Real.sqrt (w s) * (m * Real.sqrt (w s)) := by
        simpa [w] using mul_le_mul_of_nonneg_left hsqrt
          (Real.sqrt_nonneg (‖y s‖ ^ 2 + ‖z s‖ ^ 2))
      _ = m * w s := by nlinarith [hwrt]
  have hineq : ∀ᵐ s ∂MeasureTheory.volume, 0 ≤ s →
      (1 - (1 / 2 : ℝ)) * deriv w s ≤
        m * w s + D * w s ^ (1 / 2 : ℝ) := by
    filter_upwards [hode_ae, hode_ae', hwDeriv] with s hsode hsode' hsderiv
    intro hs
    have hddx : ddx s - ddx' s =
        (-γ • z s - (B (x s) - B (x' s))) - (A (x s) - B (x s)) := by
      have hddxA : ddx s = -γ • dx s - A (x s) := by
        calc
          ddx s = -(γ • dx s + A (x s)) :=
            eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hsode hs)
          _ = -γ • dx s - A (x s) := by module
      have hddxB : ddx' s = -γ • dx' s - B (x' s) := by
        calc
          ddx' s = -(γ • dx' s + B (x' s)) :=
            eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hsode' hs)
          _ = -γ • dx' s - B (x' s) := by module
      rw [hddxA, hddxB]
      dsimp [z]
      module
    have hz_le : ‖z s‖ ≤ Real.sqrt (w s) := by
      apply Real.le_sqrt_of_sq_le
      dsimp [w]
      nlinarith [sq_nonneg ‖y s‖]
    have hforce_pair :
        -inner ℝ (z s) (A (x s) - B (x s)) ≤ D * Real.sqrt (w s) := by
      calc
        -inner ℝ (z s) (A (x s) - B (x s)) ≤
            ‖z s‖ * ‖A (x s) - B (x s)‖ := by
          exact le_trans (le_abs_self _) (by
            simpa using norm_inner_le_norm (𝕜 := ℝ) (z s) (A (x s) - B (x s)))
        _ ≤ ‖z s‖ * D := mul_le_mul_of_nonneg_left (hD (x s)) (norm_nonneg _)
        _ ≤ Real.sqrt (w s) * D := mul_le_mul_of_nonneg_right hz_le hD0
        _ = D * Real.sqrt (w s) := by ring
    have henergy :
        inner ℝ (y s) (z s) + inner ℝ (z s) (ddx s - ddx' s) =
          (inner ℝ (y s) (z s) + inner ℝ (z s)
            (-γ • z s - (B (x s) - B (x' s)))) -
          inner ℝ (z s) (A (x s) - B (x s)) := by
      rw [hddx]
      simp only [inner_sub_right]
      ring
    have hderiv_eq : deriv w s =
        2 * (inner ℝ (y s) (z s) + inner ℝ (z s) (ddx s - ddx' s)) := by
      rw [(hsderiv hs).deriv]
      ring
    rw [hderiv_eq, henergy, ← Real.sqrt_eq_rpow]
    nlinarith [hfixed_pair s, hforce_pair]
  have hgronwall := ext_lem_1 (w := w) (a := fun _ : ℝ => m)
    (b := fun _ : ℝ => D) (t₀ := 0) (T := T) (α := (1 / 2 : ℝ))
    hT (by norm_num) (by norm_num) (by simpa using hwAC)
    (by intro s hs; exact hw_nonneg s) (by simp) (by simp)
    (Filter.Eventually.of_forall fun s hs => hD0)
    (by
      filter_upwards [hineq] with s hs
      intro hsIcc
      exact hs hsIcc.1)
  have hgr := hgronwall t ht (by dsimp [T]; linarith)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hkernel : (∫ s in 0..t, Real.exp ((t - s) * m)) =
      m⁻¹ * (Real.exp (m * t) - 1) := by
    calc
      (∫ s in 0..t, Real.exp ((t - s) * m)) =
          ∫ s in 0..t, Real.exp (m * (t - s)) * 1 := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with s hs
        congr 1
        ring
      _ = m⁻¹ * (Real.exp (m * t) - 1) * 1 := exp_kernel_integral m 1 t hm
      _ = m⁻¹ * (Real.exp (m * t) - 1) := by ring
  rw [hkernel] at hgr
  have hy_le : ‖x t - x' t‖ ≤ Real.sqrt (w t) := by
    change ‖y t‖ ≤ Real.sqrt (w t)
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  have hresult : ‖x t - x' t‖ ≤
      Real.exp (m * t) * Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
        m⁻¹ * (Real.exp (m * t) - 1) * D := by
    calc
      ‖x t - x' t‖ ≤ Real.sqrt (w t) := hy_le
      _ ≤ Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) *
            Real.exp (m * t) + m⁻¹ * (Real.exp (m * t) - 1) * D := by
        convert hgr using 1 <;> ring
      _ = Real.exp (m * t) *
            Real.sqrt (‖u₀ - u₀'‖ ^ 2 + ‖v₀ - v₀'‖ ^ 2) +
          m⁻¹ * (Real.exp (m * t) - 1) * D := by ring
  simpa [m] using hresult

/-- Theorem 3.1: Assume (C₁)-(C₂). For each μ∈V(μ̄) and (u₀^μ,v₀^μ)∈H×H,
  S(A_μ,u₀^μ,v₀^μ) admits a unique strong global solution x_μ and,
  if μ,μ′∈V(μ̄), then for a.e. t≥0 the estimate (3) holds, where
  m=max(m_μ,m_μ′) and m_μ=(1+2γ²+2/α_μ²)^{1/2}.

  Deviations of the statement from the paper: the trajectories are total
  functions `ℝ → H` whose values at negative times are unconstrained, so
  uniqueness is asserted only on the forward half axis (`Set.EqOn x y
  (Set.Ici 0)`) and only for `x` — `dx` and `ddx` occur existentially, as in
  `def_3`.  `γ > 0` is an explicit hypothesis of the module. -/
theorem thm_1 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (u₀ v₀ : M → H) (α : M → ℝ) (θ₁ θ₂ : ℝ)
    (hγ : 0 < γ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂) :
    (∀ μ ∈ V, ∃ x dx ddx : ℝ → H,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) x dx ddx ∧
        ∀ y dy ddy : ℝ → H, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) y dy ddy →
          Set.EqOn x y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V,
      let m_μ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))
      let m := max m_μ m_μ'
      (∃ x x' : ℝ → H, (∃ dx ddx : ℝ → H, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) x dx ddx) ∧
        (∃ dx' ddx' : ℝ → H, ext_def_2 (A μ') γ (u₀ μ') (v₀ μ') x' dx' ddx') ∧
        ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → ‖x t - x' t‖ ≤
          Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂)) := by
  constructor
  · intro μ hμ
    obtain ⟨x, dx, ddx, hx⟩ := exists_damped_solution_of_cocoercive
      (A μ) γ (u₀ μ) (v₀ μ) (α μ) hγ (hC₁ μ hμ).1 (hC₁ μ hμ).2
    refine ⟨x, dx, ddx, hx, ?_⟩
    intro y dy ddy hy t ht
    have hbound := damped_solution_stability (A μ) (A μ) γ
      (u₀ μ) (v₀ μ) (u₀ μ) (v₀ μ) (α μ) (α μ) 0
      (hC₁ μ hμ).1 (hC₁ μ hμ).1 (hC₁ μ hμ).2 (hC₁ μ hμ).2
      (by norm_num) (fun u => by simp) hx hy t ht
    have hzero : ‖x t - y t‖ = 0 := by
      apply le_antisymm
      · simpa using hbound
      · exact norm_nonneg _
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · intro μ hμ μ' hμ'
    dsimp only
    obtain ⟨x, dx, ddx, hx⟩ :=
      exists_damped_solution_of_cocoercive
        (A μ) γ (u₀ μ) (v₀ μ) (α μ) hγ (hC₁ μ hμ).1 (hC₁ μ hμ).2
    obtain ⟨x', dx', ddx', hx'⟩ :=
      exists_damped_solution_of_cocoercive
        (A μ') γ (u₀ μ') (v₀ μ') (α μ') hγ (hC₁ μ' hμ').1 (hC₁ μ' hμ').2
    let D : ℝ := θ₁ * ‖μ - μ'‖ ^ θ₂
    have hD0 : 0 ≤ D := by
      dsimp [D]
      exact mul_nonneg hC₂.1.le (Real.rpow_nonneg (norm_nonneg _) _)
    have hD : ∀ u : H, ‖A μ u - A μ' u‖ ≤ D := by
      intro u
      simpa [D] using hC₂.2.2.2 u μ μ' hμ hμ'
    refine ⟨x, x', ⟨dx, ddx, hx⟩, ⟨dx', ddx', hx'⟩, ?_⟩
    apply Filter.Eventually.of_forall
    intro t ht
    have hstable := damped_solution_stability
      (A μ) (A μ') γ (u₀ μ) (v₀ μ) (u₀ μ') (v₀ μ')
      (α μ) (α μ') D (hC₁ μ hμ).1 (hC₁ μ' hμ').1
      (hC₁ μ hμ).2 (hC₁ μ' hμ').2 hD0 hD hx hx' t ht
    dsimp only at hstable
    convert hstable using 1
    dsimp [D]
    ring

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
