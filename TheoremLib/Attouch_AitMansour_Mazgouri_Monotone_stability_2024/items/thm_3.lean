import Foundation.SetValued.Resolvent
import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_7
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_lem_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2

open scoped Pointwise

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

private theorem thm_3_cocoercive_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {B : H → H} {a : ℝ} (ha : 0 < a)
    (hco : ∀ u v : H, a * ‖B u - B v‖ ^ 2 ≤ inner ℝ (B u - B v) (u - v)) :
    ∀ u v : H, ‖B u - B v‖ ≤ a⁻¹ * ‖u - v‖ := by
  intro u v
  have hco' := hco u v
  have hinter : inner ℝ (B u - B v) (u - v) ≤ ‖B u - B v‖ * ‖u - v‖ :=
    le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) (B u - B v) (u - v))
  by_cases hzero : ‖B u - B v‖ = 0
  · rw [hzero]
    positivity
  · have hnorm : 0 < ‖B u - B v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hfactor : a * ‖B u - B v‖ ≤ ‖u - v‖ := by
      apply le_of_mul_le_mul_right _ hnorm
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hco'.trans hinter
    apply le_of_mul_le_mul_left _ ha
    convert hfactor using 1
    all_goals field_simp

private theorem thm_3_first_order_sq_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {A : H → H} {alpha gamma : ℝ} (halpha : 0 < alpha)
    (hco : ∀ u v : H, alpha * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v))
    (u u' v v' : H) :
    ‖v - v'‖ ^ 2 + ‖-gamma • v - A u - (-gamma • v' - A u')‖ ^ 2 ≤
      (1 + 2 * gamma ^ 2 + 2 / alpha ^ 2) * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) := by
  have hL := thm_3_cocoercive_lipschitz halpha hco u u'
  have hacc : ‖-gamma • v - A u - (-gamma • v' - A u')‖ ≤ |gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖ := by
    rw [show -gamma • v - A u - (-gamma • v' - A u') = -(gamma • (v - v') + (A u - A u')) by module, norm_neg]
    calc
      ‖gamma • (v - v') + (A u - A u')‖ ≤ ‖gamma • (v - v')‖ + ‖A u - A u'‖ := norm_add_le _ _
      _ ≤ |gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖ := by rw [norm_smul]; exact add_le_add (by rfl) hL
  have hsq : ‖-gamma • v - A u - (-gamma • v' - A u')‖ ^ 2 ≤
      (|gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hacc
  have hcross := sq_nonneg (|gamma| * ‖v - v'‖ - alpha⁻¹ * ‖u - u'‖)
  have habs : |gamma| ^ 2 = gamma ^ 2 := sq_abs gamma
  have hinv : alpha⁻¹ ^ 2 = 1 / alpha ^ 2 := by field_simp [halpha.ne']
  have hsumSq : (|gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖) ^ 2 ≤
      2 * gamma ^ 2 * ‖v - v'‖ ^ 2 + 2 * (1 / alpha ^ 2) * ‖u - u'‖ ^ 2 := by
    calc
      _ ≤ 2 * (|gamma| * ‖v - v'‖) ^ 2 + 2 * (alpha⁻¹ * ‖u - u'‖) ^ 2 := by nlinarith
      _ = _ := by rw [mul_pow, mul_pow, habs, hinv]; ring
  calc
    ‖v - v'‖ ^ 2 + ‖-gamma • v - A u - (-gamma • v' - A u')‖ ^ 2 ≤
        ‖v - v'‖ ^ 2 + (2 * gamma ^ 2 * ‖v - v'‖ ^ 2 + 2 * (1 / alpha ^ 2) * ‖u - u'‖ ^ 2) := by gcongr; exact hsq.trans hsumSq
    _ ≤ (1 + 2 * gamma ^ 2 + 2 / alpha ^ 2) * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) := by
      have hg : 0 ≤ gamma ^ 2 := sq_nonneg _
      have ha : 0 ≤ 1 / alpha ^ 2 := by positivity
      have hu : 0 ≤ ‖u - u'‖ ^ 2 := sq_nonneg _
      have hv : 0 ≤ ‖v - v'‖ ^ 2 := sq_nonneg _
      ring_nf
      nlinarith [mul_nonneg hg hu, mul_nonneg hg hv, mul_nonneg ha hu, mul_nonneg ha hv]

private theorem thm_3_two_pairing_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a b c d : H) :
    inner ℝ a c + inner ℝ b d ≤ Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) * Real.sqrt (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have hac : inner ℝ a c ≤ ‖a‖ * ‖c‖ := le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) a c)
  have hbd : inner ℝ b d ≤ ‖b‖ * ‖d‖ := le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) b d)
  have hprod := sq_nonneg (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖)
  have hsquare : (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖) ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by nlinarith
  have hsqrt : ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ ≤ Real.sqrt ((‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2)) := Real.le_sqrt_of_sq_le hsquare
  rw [Real.sqrt_mul (by positivity)] at hsqrt
  exact (add_le_add hac hbd).trans hsqrt

private theorem thm_3_exp_kernel_integral (m D t : ℝ) (hm : 0 < m) :
    (∫ s in 0..t, Real.exp (m * (t - s)) * D) = m⁻¹ * (Real.exp (m * t) - 1) * D := by
  let F : ℝ → ℝ := fun s => m⁻¹ * D * Real.exp (m * (t - s))
  have hderiv : ∀ s : ℝ, HasDerivAt F (-(Real.exp (m * (t - s)) * D)) s := by
    intro s
    dsimp [F]
    convert (((Real.hasDerivAt_exp (m * (t - s))).comp s (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul m)).const_mul (m⁻¹ * D)) using 1
    all_goals field_simp [hm.ne']
    all_goals ring
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (m * (t - s)) * D) MeasureTheory.volume 0 t :=
    ((Real.continuous_exp.comp ((continuous_const.sub continuous_id).const_mul m)).mul continuous_const).intervalIntegrable 0 t
  have hcalc : ∫ s in 0..t, -(Real.exp (m * (t - s)) * D) = F t - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (by simpa using hint.neg)
  rw [← neg_inj, ← intervalIntegral.integral_neg, hcalc]
  dsimp [F]
  rw [show m * (t - t) = 0 by ring, Real.exp_zero]
  field_simp [hm.ne']
  ring

private theorem thm_3_solution_data {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : H → H} {γ T : ℝ} {u₀ v₀ : H} {x dx ddx : ℝ → H} (hT : 0 < T)
    (hsol : ext_def_2 A γ u₀ v₀ x dx ddx) :
    0 < γ ∧ AbsolutelyContinuousOnInterval x 0 T ∧ AbsolutelyContinuousOnInterval dx 0 T ∧ x 0 = u₀ ∧ dx 0 = v₀ ∧
      (∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → ddx t + γ • dx t + A (x t) = 0) ∧
      (∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt x (dx t) t) ∧ ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt dx (ddx t) t := by
  rcases hsol with ⟨hγ, hdef⟩
  rcases hdef with ⟨hlac, hx0, hdx0, hxderiv, hdxderiv, hode⟩
  rcases hlac T hT with ⟨hxac, hdxac⟩
  exact ⟨hγ, hxac, hdxac, hx0, hdx0,
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hode,
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderiv,
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderiv⟩

private theorem thm_3_ac_norm_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : ℝ → H} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖ ^ 2) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a (by simp))
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ_bound⟩ := (absolutelyContinuousOnInterval_iff _ _ _).mp hf
    (ε / (2 * C + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro E hE_disj hE_length
  have hsum := hδ_bound E hE_disj hE_length
  calc
    ∑ i ∈ Finset.range E.1, dist (‖f (E.2 i).1‖ ^ 2) (‖f (E.2 i).2‖ ^ 2) ≤
        ∑ i ∈ Finset.range E.1, (2 * C) * dist (f (E.2 i).1) (f (E.2 i).2) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_mem := hE_disj.left i hi
      have hp := hC (E.2 i).1 hi_mem.left
      have hq := hC (E.2 i).2 hi_mem.right
      have hfac : ‖f (E.2 i).1‖ + ‖f (E.2 i).2‖ ≤ 2 * C := by linarith
      have hdiff : |‖f (E.2 i).1‖ - ‖f (E.2 i).2‖| ≤ ‖f (E.2 i).1 - f (E.2 i).2‖ := abs_norm_sub_norm_le _ _
      simp only [dist_eq_norm, Real.norm_eq_abs]
      calc
        |‖f (E.2 i).1‖ ^ 2 - ‖f (E.2 i).2‖ ^ 2| =
            (‖f (E.2 i).1‖ + ‖f (E.2 i).2‖) * |‖f (E.2 i).1‖ - ‖f (E.2 i).2‖| := by
          rw [show ‖f (E.2 i).1‖ ^ 2 - ‖f (E.2 i).2‖ ^ 2 =
            (‖f (E.2 i).1‖ + ‖f (E.2 i).2‖) * (‖f (E.2 i).1‖ - ‖f (E.2 i).2‖) by ring]
          rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        _ ≤ (2 * C) * ‖f (E.2 i).1 - f (E.2 i).2‖ := mul_le_mul hfac hdiff (abs_nonneg _) (by positivity)
    _ = (2 * C) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by rw [Finset.mul_sum]
    _ < (2 * C + 1) * (ε / (2 * C + 1)) := by gcongr; nlinarith
    _ = ε := by field_simp [show 2 * C + 1 ≠ 0 by linarith]

/-- Theorem 5.2: For given λ>0, let x_μ be the unique solution of (14).
  If for some ρ,T>0, x_μ(t)∈B(0,ρ) for a.e. t∈[0,T], then the d_{λ,ρ}
  estimate holds with m=(1+2γ²+2/λ²)^{1/2} and A_μ:=A(⋅,μ).

  Deviations: maximal monotonicity of the `A_μ` (Section 4.3 context in the
  paper, needed for the Yosida regularization of (14)) is an explicit
  hypothesis, and the existence/uniqueness of the solution of (14) is supplied
  by `hsol` rather than re-proved. -/
theorem thm_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → SetValuedOperator H H)
    (hA : ∀ μ, μ ∈ V → (A μ).IsMaximalMonotone)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (γ lam ρ T : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) (hT : 0 < T)
    (hsol : ∀ μ (hμ : μ ∈ V), ext_def_2 (fun u : H => lam⁻¹ •
      (u - SetValuedOperator.resolventMap (A μ) (hA μ hμ) lam hlam u)) γ
      (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hball : ∀ μ, μ ∈ V → ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ ρ) :
    ∀ μ (hμ : μ ∈ V), ∀ μ' (hμ' : μ' ∈ V),
      let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 / (lam ^ 2))
      let d_lambda_rho := def_7 (A μ) (A μ') (hA μ hμ) (hA μ' hμ')
        lam ρ hlam hρ
      ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤ Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (lam * m)⁻¹ * (Real.exp (m * T) - 1) * d_lambda_rho := by
  intro μ hμ μ' hμ'
  dsimp
  let Y : H → H := fun u => lam⁻¹ • (u - SetValuedOperator.resolventMap (A μ) (hA μ hμ) lam hlam u)
  let Y' : H → H := fun u => lam⁻¹ • (u - SetValuedOperator.resolventMap (A μ') (hA μ' hμ') lam hlam u)
  have hco : ∀ u v : H, lam * ‖Y u - Y v‖ ^ 2 ≤ inner ℝ (Y u - Y v) (u - v) := by
    intro u v
    simpa [Y, real_inner_comm] using (SetValuedOperator.yosida_is_cocoercive (A μ) (hA μ hμ) lam hlam).1.ineq
      ⟨u, Set.mem_univ _⟩ ⟨v, Set.mem_univ _⟩
  have hco' : ∀ u v : H, lam * ‖Y' u - Y' v‖ ^ 2 ≤ inner ℝ (Y' u - Y' v) (u - v) := by
    intro u v
    simpa [Y', real_inner_comm] using (SetValuedOperator.yosida_is_cocoercive (A μ') (hA μ' hμ') lam hlam).1.ineq
      ⟨u, Set.mem_univ _⟩ ⟨v, Set.mem_univ _⟩
  obtain ⟨_, hxACμ, hdxACμ, hx0μ, hdx0μ, hodeμ, hxderivμ, hdxderivμ⟩ :=
    thm_3_solution_data hT (hsol μ hμ)
  obtain ⟨_, hxACμ', hdxACμ', hx0μ', hdx0μ', hodeμ', hxderivμ', hdxderivμ'⟩ :=
    thm_3_solution_data hT (hsol μ' hμ')
  have hD_bdd : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧ q = ‖Y u - Y' u‖} := by
    let LY := thm_3_cocoercive_lipschitz hlam hco
    let LY' := thm_3_cocoercive_lipschitz hlam hco'
    refine ⟨lam⁻¹ * ρ + ‖Y 0 - Y' 0‖ + lam⁻¹ * ρ, ?_⟩
    rintro q ⟨u, hu, rfl⟩
    calc
      ‖Y u - Y' u‖ = ‖(Y u - Y 0) + (Y 0 - Y' 0) + (Y' 0 - Y' u)‖ := by congr 1; abel
      _ ≤ ‖Y u - Y 0‖ + ‖Y 0 - Y' 0‖ + ‖Y' 0 - Y' u‖ := norm_add_le _ _ |>.trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ lam⁻¹ * ρ + ‖Y 0 - Y' 0‖ + lam⁻¹ * ρ := by
        have hYu : ‖Y u - Y 0‖ ≤ lam⁻¹ * ρ := by
          simpa using (LY u 0).trans (mul_le_mul_of_nonneg_left (by simpa using hu) (inv_nonneg.mpr hlam.le))
        have hYu' : ‖Y' 0 - Y' u‖ ≤ lam⁻¹ * ρ := by
          simpa using (LY' 0 u).trans (mul_le_mul_of_nonneg_left (by simpa using hu) (inv_nonneg.mpr hlam.le))
        linarith
  let D : ℝ := lam⁻¹ * def_7 (A μ) (A μ') (hA μ hμ) (hA μ' hμ') lam ρ hlam hρ
  have hD_bound : ∀ ⦃u : H⦄, ‖u‖ ≤ ρ → ‖Y u - Y' u‖ ≤ D := by
    intro u hu
    have hs := le_csSup hD_bdd ⟨u, hu, rfl⟩
    have hne : lam ≠ 0 := ne_of_gt hlam
    change ‖Y u - Y' u‖ ≤ lam⁻¹ * (lam * sSup {q : ℝ | ∃ v : H, ‖v‖ ≤ ρ ∧ q = ‖Y v - Y' v‖})
    calc
      _ ≤ sSup {q : ℝ | ∃ v : H, ‖v‖ ≤ ρ ∧ q = ‖Y v - Y' v‖} := hs
      _ = _ := by field_simp [hne]
  have hD0 : 0 ≤ D := by
    have := hD_bound (u := (0 : H)) (by simpa using hρ.le)
    exact (norm_nonneg _).trans this
  let y : ℝ → H := fun t => x μ t - x μ' t
  let z : ℝ → H := fun t => dx μ t - dx μ' t
  let w : ℝ → ℝ := fun t => ‖y t‖ ^ 2 + ‖z t‖ ^ 2
  have hyAC : AbsolutelyContinuousOnInterval y 0 T := by simpa [y] using hxACμ.fun_sub hxACμ'
  have hzAC : AbsolutelyContinuousOnInterval z 0 T := by simpa [z] using hdxACμ.fun_sub hdxACμ'
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := by simpa [w] using (thm_3_ac_norm_sq hyAC).fun_add (thm_3_ac_norm_sq hzAC)
  have hw_nonneg : ∀ t, 0 ≤ w t := by intro t; dsimp [w]; positivity
  have hw0 : w 0 = ‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2 := by simp [w, y, z, hx0μ, hx0μ', hdx0μ, hdx0μ']
  have hwDeriv : ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt w (2 * inner ℝ (y t) (z t) + 2 * inner ℝ (z t) (ddx μ t - ddx μ' t)) t := by
    filter_upwards [hxderivμ, hxderivμ', hdxderivμ, hdxderivμ'] with t hx hx' hdx hdx'
    intro ht
    have hyD : HasDerivAt y (z t) t := by simpa [y, z] using (hx ht).sub (hx' ht)
    have hzD : HasDerivAt z (ddx μ t - ddx μ' t) t := by simpa [z] using (hdx ht).sub (hdx' ht)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 / lam ^ 2)
  have hmone : 1 ≤ m := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 2 / lam ^ 2 := by positivity
    nlinarith [sq_nonneg γ]
  have hm0 : 0 ≤ m := by linarith
  have hm : 0 < m := by linarith
  have hfixed (t : ℝ) : inner ℝ (y t) (z t) + inner ℝ (z t) (-γ • z t - (Y' (x μ t) - Y' (x μ' t))) ≤ m * w t := by
    have hb := thm_3_first_order_sq_bound (gamma := γ) hlam hco' (x μ t) (x μ' t) (dx μ t) (dx μ' t)
    have hb' : ‖z t‖ ^ 2 + ‖-γ • z t - (Y' (x μ t) - Y' (x μ' t))‖ ^ 2 ≤ m ^ 2 * w t := by
      rw [show -γ • dx μ t - Y' (x μ t) - (-γ • dx μ' t - Y' (x μ' t)) = -γ • (dx μ t - dx μ' t) - (Y' (x μ t) - Y' (x μ' t)) by module] at hb
      have hsq : m ^ 2 = 1 + 2 * γ ^ 2 + 2 / lam ^ 2 := Real.sq_sqrt (by positivity)
      simpa [z, w, hsq] using hb
    have hp := thm_3_two_pairing_le (y t) (z t) (z t) (-γ • z t - (Y' (x μ t) - Y' (x μ' t)))
    have hs := Real.sqrt_le_sqrt hb'
    rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs, abs_of_nonneg hm0] at hs
    have hwr : Real.sqrt (w t) ^ 2 = w t := Real.sq_sqrt (hw_nonneg t)
    calc
      _ ≤ Real.sqrt (‖y t‖ ^ 2 + ‖z t‖ ^ 2) * Real.sqrt (‖z t‖ ^ 2 + ‖-γ • z t - (Y' (x μ t) - Y' (x μ' t))‖ ^ 2) := hp
      _ ≤ Real.sqrt (w t) * (m * Real.sqrt (w t)) := by simpa [w] using mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = m * w t := by nlinarith [hwr]
  have hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w t ≤ m * w t + D * w t ^ (1 / 2 : ℝ) := by
    filter_upwards [hodeμ, hodeμ', hwDeriv, hball μ hμ] with t ho ho' hd hb
    intro ht
    have hddx : ddx μ t - ddx μ' t = (-γ • z t - (Y' (x μ t) - Y' (x μ' t))) - (Y (x μ t) - Y' (x μ t)) := by
      have h1 : ddx μ t = -γ • dx μ t - Y (x μ t) := by
        calc ddx μ t = -(γ • dx μ t + Y (x μ t)) := eq_neg_of_add_eq_zero_left (by simpa [add_assoc, Y] using ho ht.1)
             _ = _ := by module
      have h2 : ddx μ' t = -γ • dx μ' t - Y' (x μ' t) := by
        calc ddx μ' t = -(γ • dx μ' t + Y' (x μ' t)) := eq_neg_of_add_eq_zero_left (by simpa [add_assoc, Y'] using ho' ht.1)
             _ = _ := by module
      rw [h1, h2]
      dsimp [z]
      module
    have hf : ‖Y (x μ t) - Y' (x μ t)‖ ≤ D := hD_bound (hb ht)
    have hz : ‖z t‖ ≤ Real.sqrt (w t) := by
      apply Real.le_sqrt_of_sq_le
      dsimp [w]
      nlinarith [sq_nonneg ‖y t‖]
    have hforce : -inner ℝ (z t) (Y (x μ t) - Y' (x μ t)) ≤ D * Real.sqrt (w t) := by
      calc
        _ ≤ ‖z t‖ * ‖Y (x μ t) - Y' (x μ t)‖ := le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) (z t) (Y (x μ t) - Y' (x μ t)))
        _ ≤ D * Real.sqrt (w t) := by
          calc
            _ ≤ ‖z t‖ * D := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
            _ ≤ Real.sqrt (w t) * D := mul_le_mul_of_nonneg_right hz hD0
            _ = _ := by ring
    have he : inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t) =
        (inner ℝ (y t) (z t) + inner ℝ (z t) (-γ • z t - (Y' (x μ t) - Y' (x μ' t)))) - inner ℝ (z t) (Y (x μ t) - Y' (x μ t)) := by
      rw [hddx]
      simp only [inner_sub_right]
      ring
    have hd' : deriv w t = 2 * (inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t)) := by rw [(hd ht.1).deriv]; ring
    rw [hd', he, ← Real.sqrt_eq_rpow]
    nlinarith [hfixed t, hforce]
  have hg := ext_lem_1 (w := w) (a := fun _ : ℝ => m) (b := fun _ : ℝ => D)
    (t₀ := 0) (T := T) (α := (1 / 2 : ℝ)) hT (by norm_num) (by norm_num)
    (by simpa using hwAC) (by intro t _; exact hw_nonneg t) (by simp) (by simp)
    (Filter.Eventually.of_forall (fun _ _ => hD0)) (by simpa using hineq)
  filter_upwards with t ht
  have ht0 := ht.1
  have htT := ht.2
  have hgr := hg t ht0 (by simpa using htT)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hk : (∫ s in 0..t, Real.exp ((t - s) * m)) = m⁻¹ * (Real.exp (m * t) - 1) := by
    calc
      _ = ∫ s in 0..t, Real.exp (m * (t - s)) * 1 := by apply intervalIntegral.integral_congr_ae; filter_upwards with s hs; ring
      _ = _ := by simpa using thm_3_exp_kernel_integral m 1 t hm
  rw [hk] at hgr
  have hgr' : Real.sqrt (w t) ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) + m⁻¹ * (Real.exp (m * t) - 1) * D := by
    convert hgr using 1
    all_goals ring
  have hexp : Real.exp (m * t) ≤ Real.exp (m * T) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hm0)
  have hker : m⁻¹ * (Real.exp (m * t) - 1) * D ≤ m⁻¹ * (Real.exp (m * T) - 1) * D := by
    have hs := sub_le_sub_right hexp 1
    have hp : 0 ≤ m⁻¹ * D := mul_nonneg (inv_nonneg.mpr hm0) hD0
    nlinarith [mul_le_mul_of_nonneg_left hs hp]
  have hy : ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := by
    change ‖y t‖ ≤ _
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  calc
    ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := hy
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) + m⁻¹ * (Real.exp (m * t) - 1) * D := hgr'
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * T) + m⁻¹ * (Real.exp (m * T) - 1) * D :=
      add_le_add (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)) hker
    _ = Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) + (lam * m)⁻¹ * (Real.exp (m * T) - 1) * def_7 (A μ) (A μ') (hA μ hμ) (hA μ' hμ') lam ρ hlam hρ := by
      dsimp [D]
      field_simp [ne_of_gt hlam, ne_of_gt hm]

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
