import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_6
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_lem_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

theorem cocoercive_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {B : H → H} {a : ℝ} (ha : 0 < a)
    (hco : ∀ u v : H,
      a * ‖B u - B v‖ ^ 2 ≤ inner ℝ (B u - B v) (u - v)) :
    ∀ u v : H, ‖B u - B v‖ ≤ a⁻¹ * ‖u - v‖ := by
  intro u v
  have hco' := hco u v
  have hinter : inner ℝ (B u - B v) (u - v) ≤ ‖B u - B v‖ * ‖u - v‖ := by
    exact le_trans (le_abs_self _)
      (by simpa using norm_inner_le_norm (𝕜 := ℝ) (B u - B v) (u - v))
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

theorem first_order_sq_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {A : H → H} {alpha gamma : ℝ} (halpha : 0 < alpha)
    (hco : ∀ u v : H,
      alpha * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v))
    (u u' v v' : H) :
    ‖v - v'‖ ^ 2 + ‖-gamma • v - A u - (-gamma • v' - A u')‖ ^ 2 ≤
      (1 + 2 * gamma ^ 2 + 2 / alpha ^ 2) * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) := by
  have hL := cocoercive_lipschitz halpha hco u u'
  have hacc : ‖-gamma • v - A u - (-gamma • v' - A u')‖ ≤
      |gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖ := by
    rw [show -gamma • v - A u - (-gamma • v' - A u') =
        -(gamma • (v - v') + (A u - A u')) by module, norm_neg]
    calc
      ‖gamma • (v - v') + (A u - A u')‖ ≤
          ‖gamma • (v - v')‖ + ‖A u - A u'‖ := norm_add_le _ _
      _ ≤ |gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖ := by
        rw [norm_smul]
        exact add_le_add (by rfl) hL
  have hp : 0 ≤ |gamma| * ‖v - v'‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hq : 0 ≤ alpha⁻¹ * ‖u - u'‖ :=
    mul_nonneg (inv_nonneg.mpr halpha.le) (norm_nonneg _)
  have hsq : ‖-gamma • v - A u - (-gamma • v' - A u')‖ ^ 2 ≤
      (|gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hacc
  have hcross := sq_nonneg (|gamma| * ‖v - v'‖ - alpha⁻¹ * ‖u - u'‖)
  have habs : |gamma| ^ 2 = gamma ^ 2 := sq_abs gamma
  have hinv : alpha⁻¹ ^ 2 = 1 / alpha ^ 2 := by field_simp [halpha.ne']
  have hsumSq : (|gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖) ^ 2 ≤
      2 * gamma ^ 2 * ‖v - v'‖ ^ 2 + 2 * (1 / alpha ^ 2) * ‖u - u'‖ ^ 2 := by
    calc
      (|gamma| * ‖v - v'‖ + alpha⁻¹ * ‖u - u'‖) ^ 2 ≤
          2 * (|gamma| * ‖v - v'‖) ^ 2 + 2 * (alpha⁻¹ * ‖u - u'‖) ^ 2 := by
            nlinarith
      _ = 2 * gamma ^ 2 * ‖v - v'‖ ^ 2 + 2 * (1 / alpha ^ 2) * ‖u - u'‖ ^ 2 := by
            rw [mul_pow, mul_pow, habs, hinv]
            ring
  calc
    ‖v - v'‖ ^ 2 + ‖-gamma • v - A u - (-gamma • v' - A u')‖ ^ 2 ≤
        ‖v - v'‖ ^ 2 +
          (2 * gamma ^ 2 * ‖v - v'‖ ^ 2 +
            2 * (1 / alpha ^ 2) * ‖u - u'‖ ^ 2) := by
          gcongr
          exact hsq.trans hsumSq
    _ ≤ (1 + 2 * gamma ^ 2 + 2 / alpha ^ 2) *
          (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) := by
          have hg : 0 ≤ gamma ^ 2 := sq_nonneg _
          have ha : 0 ≤ 1 / alpha ^ 2 := by positivity
          have hu : 0 ≤ ‖u - u'‖ ^ 2 := sq_nonneg _
          have hv : 0 ≤ ‖v - v'‖ ^ 2 := sq_nonneg _
          ring_nf
          nlinarith [mul_nonneg hg hu, mul_nonneg hg hv,
            mul_nonneg ha hu, mul_nonneg ha hv]

theorem two_pairing_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a b c d : H) :
    inner ℝ a c + inner ℝ b d ≤
      Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) * Real.sqrt (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have hac : inner ℝ a c ≤ ‖a‖ * ‖c‖ := by
    exact le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) a c)
  have hbd : inner ℝ b d ≤ ‖b‖ * ‖d‖ := by
    exact le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) b d)
  have hprod := sq_nonneg (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖)
  have hleft : 0 ≤ ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ := by positivity
  have hright : 0 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by positivity
  have hsquare : (‖a‖ * ‖c‖ + ‖b‖ * ‖d‖) ^ 2 ≤
      (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
    nlinarith
  have hsqrt : ‖a‖ * ‖c‖ + ‖b‖ * ‖d‖ ≤
      Real.sqrt ((‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le hsquare
  rw [Real.sqrt_mul (by positivity)] at hsqrt
  exact (add_le_add hac hbd).trans hsqrt

theorem exp_kernel_integral (m D t : ℝ) (hm : 0 < m) :
    (∫ s in 0..t, Real.exp (m * (t - s)) * D) =
      m⁻¹ * (Real.exp (m * t) - 1) * D := by
  let F : ℝ → ℝ := fun s => m⁻¹ * D * Real.exp (m * (t - s))
  have hderiv : ∀ s : ℝ, HasDerivAt F (-(Real.exp (m * (t - s)) * D)) s := by
    intro s
    dsimp [F]
    convert (((Real.hasDerivAt_exp (m * (t - s))).comp s
      (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul m)).const_mul
        (m⁻¹ * D)) using 1
    all_goals field_simp [hm.ne']
    all_goals ring
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (m * (t - s)) * D)
      MeasureTheory.volume 0 t := by
    exact ((Real.continuous_exp.comp
      ((continuous_const.sub continuous_id).const_mul m)).mul continuous_const).intervalIntegrable 0 t
  have hcalc : ∫ s in 0..t, -(Real.exp (m * (t - s)) * D) = F t - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (by simpa using hint.neg)
  rw [← neg_inj, ← intervalIntegral.integral_neg, hcalc]
  dsimp [F]
  rw [show m * (t - t) = 0 by ring, Real.exp_zero]
  field_simp [hm.ne']
  ring

private theorem def_6_le_of_norm_le {H : Type*} [NormedAddCommGroup H] {r : ℝ}
    (hr : 0 < r) (A B : H → H)
    (hbounded : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A u - B u‖})
    {u : H} (hu : ‖u‖ ≤ r) :
    ‖A u - B u‖ ≤ def_6 r hr A B := by
  unfold def_6
  exact le_csSup hbounded ⟨u, hu, rfl⟩

private theorem def_6_bddAbove_of_cocoercive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r a b : ℝ} (_hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (A B : H → H)
    (hA : ∀ u v : H, a * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v))
    (hB : ∀ u v : H, b * ‖B u - B v‖ ^ 2 ≤ inner ℝ (B u - B v) (u - v)) :
    BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A u - B u‖} := by
  let LA : ∀ u v : H, ‖A u - A v‖ ≤ a⁻¹ * ‖u - v‖ :=
    cocoercive_lipschitz ha hA
  let LB : ∀ u v : H, ‖B u - B v‖ ≤ b⁻¹ * ‖u - v‖ :=
    cocoercive_lipschitz hb hB
  refine ⟨a⁻¹ * r + ‖A 0 - B 0‖ + b⁻¹ * r, ?_⟩
  rintro q ⟨u, hu, rfl⟩
  calc
    ‖A u - B u‖ = ‖(A u - A 0) + (A 0 - B 0) + (B 0 - B u)‖ := by
      congr 1
      abel
    _ ≤ ‖A u - A 0‖ + ‖A 0 - B 0‖ + ‖B 0 - B u‖ := by
      exact norm_add_le _ _ |>.trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ a⁻¹ * r + ‖A 0 - B 0‖ + b⁻¹ * r := by
      have hAu : ‖A u - A 0‖ ≤ a⁻¹ * r := by
        simpa using (LA u 0).trans (mul_le_mul_of_nonneg_left (by simpa using hu)
          (inv_nonneg.mpr ha.le))
      have hBu : ‖B 0 - B u‖ ≤ b⁻¹ * r := by
        simpa using (LB 0 u).trans (mul_le_mul_of_nonneg_left (by simpa using hu)
          (inv_nonneg.mpr hb.le))
      linarith

private theorem solution_data {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : H → H} {γ T : ℝ} {u₀ v₀ : H} {x dx ddx : ℝ → H} (hT : 0 < T)
    (hsol : ext_def_2 A γ u₀ v₀ x dx ddx) :
    0 < γ ∧ AbsolutelyContinuousOnInterval x 0 T ∧
      AbsolutelyContinuousOnInterval dx 0 T ∧ x 0 = u₀ ∧ dx 0 = v₀ ∧
      (∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → ddx t + γ • dx t + A (x t) = 0) ∧
      (∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt x (dx t) t) ∧
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt dx (ddx t) t := by
  rcases hsol with ⟨hγ, hdef⟩
  rcases hdef with ⟨hlac, hx0, hdx0, hxderiv, hdxderiv, hode⟩
  rcases hlac T hT with ⟨hxac, hdxac⟩
  exact ⟨hγ, hxac, hdxac, hx0, hdx0,
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hode,
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderiv,
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderiv⟩

theorem ac_norm_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : ℝ → H} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖ ^ 2) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hC0 : 0 ≤ C := by
    exact (norm_nonneg _).trans (hC a (by simp))
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ_bound⟩ :=
    (absolutelyContinuousOnInterval_iff _ _ _).mp hf
      (ε / (2 * C + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro E hE_disj hE_length
  have hsum := hδ_bound E hE_disj hE_length
  calc
    ∑ i ∈ Finset.range E.1,
        dist (‖f (E.2 i).1‖ ^ 2) (‖f (E.2 i).2‖ ^ 2)
        ≤ ∑ i ∈ Finset.range E.1,
            (2 * C) * dist (f (E.2 i).1) (f (E.2 i).2) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_mem := hE_disj.left i hi
          have hp := hC (E.2 i).1 hi_mem.left
          have hq := hC (E.2 i).2 hi_mem.right
          have hfac : ‖f (E.2 i).1‖ + ‖f (E.2 i).2‖ ≤ 2 * C := by
            linarith
          have hdiff : |‖f (E.2 i).1‖ - ‖f (E.2 i).2‖| ≤
              ‖f (E.2 i).1 - f (E.2 i).2‖ := by
            exact abs_norm_sub_norm_le _ _
          simp only [dist_eq_norm, Real.norm_eq_abs]
          calc
            |‖f (E.2 i).1‖ ^ 2 - ‖f (E.2 i).2‖ ^ 2| =
                (‖f (E.2 i).1‖ + ‖f (E.2 i).2‖) *
                  |‖f (E.2 i).1‖ - ‖f (E.2 i).2‖| := by
              rw [show ‖f (E.2 i).1‖ ^ 2 - ‖f (E.2 i).2‖ ^ 2 =
                (‖f (E.2 i).1‖ + ‖f (E.2 i).2‖) *
                  (‖f (E.2 i).1‖ - ‖f (E.2 i).2‖) by ring]
              rw [abs_mul]
              rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
            _ ≤ (2 * C) * ‖f (E.2 i).1 - f (E.2 i).2‖ := by
              exact mul_le_mul hfac hdiff (abs_nonneg _) (by positivity)
    _ = (2 * C) * ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2) := by rw [Finset.mul_sum]
    _ < (2 * C + 1) * (ε / (2 * C + 1)) := by
      gcongr
      nlinarith
    _ = ε := by field_simp [show 2 * C + 1 ≠ 0 by linarith]

/-- Theorem 5.1: For each μ, let x_μ be the unique solution of S(A_μ,u₀^μ,v₀^μ).
  Suppose (C₁) and, for given r,T>0, x_μ(t)∈B(0,r) for a.e. t∈[0,T] and every μ.
  Then the D_r estimate holds with m=max(m_μ,m_μ′).

  Deviation: the paper states that `x_μ` *is* the unique solution; here the
  solutions are given by the hypothesis `hsol` (so existence and uniqueness are
  not re-proved) and only the estimate is concluded.  `D_r` is the real
  `sSup` of `def_6`, whose finiteness is obtained inside the proof from (C₁)
  rather than assumed. -/
theorem thm_2 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (r T : ℝ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hr : 0 < r) (hT : 0 < T)
    (hball : ∀ μ, μ ∈ V → ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ r) :
    ∀ μ, μ ∈ V → ∀ μ', μ' ∈ V →
      let m_μ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))
      let m := max m_μ m_μ'
      ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤ Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          m⁻¹ * (Real.exp (m * T) - 1) * def_6 r hr (A μ) (A μ') := by
  intro μ hμ μ' hμ'
  dsimp
  obtain ⟨hαμ, hcoμ⟩ := hC₁ μ hμ
  obtain ⟨hαμ', hcoμ'⟩ := hC₁ μ' hμ'
  obtain ⟨hγμ, hxACμ, hdxACμ, hx0μ, hdx0μ, hodeμ, hxderivμ, hdxderivμ⟩ :=
    solution_data hT (hsol μ hμ)
  obtain ⟨hγμ', hxACμ', hdxACμ', hx0μ', hdx0μ', hodeμ', hxderivμ', hdxderivμ'⟩ :=
    solution_data hT (hsol μ' hμ')
  have hD_bdd : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A μ u - A μ' u‖} :=
    def_6_bddAbove_of_cocoercive hr.le hαμ hαμ' (A μ) (A μ') hcoμ hcoμ'
  have hD_bound : ∀ ⦃u : H⦄, ‖u‖ ≤ r →
      ‖A μ u - A μ' u‖ ≤ def_6 r hr (A μ) (A μ') := by
    intro u hu
    exact def_6_le_of_norm_le hr (A μ) (A μ') hD_bdd hu
  have hD_nonneg : 0 ≤ def_6 r hr (A μ) (A μ') := by
    have hzero : ‖A μ (0 : H) - A μ' 0‖ ≤ def_6 r hr (A μ) (A μ') :=
      hD_bound (by simpa using hr.le)
    exact (norm_nonneg _).trans hzero
  let y : ℝ → H := fun t => x μ t - x μ' t
  let z : ℝ → H := fun t => dx μ t - dx μ' t
  let w : ℝ → ℝ := fun t => ‖y t‖ ^ 2 + ‖z t‖ ^ 2
  have hyAC : AbsolutelyContinuousOnInterval y 0 T := by
    simpa [y] using hxACμ.fun_sub hxACμ'
  have hzAC : AbsolutelyContinuousOnInterval z 0 T := by
    simpa [z] using hdxACμ.fun_sub hdxACμ'
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := by
    simpa [w] using (ac_norm_sq hyAC).fun_add (ac_norm_sq hzAC)
  have hw_nonneg : ∀ t, 0 ≤ w t := by
    intro t
    dsimp [w]
    positivity
  have hw0 : w 0 = ‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2 := by
    simp only [w, y, z, hx0μ, hx0μ', hdx0μ, hdx0μ']
  have hwDeriv : ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      HasDerivAt w
        (2 * inner ℝ (y t) (z t) +
          2 * inner ℝ (z t) (ddx μ t - ddx μ' t)) t := by
    filter_upwards [hxderivμ, hxderivμ', hdxderivμ, hdxderivμ'] with t hxμ hxμ' hdxμ hdxμ'
    intro ht
    have hyD : HasDerivAt y (z t) t := by
      simpa [y, z] using (hxμ ht).sub (hxμ' ht)
    have hzD : HasDerivAt z (ddx μ t - ddx μ' t) t := by
      simpa [z] using (hdxμ ht).sub (hdxμ' ht)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  let D := def_6 r hr (A μ) (A μ')
  let m := max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ) ^ 2))
    (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2))
  have hD0 : 0 ≤ D := by simpa [D] using hD_nonneg
  have hmone : 1 ≤ m := by
    apply le_trans ?_ (le_max_right _ _)
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hsq : 0 ≤ γ ^ 2 := sq_nonneg _
    have hinv : 0 ≤ 2 / (α μ') ^ 2 := by positivity
    linarith
  have hm0 : 0 ≤ m := by linarith
  have hm : 0 < m := by linarith
  have hfixed_pair (t : ℝ) :
      inner ℝ (y t) (z t) + inner ℝ (z t)
          (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))) ≤ m * w t := by
    have hbase := first_order_sq_bound (gamma := γ) hαμ' hcoμ'
      (x μ t) (x μ' t) (dx μ t) (dx μ' t)
    have hbase' : ‖z t‖ ^ 2 + ‖-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
        (1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2) * w t := by
      rw [show -γ • dx μ t - A μ' (x μ t) -
          (-γ • dx μ' t - A μ' (x μ' t)) =
          -γ • (dx μ t - dx μ' t) - (A μ' (x μ t) - A μ' (x μ' t)) by module] at hbase
      simpa [z, w] using hbase
    have hcoef : 1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2 ≤ m ^ 2 := by
      have hnon : 0 ≤ 1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2 := by positivity
      have hsqrtle : Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2) ≤ m :=
        le_max_right _ _
      rw [← Real.sq_sqrt hnon]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hm0).mpr hsqrtle
    have hsq : ‖z t‖ ^ 2 + ‖-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
        m ^ 2 * w t := by
      exact hbase'.trans (mul_le_mul_of_nonneg_right hcoef (hw_nonneg t))
    have hpair := two_pairing_le (y t) (z t) (z t)
      (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t)))
    have hwrt : Real.sqrt (w t) ^ 2 = w t := Real.sq_sqrt (hw_nonneg t)
    have hsqrt : Real.sqrt (‖z t‖ ^ 2 + ‖-γ • z t -
        (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2) ≤ m * Real.sqrt (w t) := by
      have := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs, abs_of_nonneg hm0] at this
      exact this
    calc
      inner ℝ (y t) (z t) + inner ℝ (z t) (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))) ≤
          Real.sqrt (‖y t‖ ^ 2 + ‖z t‖ ^ 2) *
            Real.sqrt (‖z t‖ ^ 2 + ‖-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2) := hpair
      _ ≤ Real.sqrt (w t) * (m * Real.sqrt (w t)) := by
        simpa [w] using mul_le_mul_of_nonneg_left hsqrt
          (Real.sqrt_nonneg (‖y t‖ ^ 2 + ‖z t‖ ^ 2))
      _ = m * w t := by nlinarith [hwrt]
  have hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w t <= m * w t + D * w t ^ (1 / 2 : ℝ) := by
    filter_upwards [hodeμ, hodeμ', hwDeriv, hball μ hμ] with t htodeμ htodeμ' htderiv htball
    intro htIcc
    have hddxμ : ddx μ t = -γ • dx μ t - A μ (x μ t) := by
      calc
        ddx μ t = -(γ • dx μ t + A μ (x μ t)) :=
          eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using htodeμ htIcc.1)
        _ = -γ • dx μ t - A μ (x μ t) := by module
    have hddxμ' : ddx μ' t = -γ • dx μ' t - A μ' (x μ' t) := by
      calc
        ddx μ' t = -(γ • dx μ' t + A μ' (x μ' t)) :=
          eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using htodeμ' htIcc.1)
        _ = -γ • dx μ' t - A μ' (x μ' t) := by module
    have hddx : ddx μ t - ddx μ' t =
        (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))) -
          (A μ (x μ t) - A μ' (x μ t)) := by
      rw [hddxμ, hddxμ']
      dsimp [z]
      module
    have hforce : ‖A μ (x μ t) - A μ' (x μ t)‖ <= D := by
      simpa [D] using hD_bound (htball htIcc)
    have hz_le : ‖z t‖ <= Real.sqrt (w t) := by
      apply Real.le_sqrt_of_sq_le
      dsimp [w]
      nlinarith [sq_nonneg ‖y t‖]
    have hforce_pair :
        -inner ℝ (z t) (A μ (x μ t) - A μ' (x μ t)) <= D * Real.sqrt (w t) := by
      calc
        -inner ℝ (z t) (A μ (x μ t) - A μ' (x μ t)) <=
            ‖z t‖ * ‖A μ (x μ t) - A μ' (x μ t)‖ := by
              exact le_trans (le_abs_self _) (by
                simpa using norm_inner_le_norm (𝕜 := ℝ) (z t)
                  (A μ (x μ t) - A μ' (x μ t)))
        _ <= D * Real.sqrt (w t) := by
              calc
                ‖z t‖ * ‖A μ (x μ t) - A μ' (x μ t)‖ <= ‖z t‖ * D :=
                  mul_le_mul_of_nonneg_left hforce (norm_nonneg _)
                _ <= Real.sqrt (w t) * D :=
                  mul_le_mul_of_nonneg_right hz_le hD0
                _ = D * Real.sqrt (w t) := by ring
    have henergy :
        inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t) =
        (inner ℝ (y t) (z t) + inner ℝ (z t)
          (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t)))) -
          inner ℝ (z t) (A μ (x μ t) - A μ' (x μ t)) := by
      rw [hddx]
      simp only [inner_sub_right]
      ring
    have hderiv_eq : deriv w t =
        2 * (inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t)) := by
      rw [(htderiv htIcc.1).deriv]
      ring
    rw [hderiv_eq, henergy]
    rw [← Real.sqrt_eq_rpow]
    nlinarith [hfixed_pair t, hforce_pair]
  have hgronwall := ext_lem_1 (w := w) (a := fun _ : ℝ => m)
    (b := fun _ : ℝ => D) (t₀ := 0) (T := T) (α := (1 / 2 : ℝ))
    hT (by norm_num) (by norm_num) (by simpa using hwAC)
    (by intro t ht; exact hw_nonneg t)
    (by simp)
    (by simp)
    (Filter.Eventually.of_forall (fun t _ => hD0)) (by simpa using hineq)
  have hconst_int (a b : ℝ) : (∫ s in a..b, m) = (b - a) * m := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  filter_upwards with t htIcc
  have ht0 : 0 <= t := htIcc.1
  have htT : t <= T := htIcc.2
  have hgr := hgronwall t ht0 (by simpa using htT)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hkernel0 : (∫ s in 0..t, Real.exp ((t - s) * m)) =
      m⁻¹ * (Real.exp (m * t) - 1) := by
    calc
      (∫ s in 0..t, Real.exp ((t - s) * m)) =
          ∫ s in 0..t, Real.exp (m * (t - s)) * 1 := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with s hs
            ring
      _ = m⁻¹ * (Real.exp (m * t) - 1) * 1 := exp_kernel_integral m 1 t hm
      _ = m⁻¹ * (Real.exp (m * t) - 1) := by ring
  have hgr' : Real.sqrt (w t) <=
      Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) +
        m⁻¹ * (Real.exp (m * t) - 1) * D := by
    rw [hkernel0] at hgr
    convert hgr using 1
    all_goals ring
  have hmt : m * t <= m * T := mul_le_mul_of_nonneg_left htT hm0
  have hexp : Real.exp (m * t) <= Real.exp (m * T) := Real.exp_le_exp.mpr hmt
  have hkernel : m⁻¹ * (Real.exp (m * t) - 1) * D <=
      m⁻¹ * (Real.exp (m * T) - 1) * D := by
    have hsub := sub_le_sub_right hexp 1
    have hscale : 0 <= m⁻¹ * D := mul_nonneg (inv_nonneg.mpr hm0) hD0
    nlinarith [mul_le_mul_of_nonneg_left hsub hscale]
  have hy_le : ‖x μ t - x μ' t‖ <= Real.sqrt (w t) := by
    change ‖y t‖ <= Real.sqrt (w t)
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  have hinit0 : 0 <= Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) :=
    Real.sqrt_nonneg _
  calc
    ‖x μ t - x μ' t‖ <= Real.sqrt (w t) := hy_le
    _ <= Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) +
        m⁻¹ * (Real.exp (m * t) - 1) * D := hgr'
    _ <= Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * T) +
        m⁻¹ * (Real.exp (m * T) - 1) * D := by
      exact add_le_add (mul_le_mul_of_nonneg_left hexp hinit0) hkernel
    _ = Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        m⁻¹ * (Real.exp (m * T) - 1) * def_6 r hr (A μ) (A μ') := by
      dsimp [D]
      ring

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
