import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_8
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set

/-- Theorem 5.4, with the local cross-operator estimate used in the paper made
explicit.  The coefficient contains `d_r ^ 2`: this is the coefficient implied
by `‖A u - B v‖ ≤ d_r(A, B) * ‖u - v‖`.

Three documented deviations from the paper:

* the printed exponent `2/d_r(A_μ,A_{μ'})²` (paper's display of Theorem 5.4) is
  evidently a typo: the estimate that the paper's own proof uses,
  `‖A_{μ'}v - A_μ u‖ ≤ d_r‖v - u‖`, yields `2·d_r²` in the exponent, which is
  what is proved here;
* the paper's `d_r(A_μ,A_{μ'})` controls only the pairs with `u ≠ v`, while the
  term the proof has to bound, `‖A_μ(x_μ t) - A_{μ'}(x_{μ'} t)‖`, is taken at
  points where the two trajectories may coincide.  Reading the bound at
  `u = v` would force `A_μ = A_{μ'}` on the whole ball, which typical
  parametric families fail.  The hypothesis below therefore keeps the paper's
  ratio bound for all pairs and adds an *additive slack* `ε μ μ' ≥ 0`; the
  conclusion carries the matching Gronwall term
  `(2m)⁻¹(e^{2mT} - 1)·ε μ μ'`.  At `ε = 0` this is exactly the paper's
  statement, and `ε > 0` is genuinely needed — the paper's own hypotheses do
  not exclude it;
* as in the paper, no cocoercivity of `A_μ` is assumed. -/
theorem thm_4 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ) (ε : M → M → ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (r T : ℝ)
    (hr : 0 < r) (hT : 0 < T)
    (hsol : ∀ μ, μ ∈ V →
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hball : ∀ μ, μ ∈ V → ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ r)
    (hdist : ∀ μ, μ ∈ V → ∀ μ', μ' ∈ V →
      let d := def_8 r hr (A μ) (A μ')
      0 ≤ d ∧ 0 ≤ ε μ μ' ∧ ∀ u v : H, ‖u‖ ≤ r → ‖v‖ ≤ r →
        ‖A μ u - A μ' v‖ ≤ d * ‖u - v‖ + ε μ μ') :
    ∀ μ, μ ∈ V → ∀ μ', μ' ∈ V →
      let d := def_8 r hr (A μ) (A μ')
      let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 * d ^ 2)
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
            Real.exp ((2 * m) * T) +
          (2 * m)⁻¹ * (Real.exp ((2 * m) * T) - 1) * ε μ μ' := by
  intro μ hμ μ' hμ'
  dsimp only
  let d := def_8 r hr (A μ) (A μ')
  let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 * d ^ 2)
  change ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
    ‖x μ t - x μ' t‖ ≤
      Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
        Real.exp ((2 * m) * T) +
      (2 * m)⁻¹ * (Real.exp ((2 * m) * T) - 1) * ε μ μ'
  obtain ⟨hd0, hε0, hdist_bound⟩ := hdist μ hμ μ' hμ'
  change 0 ≤ d at hd0
  change 0 ≤ ε μ μ' at hε0
  change ∀ u v : H, ‖u‖ ≤ r → ‖v‖ ≤ r →
    ‖A μ u - A μ' v‖ ≤ d * ‖u - v‖ + ε μ μ' at hdist_bound
  obtain ⟨_, hdefμ⟩ := hsol μ hμ
  obtain ⟨_, hdefμ'⟩ := hsol μ' hμ'
  rcases hdefμ with ⟨hlacμ, hx0μ, hdx0μ, hxderivμ, hdxderivμ, hodeμ⟩
  rcases hdefμ' with
    ⟨hlacμ', hx0μ', hdx0μ', hxderivμ', hdxderivμ', hodeμ'⟩
  obtain ⟨hxACμ, hdxACμ⟩ := hlacμ T hT
  obtain ⟨hxACμ', hdxACμ'⟩ := hlacμ' T hT
  have hxderivμ_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderivμ
  have hxderivμ'_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderivμ'
  have hdxderivμ_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderivμ
  have hdxderivμ'_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderivμ'
  have hodeμ_vol := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hodeμ
  have hodeμ'_vol := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hodeμ'
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
  have hw0 : w 0 =
      ‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2 := by
    simp only [w, y, z, hx0μ, hx0μ', hdx0μ, hdx0μ']
  have hwDeriv : ∀ᵐ t ∂MeasureTheory.volume, 0 ≤ t →
      HasDerivAt w
        (2 * inner ℝ (y t) (z t) +
          2 * inner ℝ (z t) (ddx μ t - ddx μ' t)) t := by
    filter_upwards [hxderivμ_vol, hxderivμ'_vol, hdxderivμ_vol,
      hdxderivμ'_vol] with
      t hxμ hxμ' hdxμ hdxμ'
    intro ht
    have hyD : HasDerivAt y (z t) t := by
      simpa [y, z] using (hxμ ht).sub (hxμ' ht)
    have hzD : HasDerivAt z (ddx μ t - ddx μ' t) t := by
      simpa [z] using (hdxμ ht).sub (hdxμ' ht)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  have hm_sq : m ^ 2 = 1 + 2 * γ ^ 2 + 2 * d ^ 2 := by
    apply Real.sq_sqrt
    positivity
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hm : 0 < m := by
    have hmone : 1 ≤ m := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg γ, sq_nonneg d]
    linarith
  -- the `ε`-free part of the pair norm, bounded by `m √w`
  have hfield_sq (t : ℝ) :
      ‖z t‖ ^ 2 + (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤ m ^ 2 * w t := by
    have hsumSq : (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤
        2 * γ ^ 2 * ‖z t‖ ^ 2 + 2 * d ^ 2 * ‖y t‖ ^ 2 := by
      calc
        (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤
            2 * (|γ| * ‖z t‖) ^ 2 + 2 * (d * ‖y t‖) ^ 2 := by
          nlinarith [sq_nonneg (|γ| * ‖z t‖ - d * ‖y t‖)]
        _ = 2 * γ ^ 2 * ‖z t‖ ^ 2 + 2 * d ^ 2 * ‖y t‖ ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
          ring
    rw [hm_sq]
    dsimp [w]
    calc
      ‖z t‖ ^ 2 + (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤
          ‖z t‖ ^ 2 +
            (2 * γ ^ 2 * ‖z t‖ ^ 2 + 2 * d ^ 2 * ‖y t‖ ^ 2) := by
        linarith [hsumSq]
      _ ≤ (1 + 2 * γ ^ 2 + 2 * d ^ 2) *
          (‖y t‖ ^ 2 + ‖z t‖ ^ 2) := by
        have hγ : 0 ≤ γ ^ 2 := sq_nonneg _
        have hd : 0 ≤ d ^ 2 := sq_nonneg _
        have hy : 0 ≤ ‖y t‖ ^ 2 := sq_nonneg _
        have hz : 0 ≤ ‖z t‖ ^ 2 := sq_nonneg _
        ring_nf
        nlinarith [mul_nonneg hγ hy, mul_nonneg hγ hz,
          mul_nonneg hd hy, mul_nonneg hd hz]
  have hfield_sqrt (t : ℝ)
      (hforce : ‖A μ (x μ t) - A μ' (x μ' t)‖ ≤ d * ‖y t‖ + ε μ μ') :
      Real.sqrt (‖z t‖ ^ 2 +
          ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2) ≤
        m * Real.sqrt (w t) + ε μ μ' := by
    have hacc :
        ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ≤
          |γ| * ‖z t‖ + d * ‖y t‖ + ε μ μ' := by
      calc
        ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ≤
            ‖-γ • z t‖ + ‖A μ (x μ t) - A μ' (x μ' t)‖ := norm_sub_le _ _
        _ ≤ |γ| * ‖z t‖ + (d * ‖y t‖ + ε μ μ') := by
          simpa [norm_smul] using add_le_add_left hforce ‖-γ • z t‖
        _ = |γ| * ‖z t‖ + d * ‖y t‖ + ε μ μ' := by ring
    have hstep : ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
        (|γ| * ‖z t‖ + d * ‖y t‖ + ε μ μ') ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (add_nonneg (mul_nonneg (abs_nonneg γ) (norm_nonneg _))
          (mul_nonneg hd0 (norm_nonneg _))) hε0)).mpr hacc
    have hAle : |γ| * ‖z t‖ + d * ‖y t‖ ≤ m * Real.sqrt (w t) := by
      have hA2 : (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤ m ^ 2 * w t := by
        linarith [hfield_sq t, sq_nonneg ‖z t‖]
      have hwrt : (m * Real.sqrt (w t)) ^ 2 = m ^ 2 * w t := by
        rw [mul_pow, Real.sq_sqrt (hw_nonneg t)]
      rw [← hwrt] at hA2
      exact (sq_le_sq₀
        (add_nonneg (mul_nonneg (abs_nonneg γ) (norm_nonneg _))
          (mul_nonneg hd0 (norm_nonneg _)))
        (mul_nonneg hm0 (Real.sqrt_nonneg _))).mp hA2
    have hAε : ‖z t‖ ^ 2 + (|γ| * ‖z t‖ + d * ‖y t‖ + ε μ μ') ^ 2 ≤
        (m * Real.sqrt (w t) + ε μ μ') ^ 2 := by
      have h2 : (|γ| * ‖z t‖ + d * ‖y t‖) * ε μ μ' ≤
          (m * Real.sqrt (w t)) * ε μ μ' :=
        mul_le_mul_of_nonneg_right hAle hε0
      have hident : (m * Real.sqrt (w t) + ε μ μ') ^ 2 =
          m ^ 2 * w t + 2 * ((m * Real.sqrt (w t)) * ε μ μ') + (ε μ μ') ^ 2 := by
        rw [show (m * Real.sqrt (w t) + ε μ μ') ^ 2 =
            (m * Real.sqrt (w t)) ^ 2 + 2 * (m * Real.sqrt (w t)) * (ε μ μ') +
              (ε μ μ') ^ 2 by ring]
        rw [mul_pow, Real.sq_sqrt (hw_nonneg t)]
        ring
      calc
        ‖z t‖ ^ 2 + (|γ| * ‖z t‖ + d * ‖y t‖ + ε μ μ') ^ 2 =
            (‖z t‖ ^ 2 + (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2) +
              2 * ((|γ| * ‖z t‖ + d * ‖y t‖) * ε μ μ') + (ε μ μ') ^ 2 := by
          ring
        _ ≤ m ^ 2 * w t + 2 * ((m * Real.sqrt (w t)) * ε μ μ') + (ε μ μ') ^ 2 := by
          linarith [hfield_sq t, h2]
        _ = (m * Real.sqrt (w t) + ε μ μ') ^ 2 := hident.symm
    calc
      Real.sqrt (‖z t‖ ^ 2 +
          ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2) ≤
          Real.sqrt ((m * Real.sqrt (w t) + ε μ μ') ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [hstep, hAε])
      _ = m * Real.sqrt (w t) + ε μ μ' :=
        Real.sqrt_sq (add_nonneg (mul_nonneg hm0 (Real.sqrt_nonneg _)) hε0)
  have hfield_pair (t : ℝ)
      (hforce : ‖A μ (x μ t) - A μ' (x μ' t)‖ ≤ d * ‖y t‖ + ε μ μ') :
      inner ℝ (y t) (z t) +
          inner ℝ (z t) (-γ • z t - (A μ (x μ t) - A μ' (x μ' t))) ≤
        m * w t + ε μ μ' * Real.sqrt (w t) := by
    have hsqrt := hfield_sqrt t hforce
    have hpair := two_pairing_le (y t) (z t) (z t)
      (-γ • z t - (A μ (x μ t) - A μ' (x μ' t)))
    have hwrt : Real.sqrt (w t) * Real.sqrt (w t) = w t := by
      rw [← sq, Real.sq_sqrt (hw_nonneg t)]
    calc
      inner ℝ (y t) (z t) +
          inner ℝ (z t) (-γ • z t - (A μ (x μ t) - A μ' (x μ' t))) ≤
          Real.sqrt (‖y t‖ ^ 2 + ‖z t‖ ^ 2) *
            Real.sqrt (‖z t‖ ^ 2 +
              ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2) := hpair
      _ ≤ Real.sqrt (w t) * (m * Real.sqrt (w t) + ε μ μ') := by
        simpa [w] using mul_le_mul_of_nonneg_left hsqrt
          (Real.sqrt_nonneg (‖y t‖ ^ 2 + ‖z t‖ ^ 2))
      _ = m * w t + ε μ μ' * Real.sqrt (w t) := by
        have : Real.sqrt (w t) * (m * Real.sqrt (w t) + ε μ μ') =
            m * (Real.sqrt (w t) * Real.sqrt (w t)) + ε μ μ' * Real.sqrt (w t) :=
          by ring
        rw [this, hwrt]
  have hineq : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w t ≤
        (2 * m) * w t + ε μ μ' * w t ^ (1 / 2 : ℝ) := by
    filter_upwards [hodeμ_vol, hodeμ'_vol, hwDeriv, hball μ hμ,
      hball μ' hμ'] with t htodeμ htodeμ' htderiv htballμ htballμ'
    intro htIcc
    have hddxμ : ddx μ t = -γ • dx μ t - A μ (x μ t) := by
      calc
        ddx μ t = -(γ • dx μ t + A μ (x μ t)) :=
          eq_neg_of_add_eq_zero_left (by
            simpa [add_assoc] using htodeμ htIcc.1)
        _ = -γ • dx μ t - A μ (x μ t) := by module
    have hddxμ' : ddx μ' t = -γ • dx μ' t - A μ' (x μ' t) := by
      calc
        ddx μ' t = -(γ • dx μ' t + A μ' (x μ' t)) :=
          eq_neg_of_add_eq_zero_left (by
            simpa [add_assoc] using htodeμ' htIcc.1)
        _ = -γ • dx μ' t - A μ' (x μ' t) := by module
    have hddx : ddx μ t - ddx μ' t =
        -γ • z t - (A μ (x μ t) - A μ' (x μ' t)) := by
      rw [hddxμ, hddxμ']
      dsimp [z]
      module
    have hforce : ‖A μ (x μ t) - A μ' (x μ' t)‖ ≤ d * ‖y t‖ + ε μ μ' := by
      simpa [y] using hdist_bound (x μ t) (x μ' t)
        (htballμ htIcc) (htballμ' htIcc)
    have hderiv_eq : deriv w t =
        2 * (inner ℝ (y t) (z t) +
          inner ℝ (z t) (ddx μ t - ddx μ' t)) := by
      rw [(htderiv htIcc.1).deriv]
      ring
    calc
      (1 - (1 / 2 : ℝ)) * deriv w t =
          inner ℝ (y t) (z t) +
            inner ℝ (z t)
              (-γ • z t - (A μ (x μ t) - A μ' (x μ' t))) := by
        rw [hderiv_eq, hddx]
        ring
      _ ≤ m * w t + ε μ μ' * Real.sqrt (w t) := hfield_pair t hforce
      _ ≤ (2 * m) * w t + ε μ μ' * w t ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        have hm2 : m * w t ≤ (2 * m) * w t :=
          mul_le_mul_of_nonneg_right (by linarith [hm0]) (hw_nonneg t)
        linarith
  have hgronwall := ext_lem_1 (w := w) (a := fun _ : ℝ => 2 * m)
    (b := fun _ : ℝ => ε μ μ') (t₀ := 0) (T := T) (α := (1 / 2 : ℝ))
    hT (by norm_num) (by norm_num) (by simpa using hwAC)
    (by intro t ht; exact hw_nonneg t)
    (by exact MeasureTheory.integrableOn_const (by simp [Real.volume_Icc]))
    (by exact MeasureTheory.integrableOn_const (by simp [Real.volume_Icc]))
    (Filter.Eventually.of_forall (fun t _ => hε0)) (by simpa using hineq)
  apply Filter.Eventually.of_forall
  intro t htIcc
  have hgr := hgronwall t htIcc.1 (by simpa using htIcc.2)
  have hAint : (∫ τ in (0 : ℝ)..t, (2 * m : ℝ)) = (2 * m) * t := by
    rw [intervalIntegral.integral_const]
    ring
  have hBint : (∫ s in (0 : ℝ)..t,
      Real.exp (∫ τ in s..t, (2 * m : ℝ)) * (ε μ μ')) =
      (2 * m)⁻¹ * (Real.exp ((2 * m) * t) - 1) * (ε μ μ') := by
    have hcongr : (∫ s in (0 : ℝ)..t,
        Real.exp (∫ τ in s..t, (2 * m : ℝ)) * (ε μ μ')) =
        ∫ s in (0 : ℝ)..t, Real.exp ((2 * m) * (t - s)) * (ε μ μ') := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [intervalIntegral.integral_const]
      ring
    rw [hcongr, exp_kernel_integral (2 * m) (ε μ μ') t (by linarith)]
  rw [hAint, hBint] at hgr
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hy_le : ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := by
    change ‖y t‖ ≤ Real.sqrt (w t)
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  have hexp : Real.exp ((2 * m) * t) ≤ Real.exp ((2 * m) * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htIcc.2 (by positivity)
  have hexp1 : Real.exp ((2 * m) * t) - 1 ≤ Real.exp ((2 * m) * T) - 1 := by
    linarith
  have hinit : 0 ≤
      Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) :=
    Real.sqrt_nonneg _
  have hc0 : 0 ≤ (2 * m)⁻¹ := by positivity
  calc
    ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := hy_le
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
          Real.exp ((2 * m) * t) +
        (2 * m)⁻¹ * (Real.exp ((2 * m) * t) - 1) * ε μ μ' := by
      convert hgr using 1
      all_goals ring
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
          Real.exp ((2 * m) * T) +
        (2 * m)⁻¹ * (Real.exp ((2 * m) * T) - 1) * ε μ μ' := by
      refine add_le_add (mul_le_mul_of_nonneg_left hexp hinit) ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp1 hc0) hε0

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
