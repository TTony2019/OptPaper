import TheoremLib.Dual_guided_2026.SDOTLinearization

/-!
# Fourth moments for the categorical variance term

The leading variance can be computed from exact iid fourth moments, without
using a central limit theorem or a convergence-of-moments assertion.
-/

namespace DualGuided2026

open MeasureTheory ProbabilityTheory
open scoped BigOperators

section FourthMoments

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]

theorem memLp_pow_of_bound {f : Y → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC : 0 ≤ C) (hbound : ∀ y, ‖f y‖ ≤ C) (p : ℕ) :
    MemLp (fun y => (f y) ^ p) 2 μ := by
  apply MemLp.of_bound (hf.pow_const p).aestronglyMeasurable (C ^ p)
  exact Filter.Eventually.of_forall fun y => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound y) _

theorem integral_add_fourth_of_independent {f g : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfbound : ∀ y, ‖f y‖ ≤ C) (hgbound : ∀ y, ‖g y‖ ≤ D)
    (hindep : IndepFun f g μ) (hfzero : (∫ y, f y ∂μ) = 0)
    (hgzero : (∫ y, g y ∂μ) = 0) :
    (∫ y, (f y + g y) ^ 4 ∂μ) =
      (∫ y, (f y) ^ 4 ∂μ) +
        6 * (∫ y, (f y) ^ 2 ∂μ) * (∫ y, (g y) ^ 2 ∂μ) +
        (∫ y, (g y) ^ 4 ∂μ) := by
  have hfi (p : ℕ) := (memLp_pow_of_bound (μ := μ) hf hC hfbound p).integrable (by norm_num)
  have hgi (p : ℕ) := (memLp_pow_of_bound (μ := μ) hg hD hgbound p).integrable (by norm_num)
  have hfg (p q : ℕ) : Integrable (fun y => (f y) ^ p * (g y) ^ q) μ :=
    (memLp_pow_of_bound (μ := μ) hf hC hfbound p).integrable_mul
      (memLp_pow_of_bound (μ := μ) hg hD hgbound q)
  have hprod (p q : ℕ) : (∫ y, (f y) ^ p * (g y) ^ q ∂μ) =
      (∫ y, (f y) ^ p ∂μ) * (∫ y, (g y) ^ q ∂μ) := by
    have h := hindep.comp (measurable_id.pow_const p) (measurable_id.pow_const q)
    exact h.integral_fun_mul_eq_mul_integral (hf.pow_const p).aestronglyMeasurable
      (hg.pow_const q).aestronglyMeasurable
  have hpoly : (fun y => (f y + g y) ^ 4) =
      (fun y => (f y) ^ 4 + 4 * ((f y) ^ 3 * g y) +
        6 * ((f y) ^ 2 * (g y) ^ 2) + 4 * (f y * (g y) ^ 3) + (g y) ^ 4) := by
    funext y
    ring
  have h31i : Integrable (fun y => f y ^ 3 * g y) μ := by simpa using hfg 3 1
  have h13i : Integrable (fun y => f y * g y ^ 3) μ := by simpa using hfg 1 3
  have hi1 : Integrable (fun y => f y ^ 4 + 4 * (f y ^ 3 * g y)) μ :=
    (hfi 4).add (h31i.const_mul 4)
  have hi2 : Integrable (fun y => f y ^ 4 + 4 * (f y ^ 3 * g y) +
      6 * (f y ^ 2 * g y ^ 2)) μ := hi1.add ((hfg 2 2).const_mul 6)
  have hi3 : Integrable (fun y => f y ^ 4 + 4 * (f y ^ 3 * g y) +
      6 * (f y ^ 2 * g y ^ 2) + 4 * (f y * g y ^ 3)) μ := hi2.add (h13i.const_mul 4)
  rw [hpoly, integral_add hi3 (hgi 4), integral_add hi2 (h13i.const_mul 4),
    integral_add hi1 ((hfg 2 2).const_mul 6), integral_add (hfi 4) (h31i.const_mul 4)]
  simp only [integral_const_mul]
  have h31 := hprod 3 1
  have h13 := hprod 1 3
  simp only [pow_one, hfzero, hgzero, mul_zero, zero_mul] at h31 h13
  rw [h31, h13, hprod 2 2]
  ring

theorem integral_sum_fourth_iid {f : Y → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfbound : ∀ y, ‖f y‖ ≤ C)
    (hfzero : (∫ y, f y ∂μ) = 0) {ι : Type*} [Fintype ι] (s : Finset ι) :
    (∫ samples, (∑ i ∈ s, f (samples i)) ^ 4 ∂Measure.pi (fun _ : ι => μ)) =
      (s.card : ℝ) * (∫ y, (f y) ^ 4 ∂μ) +
        3 * (s.card : ℝ) * ((s.card : ℝ) - 1) * (∫ y, (f y) ^ 2 ∂μ) ^ 2 := by
  classical
  let μi := Measure.pi (fun _ : ι => μ)
  have hmem : MemLp f 2 μ := by simpa using memLp_pow_of_bound (μ := μ) hf hC hfbound 1
  have hmemi (i : ι) : MemLp (fun samples : ι → Y => f (samples i)) 2 μi :=
    hmem.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)
  have hmeasi (i : ι) : Measurable (fun samples : ι → Y => f (samples i)) :=
    hf.comp (measurable_pi_apply i)
  have hiindep : iIndepFun (fun i (samples : ι → Y) => f (samples i)) μi :=
    iIndepFun_pi (fun _ => hf.aemeasurable)
  have hint (p : ℕ) (i : ι) :
      (∫ samples : ι → Y, (f (samples i)) ^ p ∂μi) = ∫ y, (f y) ^ p ∂μ :=
    integral_comp_eval (μ := fun _ : ι => μ) (i := i) (hf.pow_const p).aestronglyMeasurable
  have hbound (t : Finset ι) (samples : ι → Y) :
      ‖∑ i ∈ t, f (samples i)‖ ≤ (t.card : ℝ) * C := by
    calc
      ‖∑ i ∈ t, f (samples i)‖ ≤ ∑ i ∈ t, ‖f (samples i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t, C := Finset.sum_le_sum (fun i _ => hfbound (samples i))
      _ = (t.card : ℝ) * C := by simp
  have hzero (t : Finset ι) : (∫ samples : ι → Y, ∑ i ∈ t, f (samples i) ∂μi) = 0 := by
    rw [integral_finset_sum t (fun i _ => (hmemi i).integrable (by norm_num))]
    have hintone (i : ι) : (∫ samples : ι → Y, f (samples i) ∂μi) = 0 := by
      simpa [hfzero] using hint 1 i
    simp [hintone]
  have hsecond (t : Finset ι) :
      (∫ samples : ι → Y, (∑ i ∈ t, f (samples i)) ^ 2 ∂μi) =
        (t.card : ℝ) * (∫ y, (f y) ^ 2 ∂μ) := by
    have hvar := IndepFun.variance_sum (fun i (_ : i ∈ t) => hmemi i)
      (fun i _ j _ hij => hiindep.indepFun hij)
    have hsumfun : (∑ i ∈ t, fun samples : ι → Y => f (samples i)) =
        (fun samples => ∑ i ∈ t, f (samples i)) := by ext samples; simp
    rw [hsumfun, variance_eq_sub (memLp_finset_sum t (fun i _ => hmemi i)), hzero] at hvar
    simp only [Pi.pow_apply, zero_pow (show (2 : ℕ) ≠ 0 by decide), sub_zero] at hvar
    have hvari (i : ι) : variance (fun samples : ι → Y => f (samples i)) μi =
        variance f μ :=
      (measurePreserving_eval (fun _ : ι => μ) i).variance_fun_comp hmem.aemeasurable
    simp only [hvari, variance_eq_sub hmem, hfzero, Pi.pow_apply,
      zero_pow (by decide : (2 : ℕ) ≠ 0),
      sub_zero, Finset.sum_const, nsmul_eq_mul] at hvar
    exact hvar
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hit ht =>
    have hsummeas : Measurable (fun samples : ι → Y => ∑ j ∈ t, f (samples j)) :=
      Finset.measurable_sum t (fun j _ => hmeasi j)
    have hindep : IndepFun (fun samples : ι → Y => ∑ j ∈ t, f (samples j))
        (fun samples => f (samples i)) μi := by
      have h := hiindep.indepFun_finset_sum_of_notMem hmeasi hit
      have heq : (∑ j ∈ t, fun samples : ι → Y => f (samples j)) =
          (fun samples => ∑ j ∈ t, f (samples j)) := by ext samples; simp
      rwa [heq] at h
    have hfour := integral_add_fourth_of_independent hsummeas (hmeasi i)
      (mul_nonneg (Nat.cast_nonneg _) hC) hC (hbound t) (fun samples => hfbound (samples i))
      hindep (hzero t) (by simpa [hfzero] using hint 1 i)
    rw [hsecond t, hint 2 i, hint 4 i] at hfour
    simp only [Finset.sum_insert hit, Finset.card_insert_of_notMem hit, Nat.cast_add,
      Nat.cast_one]
    rw [show (fun samples : ι → Y => (f (samples i) + ∑ j ∈ t, f (samples j)) ^ 4) =
      (fun samples => (∑ j ∈ t, f (samples j) + f (samples i)) ^ 4) from
      funext (fun _ => by rw [add_comm])]
    rw [hfour, ht]
    ring

theorem integral_iidAverage_fourth {f : Y → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfbound : ∀ y, ‖f y‖ ≤ C)
    (hfzero : (∫ y, f y ∂μ) = 0) {k : ℕ} (hk : 0 < k) :
    (∫ samples, (iidAverage f k samples) ^ 4 ∂Measure.pi (fun _ : Fin k => μ)) =
      ((∫ y, (f y) ^ 4 ∂μ) +
        3 * ((k : ℝ) - 1) * (∫ y, (f y) ^ 2 ∂μ) ^ 2) / (k : ℝ) ^ 3 := by
  simp only [iidAverage, mul_pow, integral_const_mul]
  rw [integral_sum_fourth_iid hf hC hfbound hfzero]
  simp only [Finset.card_univ, Fintype.card_fin]
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

omit [MeasurableSpace Y] in
theorem norm_iidAverage_le {f : Y → ℝ} {C : ℝ}
    (hfbound : ∀ y, ‖f y‖ ≤ C) {k : ℕ} (hk : 0 < k) (samples : Fin k → Y) :
    ‖iidAverage f k samples‖ ≤ C := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [iidAverage, norm_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hkreal)]
  calc
    (1 / (k : ℝ)) * |∑ i, f (samples i)| ≤
        (1 / (k : ℝ)) * ∑ i, |f (samples i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (one_div_pos.mpr hkreal).le
    _ ≤ (1 / (k : ℝ)) * ∑ _i : Fin k, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hfbound (samples i)))
        (one_div_pos.mpr hkreal).le
    _ = C := by simp; field_simp

omit [IsProbabilityMeasure μ] in
theorem integral_add_sq_of_memLp {f g : Y → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ y, (f y + g y) ^ 2 ∂μ) = (∫ y, (f y) ^ 2 ∂μ) +
      2 * (∫ y, f y * g y ∂μ) + (∫ y, (g y) ^ 2 ∂μ) := by
  have hpoly : (fun y => (f y + g y) ^ 2) =
      (fun y => (f y) ^ 2 + 2 * (f y * g y) + (g y) ^ 2) := by funext y; ring
  have hfg : Integrable (fun y => f y * g y) μ := hf.integrable_mul hg
  have hi : Integrable (fun y => (f y) ^ 2 + 2 * (f y * g y)) μ :=
    hf.integrable_sq.add (hfg.const_mul 2)
  rw [hpoly, integral_add hi hg.integrable_sq,
    integral_add hf.integrable_sq (hfg.const_mul 2), integral_const_mul]

theorem integral_fourth_polarization {f g : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfbound : ∀ y, ‖f y‖ ≤ C) (hgbound : ∀ y, ‖g y‖ ≤ D) :
    (∫ y, (f y + g y) ^ 4 ∂μ) + (∫ y, (f y - g y) ^ 4 ∂μ) =
      2 * (∫ y, (f y) ^ 4 ∂μ) +
        12 * (∫ y, (f y) ^ 2 * (g y) ^ 2 ∂μ) + 2 * (∫ y, (g y) ^ 4 ∂μ) := by
  have hfb (y : Y) : ‖f y + g y‖ ≤ C + D :=
    (norm_add_le _ _).trans (add_le_add (hfbound y) (hgbound y))
  have hgb (y : Y) : ‖f y - g y‖ ≤ C + D :=
    (norm_sub_le _ _).trans (add_le_add (hfbound y) (hgbound y))
  have hfi (p : ℕ) := (memLp_pow_of_bound (μ := μ) hf hC hfbound p).integrable (by norm_num)
  have hgi (p : ℕ) := (memLp_pow_of_bound (μ := μ) hg hD hgbound p).integrable (by norm_num)
  have hcross : Integrable (fun y => f y ^ 2 * g y ^ 2) μ :=
    (memLp_pow_of_bound (μ := μ) hf hC hfbound 2).integrable_mul
      (memLp_pow_of_bound (μ := μ) hg hD hgbound 2)
  have hi : Integrable (fun y => 2 * f y ^ 4 + 12 * (f y ^ 2 * g y ^ 2)) μ :=
    ((hfi 4).const_mul 2).add (hcross.const_mul 12)
  have hplus := memLp_pow_of_bound (μ := μ) (hf.add hg) (add_nonneg hC hD) hfb 4
  have hminus := memLp_pow_of_bound (μ := μ) (hf.sub hg) (add_nonneg hC hD) hgb 4
  rw [← integral_add (hplus.integrable (by norm_num)) (hminus.integrable (by norm_num))]
  rw [show (fun y => (f y + g y) ^ 4 + (f y - g y) ^ 4) =
    (fun y => 2 * f y ^ 4 + 12 * (f y ^ 2 * g y ^ 2) + 2 * g y ^ 4) from funext (fun _ => by ring)]
  rw [integral_add hi ((hgi 4).const_mul 2),
    integral_add ((hfi 4).const_mul 2) (hcross.const_mul 12)]
  simp only [integral_const_mul]

theorem integral_iidAverage_mixed_fourth {f g : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfbound : ∀ y, ‖f y‖ ≤ C) (hgbound : ∀ y, ‖g y‖ ≤ D)
    (hfzero : (∫ y, f y ∂μ) = 0) (hgzero : (∫ y, g y ∂μ) = 0)
    {k : ℕ} (hk : 0 < k) :
    (∫ samples, (iidAverage f k samples) ^ 2 * (iidAverage g k samples) ^ 2
      ∂Measure.pi (fun _ : Fin k => μ)) =
      ((∫ y, (f y) ^ 2 * (g y) ^ 2 ∂μ) + ((k : ℝ) - 1) *
        ((∫ y, (f y) ^ 2 ∂μ) * (∫ y, (g y) ^ 2 ∂μ) +
          2 * (∫ y, f y * g y ∂μ) ^ 2)) / (k : ℝ) ^ 3 := by
  have hfmem : MemLp f 2 μ := by simpa using memLp_pow_of_bound (μ := μ) hf hC hfbound 1
  have hgmem : MemLp g 2 μ := by simpa using memLp_pow_of_bound (μ := μ) hg hD hgbound 1
  have hfb (y : Y) : ‖f y + g y‖ ≤ C + D :=
    (norm_add_le _ _).trans (add_le_add (hfbound y) (hgbound y))
  have hgb (y : Y) : ‖f y - g y‖ ≤ C + D :=
    (norm_sub_le _ _).trans (add_le_add (hfbound y) (hgbound y))
  have hfpzero : (∫ y, f y + g y ∂μ) = 0 := by
    rw [integral_add (hfmem.integrable (by norm_num)) (hgmem.integrable (by norm_num)),
      hfzero, hgzero]
    ring
  have hfmzero : (∫ y, f y - g y ∂μ) = 0 := by
    rw [integral_sub (hfmem.integrable (by norm_num)) (hgmem.integrable (by norm_num)),
      hfzero, hgzero]
    ring
  have hplus := integral_iidAverage_fourth (μ := μ) (hf.add hg) (add_nonneg hC hD) hfb hfpzero hk
  have hminus := integral_iidAverage_fourth (μ := μ) (hf.sub hg) (add_nonneg hC hD) hgb hfmzero hk
  have hf4 := integral_iidAverage_fourth (μ := μ) hf hC hfbound hfzero hk
  have hg4 := integral_iidAverage_fourth (μ := μ) hg hD hgbound hgzero hk
  have hsource := integral_fourth_polarization (μ := μ) hf hg hC hD hfbound hgbound
  have hsecondplus := integral_add_sq_of_memLp hfmem hgmem
  have hsecondminus := integral_add_sq_of_memLp hfmem hgmem.neg
  simp only [Pi.neg_apply, mul_neg, integral_neg, ← sub_eq_add_neg] at hsecondminus
  have hnegsq : (fun y => (-g y) ^ 2) = (fun y => (g y) ^ 2) := by ext y; ring
  rw [hnegsq] at hsecondminus
  have hmeasf : Measurable (iidAverage f k) := by
    unfold iidAverage
    fun_prop
  have hmeasg : Measurable (iidAverage g k) := by
    unfold iidAverage
    fun_prop
  have havg := integral_fourth_polarization (μ := Measure.pi fun _ : Fin k => μ)
    hmeasf hmeasg hC hD (norm_iidAverage_le hfbound hk) (norm_iidAverage_le hgbound hk)
  have hlinearp : iidAverage (fun y => f y + g y) k =
      (fun samples => iidAverage f k samples + iidAverage g k samples) := by
    ext samples
    simp only [iidAverage, Finset.sum_add_distrib, mul_add]
  have hlinearm : iidAverage (fun y => f y - g y) k =
      (fun samples => iidAverage f k samples - iidAverage g k samples) := by
    ext samples
    simp only [iidAverage, Finset.sum_sub_distrib, mul_sub]
  rw [hlinearp] at hplus
  rw [hlinearm] at hminus
  rw [hsecondplus] at hplus
  rw [hsecondminus] at hminus
  rw [hplus, hminus, hf4, hg4] at havg
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  apply (eq_div_iff (pow_ne_zero _ hkreal)).mpr
  field_simp at havg
  nlinarith only [havg, hsource]

theorem integral_iidAverage_sq_of_centered {f : Y → ℝ}
    (hf : MemLp f 2 μ) (hfzero : (∫ y, f y ∂μ) = 0) {k : ℕ} (hk : 0 < k) :
    (∫ samples, (iidAverage f k samples) ^ 2 ∂Measure.pi (fun _ : Fin k => μ)) =
      (∫ y, (f y) ^ 2 ∂μ) / k := by
  have hvar := variance_eq_sub (memLp_iidAverage μ hf k)
  rw [integral_iidAverage μ hf hk, hfzero, variance_iidAverage μ hf hk,
    variance_eq_sub hf, hfzero] at hvar
  simpa only [Pi.pow_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hvar.symm

theorem integral_iidAverage_mul_of_centered {f g : Y → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfzero : (∫ y, f y ∂μ) = 0) (hgzero : (∫ y, g y ∂μ) = 0)
    {k : ℕ} (hk : 0 < k) :
    (∫ samples, iidAverage f k samples * iidAverage g k samples
      ∂Measure.pi (fun _ : Fin k => μ)) = (∫ y, f y * g y ∂μ) / k := by
  have hsumzero : (∫ y, (f + g) y ∂μ) = 0 := by
    simp only [Pi.add_apply]
    rw [integral_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num)), hfzero, hgzero]
    ring
  have hlinearp : iidAverage (f + g) k =
      (fun samples => iidAverage f k samples + iidAverage g k samples) := by
    ext samples
    simp only [iidAverage, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  have hsum := integral_iidAverage_sq_of_centered (hf.add hg) hsumzero hk
  simp only [Pi.add_apply] at hsum
  rw [hlinearp, integral_add_sq_of_memLp (memLp_iidAverage μ hf k) (memLp_iidAverage μ hg k),
    integral_add_sq_of_memLp hf hg, integral_iidAverage_sq_of_centered hf hfzero hk,
    integral_iidAverage_sq_of_centered hg hgzero hk] at hsum
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  apply (eq_div_iff hkreal).mpr
  field_simp at hsum
  linarith

theorem integral_nested_iidAverage_mixed_fourth {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsProbabilityMeasure ν] {f g : Y → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfbound : ∀ y, ‖f y‖ ≤ C) (hgbound : ∀ y, ‖g y‖ ≤ D)
    (hfzero : (∫ y, f y ∂μ) = 0) (hgzero : (∫ y, g y ∂μ) = 0)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    (∫ batches,
      (iidAverage (fun batch : (Fin m → Y) × Z => iidAverage f m batch.1) R batches) ^ 2 *
        (iidAverage (fun batch : (Fin m → Y) × Z => iidAverage g m batch.1) R batches) ^ 2
      ∂Measure.pi (fun _ : Fin R => (Measure.pi (fun _ : Fin m => μ)).prod ν)) =
      ((∫ y, (f y) ^ 2 * (g y) ^ 2 ∂μ) + ((m : ℝ) * R - 1) *
        ((∫ y, (f y) ^ 2 ∂μ) * (∫ y, (g y) ^ 2 ∂μ) +
          2 * (∫ y, f y * g y ∂μ) ^ 2)) / ((m : ℝ) * R) ^ 3 := by
  let μm := Measure.pi (fun _ : Fin m => μ)
  let F : (Fin m → Y) × Z → ℝ := fun batch => iidAverage f m batch.1
  let G : (Fin m → Y) × Z → ℝ := fun batch => iidAverage g m batch.1
  have hfmem : MemLp f 2 μ := by simpa using memLp_pow_of_bound (μ := μ) hf hC hfbound 1
  have hgmem : MemLp g 2 μ := by simpa using memLp_pow_of_bound (μ := μ) hg hD hgbound 1
  have hmeasF : Measurable F := by dsimp [F, iidAverage]; fun_prop
  have hmeasG : Measurable G := by dsimp [G, iidAverage]; fun_prop
  have hFzero : (∫ batch, F batch ∂μm.prod ν) = 0 := by
    dsimp [F, μm]
    rw [integral_fun_fst (iidAverage f m), integral_iidAverage μ hfmem hm, hfzero]
    simp
  have hGzero : (∫ batch, G batch ∂μm.prod ν) = 0 := by
    dsimp [G, μm]
    rw [integral_fun_fst (iidAverage g m), integral_iidAverage μ hgmem hm, hgzero]
    simp
  have hFsecond : (∫ batch, F batch ^ 2 ∂μm.prod ν) = (∫ y, f y ^ 2 ∂μ) / m := by
    dsimp [F, μm]
    rw [integral_fun_fst (fun samples => iidAverage f m samples ^ 2),
      integral_iidAverage_sq_of_centered hfmem hfzero hm]
    simp
  have hGsecond : (∫ batch, G batch ^ 2 ∂μm.prod ν) = (∫ y, g y ^ 2 ∂μ) / m := by
    dsimp [G, μm]
    rw [integral_fun_fst (fun samples => iidAverage g m samples ^ 2),
      integral_iidAverage_sq_of_centered hgmem hgzero hm]
    simp
  have hFG : (∫ batch, F batch * G batch ∂μm.prod ν) = (∫ y, f y * g y ∂μ) / m := by
    dsimp [F, G, μm]
    rw [integral_fun_fst (fun samples => iidAverage f m samples * iidAverage g m samples),
      integral_iidAverage_mul_of_centered hfmem hgmem hfzero hgzero hm]
    simp
  have hFGfourth : (∫ batch, F batch ^ 2 * G batch ^ 2 ∂μm.prod ν) =
      ((∫ y, f y ^ 2 * g y ^ 2 ∂μ) + ((m : ℝ) - 1) *
        ((∫ y, f y ^ 2 ∂μ) * (∫ y, g y ^ 2 ∂μ) +
          2 * (∫ y, f y * g y ∂μ) ^ 2)) / (m : ℝ) ^ 3 := by
    dsimp [F, G, μm]
    rw [integral_fun_fst (fun samples => iidAverage f m samples ^ 2 * iidAverage g m samples ^ 2),
      integral_iidAverage_mixed_fourth hf hg hC hD hfbound hgbound hfzero hgzero hm]
    simp
  have houter := integral_iidAverage_mixed_fourth (μ := μm.prod ν) hmeasF hmeasG hC hD
    (fun batch => norm_iidAverage_le hfbound hm batch.1)
    (fun batch => norm_iidAverage_le hgbound hm batch.1) hFzero hGzero hR
  rw [hFsecond, hGsecond, hFG, hFGfourth] at houter
  change (∫ batches, iidAverage F R batches ^ 2 * iidAverage G R batches ^ 2
    ∂Measure.pi (fun _ : Fin R => μm.prod ν)) = _
  rw [houter]
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hRreal : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp
  ring

end FourthMoments

section Categorical

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem measurable_centeredCellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : Measurable (centeredCellIndicator data g j) :=
  ((measurable_const.indicator (measurableSet_laguerreCell data g j)).sub measurable_const)

theorem norm_centeredCellIndicator_le (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) (x : X) :
    ‖centeredCellIndicator data g j x‖ ≤ 1 + data.populationMarginal g j := by
  have hind : ‖cellIndicator data g j x‖ ≤ 1 := by
    classical
    by_cases hx : x ∈ laguerreCell data g j <;> simp [cellIndicator, hx]
  unfold centeredCellIndicator
  calc
    ‖cellIndicator data g j x - data.populationMarginal g j‖ ≤
        ‖cellIndicator data g j x‖ + ‖data.populationMarginal g j‖ := norm_sub_le _ _
    _ ≤ 1 + data.populationMarginal g j := by
      rw [show ‖data.populationMarginal g j‖ = data.populationMarginal g j from
        Real.norm_of_nonneg (populationMarginal_nonneg data g j)]
      exact add_le_add hind le_rfl

theorem cellIndicator_mul (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j k : Fin data.n) (x : X) :
    cellIndicator data g j x * cellIndicator data g k x =
      if j = k then cellIndicator data g j x else 0 := by
  classical
  simp only [cellIndicator_eq_assignment]
  split_ifs <;> simp_all

theorem integral_centeredCellIndicator_mul (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j k : Fin data.n) :
    (∫ x, centeredCellIndicator data g j x * centeredCellIndicator data g k x
      ∂data.sourceMeasure) =
      (if j = k then data.populationMarginal g j else 0) -
        data.populationMarginal g j * data.populationMarginal g k := by
  classical
  have hj := (memLp_cellIndicator data g j).integrable (by norm_num)
  have hk := (memLp_cellIndicator data g k).integrable (by norm_num)
  have hprod : Integrable (fun x => cellIndicator data g j x * cellIndicator data g k x)
      data.sourceMeasure :=
    (memLp_cellIndicator data g j).integrable_mul (memLp_cellIndicator data g k)
  have hpoly : (fun x => centeredCellIndicator data g j x * centeredCellIndicator data g k x) =
      (fun x => cellIndicator data g j x * cellIndicator data g k x -
        data.populationMarginal g k * cellIndicator data g j x -
        data.populationMarginal g j * cellIndicator data g k x +
        data.populationMarginal g j * data.populationMarginal g k) := by
    ext x
    unfold centeredCellIndicator
    ring
  have hi : Integrable (fun x => cellIndicator data g j x * cellIndicator data g k x -
      data.populationMarginal g k * cellIndicator data g j x) data.sourceMeasure :=
    hprod.sub (hj.const_mul _)
  have hii : Integrable (fun x => cellIndicator data g j x * cellIndicator data g k x -
      data.populationMarginal g k * cellIndicator data g j x -
      data.populationMarginal g j * cellIndicator data g k x) data.sourceMeasure :=
    hi.sub (hk.const_mul _)
  rw [hpoly, integral_add hii (integrable_const _), integral_sub hi (hk.const_mul _),
    integral_sub hprod (hj.const_mul _)]
  simp only [integral_const_mul, integral_cellIndicator, integral_const,
    probReal_univ, one_smul]
  simp only [cellIndicator_mul]
  split_ifs with heq
  · rw [integral_cellIndicator]
    ring
  · simp
    ring

theorem categorical_covariance_square_sum (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b) :
    (∑ j, ∑ k, (∫ x, centeredCellIndicator data gStar j x *
      centeredCellIndicator data gStar k x ∂data.sourceMeasure) ^ 2 / (data.b j * data.b k)) =
      (data.n : ℝ) - 1 := by
  classical
  simp only [integral_centeredCellIndicator_mul, hbalanced]
  have hscalar (j k : Fin data.n) :
      ((if j = k then data.b j else 0) - data.b j * data.b k) ^ 2 / (data.b j * data.b k) =
        (if j = k then 1 - 2 * data.b j else 0) + data.b j * data.b k := by
    split_ifs with heq
    · subst k
      field_simp [(data.b_pos j).ne']
      ring
    · field_simp [(data.b_pos j).ne', (data.b_pos k).ne']
      ring
  simp only [hscalar, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum, data.b_sum,
    mul_one, Finset.sum_sub_distrib]
  simp
  ring

theorem integral_laguerreAssignment (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (v : Fin data.n → ℝ) :
    (∫ x, v (laguerreAssignment data g x) ∂data.sourceMeasure) =
      ∑ j, data.populationMarginal g j * v j := by
  rw [show (fun x => v (laguerreAssignment data g x)) =
    (fun x => ∑ j, cellIndicator data g j x * v j) from
    funext (fun x => (sum_cellIndicator_mul data g v x).symm)]
  rw [integral_finset_sum Finset.univ (fun j _ =>
    ((memLp_cellIndicator data g j).integrable (by norm_num)).mul_const (v j))]
  simp only [integral_mul_const, integral_cellIndicator]

theorem weightedSquare_centeredCellIndicator (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b) (x : X) :
    weightedSquare data (fun j => centeredCellIndicator data gStar j x) =
      1 / data.b (laguerreAssignment data gStar x) - 1 := by
  have hscalar (j : Fin data.n) : (centeredCellIndicator data gStar j x) ^ 2 / data.b j =
      cellIndicator data gStar j x * (1 / data.b j) -
        2 * cellIndicator data gStar j x + data.b j := by
    unfold centeredCellIndicator
    rw [hbalanced]
    have hs := cellIndicator_sq data gStar j x
    field_simp [(data.b_pos j).ne']
    nlinarith only [hs]
  have hsum : (∑ j, cellIndicator data gStar j x) = 1 := by
    simpa using sum_cellIndicator_mul data gStar (fun _ => 1) x
  simp only [weightedSquare, hscalar, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [sum_cellIndicator_mul, hsum, data.b_sum]
  ring

theorem categorical_single_fourth_energy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b) :
    (∫ x, (weightedSquare data (fun j => centeredCellIndicator data gStar j x)) ^ 2
      ∂data.sourceMeasure) = (∑ j, 1 / data.b j) - 2 * data.n + 1 := by
  simp only [weightedSquare_centeredCellIndicator data gStar hbalanced]
  rw [integral_laguerreAssignment data gStar (fun j => (1 / data.b j - 1) ^ 2)]
  rw [hbalanced]
  have hscalar (j : Fin data.n) : data.b j * (1 / data.b j - 1) ^ 2 =
      1 / data.b j - 2 + data.b j := by field_simp [(data.b_pos j).ne']; ring
  simp only [hscalar, Finset.sum_add_distrib, Finset.sum_sub_distrib, data.b_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_centeredCellIndicator_sq (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) :
    (∫ x, (centeredCellIndicator data g j x) ^ 2 ∂data.sourceMeasure) =
      data.populationMarginal g j * (1 - data.populationMarginal g j) := by
  have hvar := variance_eq_sub (memLp_centeredCellIndicator data g j)
  rw [integral_centeredCellIndicator, variance_centeredCellIndicator] at hvar
  simpa only [Pi.pow_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hvar.symm

theorem integral_averagedCategoricalFluctuation_mixed_fourth (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m R : ℕ} (hm : 0 < m) (hR : 0 < R) (j k : Fin data.n) :
    (∫ batches, (averagedCategoricalFluctuation data g m R batches j) ^ 2 *
      (averagedCategoricalFluctuation data g m R batches k) ^ 2 ∂repetitionMeasure data m R) =
      ((∫ x, (centeredCellIndicator data g j x) ^ 2 * (centeredCellIndicator data g k x) ^ 2
          ∂data.sourceMeasure) + ((m : ℝ) * R - 1) *
        (data.populationMarginal g j * (1 - data.populationMarginal g j) *
          (data.populationMarginal g k * (1 - data.populationMarginal g k)) +
            2 * (∫ x, centeredCellIndicator data g j x * centeredCellIndicator data g k x
              ∂data.sourceMeasure) ^ 2)) / ((m : ℝ) * R) ^ 3 := by
  have h := integral_nested_iidAverage_mixed_fourth (μ := data.sourceMeasure)
    (data.solverMeasure m)
    (measurable_centeredCellIndicator data g j) (measurable_centeredCellIndicator data g k)
    (add_nonneg zero_le_one (populationMarginal_nonneg data g j))
    (add_nonneg zero_le_one (populationMarginal_nonneg data g k))
    (norm_centeredCellIndicator_le data g j) (norm_centeredCellIndicator_le data g k)
    (integral_centeredCellIndicator data g j) (integral_centeredCellIndicator data g k) hm hR
  rw [integral_centeredCellIndicator_sq, integral_centeredCellIndicator_sq] at h
  exact h

theorem memLp_averagedCategoricalFluctuation_sq (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m R : ℕ} (hm : 0 < m) (hR : 0 < R) (j : Fin data.n) :
    MemLp (fun batches => (averagedCategoricalFluctuation data g m R batches j) ^ 2) 2
      (repetitionMeasure data m R) := by
  have hmeas : Measurable (fun batches => averagedCategoricalFluctuation data g m R batches j) := by
    unfold averagedCategoricalFluctuation batchCategoricalFluctuation
      sourceCategoricalFluctuation iidAverage
    exact measurable_const.mul (Finset.measurable_sum _ (fun r _ =>
      measurable_const.mul (Finset.measurable_sum _ (fun k _ =>
        (measurable_centeredCellIndicator data g j).comp
          ((measurable_pi_apply k).comp (measurable_fst.comp (measurable_pi_apply r)))))))
  apply memLp_pow_of_bound hmeas (add_nonneg zero_le_one (populationMarginal_nonneg data g j)) _ 2
  intro batches
  unfold averagedCategoricalFluctuation batchCategoricalFluctuation sourceCategoricalFluctuation
  apply norm_iidAverage_le _ hR
  intro batch
  exact norm_iidAverage_le (norm_centeredCellIndicator_le data g j) hm batch.1

theorem integral_weightedSquare_sq {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (data : HELLOSDOTData X Ω) (f : Y → Fin data.n → ℝ)
    (hf : ∀ j, MemLp (fun y => f y j ^ 2) 2 μ) :
    (∫ y, weightedSquare data (f y) ^ 2 ∂μ) =
      ∑ j, ∑ k, (∫ y, f y j ^ 2 * f y k ^ 2 ∂μ) / (data.b j * data.b k) := by
  have hpoly (y : Y) : weightedSquare data (f y) ^ 2 =
      ∑ j, ∑ k, (f y j ^ 2 * f y k ^ 2) / (data.b j * data.b k) := by
    simp only [weightedSquare, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [hpoly]
  have hpair (j k : Fin data.n) : Integrable (fun y =>
      f y j ^ 2 * f y k ^ 2 / (data.b j * data.b k)) μ :=
    ((hf j).integrable_mul (hf k)).div_const _
  have hsum (j : Fin data.n) : Integrable (fun y =>
      ∑ k, f y j ^ 2 * f y k ^ 2 / (data.b j * data.b k)) μ :=
    integrable_finset_sum Finset.univ (fun k _ => hpair j k)
  rw [integral_finset_sum Finset.univ (fun j _ => hsum j)]
  congr 1
  ext j
  rw [integral_finset_sum Finset.univ (fun k _ => hpair j k)]
  simp only [integral_div]

theorem categorical_fourth_moment (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    (∫ batches, (weightedSquare data (averagedCategoricalFluctuation data gStar m R batches)) ^ 2
      ∂repetitionMeasure data m R) =
      ((∑ j, 1 / data.b j) - 2 * data.n + 1 + ((m : ℝ) * R - 1) *
        (((data.n : ℝ) - 1) ^ 2 + 2 * ((data.n : ℝ) - 1))) / ((m : ℝ) * R) ^ 3 := by
  have hsource := integral_weightedSquare_sq data.sourceMeasure data
    (fun x j => centeredCellIndicator data gStar j x) (fun j =>
      memLp_pow_of_bound (measurable_centeredCellIndicator data gStar j)
        (add_nonneg zero_le_one (populationMarginal_nonneg data gStar j))
        (norm_centeredCellIndicator_le data gStar j) 2)
  rw [categorical_single_fourth_energy data gStar hbalanced] at hsource
  have hcov := categorical_covariance_square_sum data gStar hbalanced
  have hproduct : (∑ j, ∑ k, (data.b j * (1 - data.b j) *
        (data.b k * (1 - data.b k))) / (data.b j * data.b k)) = ((data.n : ℝ) - 1) ^ 2 := by
    have hscalar (j k : Fin data.n) : (data.b j * (1 - data.b j) *
        (data.b k * (1 - data.b k))) / (data.b j * data.b k) = (1 - data.b j) * (1 - data.b k) := by
      field_simp [(data.b_pos j).ne', (data.b_pos k).ne']
    simp only [hscalar, ← Finset.mul_sum, Finset.sum_sub_distrib, data.b_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Finset.sum_mul]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, data.b_sum]
    ring
  rw [integral_weightedSquare_sq (repetitionMeasure data m R) data
    (averagedCategoricalFluctuation data gStar m R)
    (memLp_averagedCategoricalFluctuation_sq data gStar hm hR)]
  simp only [integral_averagedCategoricalFluctuation_mixed_fourth data gStar hm hR, hbalanced]
  have hscalar (W A C : ℝ) (j k : Fin data.n) :
      (W + ((m : ℝ) * R - 1) * (A + 2 * C)) / ((m : ℝ) * R) ^ 3 /
        (data.b j * data.b k) =
      (W / (data.b j * data.b k) + ((m : ℝ) * R - 1) *
        (A / (data.b j * data.b k) + 2 * (C / (data.b j * data.b k)))) /
          ((m : ℝ) * R) ^ 3 := by ring
  simp only [hscalar, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← hsource, hproduct, hcov]

noncomputable def categoricalQuadraticError (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (m R : ℕ) (batches : Fin R → ((Fin m → X) × Ω)) : ℝ :=
  weightedSquare data (averagedCategoricalFluctuation data g m R batches)

theorem memLp_categoricalQuadraticError (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    MemLp (categoricalQuadraticError data g m R) 2 (repetitionMeasure data m R) := by
  unfold categoricalQuadraticError weightedSquare
  apply memLp_finset_sum Finset.univ
  intro j _
  convert (memLp_averagedCategoricalFluctuation_sq data g hm hR j).const_mul (1 / data.b j) using 1
  funext batches
  ring

/-- The Pearson quadratic error has an exact finite-sample variance. The
correction term is one order smaller than the variance in Theorem III.1. -/
theorem categorical_variance_exact (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    variance (categoricalQuadraticError data gStar m R) (repetitionMeasure data m R) =
      helloSDOTVarianceLeading data.n m R +
        ((∑ j, 1 / data.b j) - (data.n : ℝ) ^ 2 - 2 * data.n + 2) / ((m : ℝ) * R) ^ 3 := by
  rw [variance_eq_sub (memLp_categoricalQuadraticError data gStar hm hR)]
  simp only [categoricalQuadraticError, Pi.pow_apply]
  rw [categorical_fourth_moment data gStar hbalanced hm hR]
  have hmean : (∫ batches, weightedSquare data
      (averagedCategoricalFluctuation data gStar m R batches)
      ∂repetitionMeasure data m R) = helloSDOTMeanLeading data.n m R :=
    categorical_second_moment data gStar hbalanced hm hR
  rw [hmean]
  simp only [helloSDOTMeanLeading, helloSDOTVarianceLeading]
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hRreal : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp
  ring

theorem categorical_variance_asymptotic (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b) :
    IsUniformLittleOInM data.rmax
      (fun m R => variance (categoricalQuadraticError data gStar m R) (repetitionMeasure data m R) -
        helloSDOTVarianceLeading data.n m R) (fun m => 1 / (m : ℝ) ^ 2) := by
  intro δ hδ
  let C := (∑ j, 1 / data.b j) - (data.n : ℝ) ^ 2 - 2 * data.n + 2
  obtain ⟨M, hM⟩ := exists_nat_gt (|C| / δ + 1)
  refine ⟨M, ?_⟩
  intro m hm R hR _
  dsimp only
  have hmM : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hmreal : (1 : ℝ) < m := by
    have hCpos : 0 ≤ |C| / δ := div_nonneg (abs_nonneg _) hδ.le
    linarith
  have hmpos : (0 : ℝ) < m := (by norm_num : (0 : ℝ) < 1).trans hmreal
  have hmnat : 0 < m := by exact_mod_cast hmpos
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : 0 < R := Nat.zero_lt_one.trans_le hR
  have hNpos : (0 : ℝ) < (m : ℝ) * R := by positivity
  have hCsmall : |C| ≤ δ * m := by
    have hlt : |C| / δ < m := by linarith
    simpa [mul_comm] using ((div_lt_iff₀ hδ).mp hlt).le
  rw [categorical_variance_exact data gStar hbalanced hmnat hRpos, add_sub_cancel_left]
  change |C / ((m : ℝ) * R) ^ 3| ≤ δ * |1 / (m : ℝ) ^ 2|
  rw [abs_div, abs_pow, abs_of_pos hNpos,
    abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hmpos))]
  have hden : (m : ℝ) ^ 3 ≤ ((m : ℝ) * R) ^ 3 :=
    pow_le_pow_left₀ hmpos.le (by nlinarith) _
  calc
    |C| / ((m : ℝ) * R) ^ 3 ≤ |C| / (m : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hmpos _) hden
    _ ≤ δ / (m : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (pow_pos hmpos _) (sq_pos_of_pos hmpos)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hCsmall (sq_nonneg (m : ℝ))]
    _ = δ * (1 / (m : ℝ) ^ 2) := by ring

end Categorical

section Comparison

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]

theorem variance_difference_young_bound {f g : Y → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {ε : ℝ} (hε : 0 < ε) :
    |variance f μ - variance g μ| ≤ ε * variance g μ +
      ((1 + ε) / ε) * (∫ y, (f y - g y) ^ 2 ∂μ) := by
  let h := fun y => f y - g y
  have hh : MemLp h 2 μ := hf.sub hg
  have hsum : (fun y => g y + h y) = f := by ext y; dsimp [h]; ring
  have hvar := variance_fun_add hg hh
  rw [hsum] at hvar
  have hplus := variance_nonneg (fun y => ε * g y + h y) μ
  have hminus := variance_nonneg (fun y => ε * g y - h y) μ
  rw [variance_fun_add (hg.const_mul ε) hh, variance_const_mul,
    covariance_const_mul_left] at hplus
  rw [variance_fun_sub (hg.const_mul ε) hh, variance_const_mul,
    covariance_const_mul_left] at hminus
  have hconvert : (ε ^ 2 * variance g μ + (1 + ε) * variance h μ) / ε =
      ε * variance g μ + ((1 + ε) / ε) * variance h μ := by field_simp
  have hbound : |variance f μ - variance g μ| ≤
      (ε ^ 2 * variance g μ + (1 + ε) * variance h μ) / ε := by
    have hscaled := congrArg (fun x : ℝ => ε * x) hvar
    apply abs_le.mpr
    constructor
    · rw [← neg_div]
      apply (div_le_iff₀ hε).mpr
      nlinarith only [hscaled, hplus, mul_nonneg hε.le (variance_nonneg h μ)]
    · apply (le_div_iff₀ hε).mpr
      nlinarith only [hscaled, hminus]
  rw [hconvert] at hbound
  exact hbound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (variance_le_expectation_sq hh.aestronglyMeasurable) (by positivity)))

end Comparison

section VarianceReduction

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def quadraticErrorDifferenceEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ) : ℝ :=
  ∫ batches, (empiricalMarginalError data m R batches -
    categoricalQuadraticError data gStar m R batches) ^ 2 ∂repetitionMeasure data m R

theorem varianceError_comparison (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    |data.varianceError m R -
      variance (categoricalQuadraticError data gStar m R) (repetitionMeasure data m R)| ≤
        ε * variance (categoricalQuadraticError data gStar m R) (repetitionMeasure data m R) +
          ((1 + ε) / ε) * quadraticErrorDifferenceEnergy data gStar m R :=
  variance_difference_young_bound (memLp_empiricalMarginalError data hexact hm R)
    (memLp_categoricalQuadraticError data gStar hm hR) hε

end VarianceReduction

end DualGuided2026
