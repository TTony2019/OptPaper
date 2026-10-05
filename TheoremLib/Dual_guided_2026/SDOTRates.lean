import TheoremLib.Dual_guided_2026.SDOT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rates for shrinking potential balls and finite grids

The powers below make both the Taylor remainder and the grid remainder
negligible, while localization has an exponential tail in a positive power
of the sample size.
-/

namespace DualGuided2026

open Filter
open scoped Topology

noncomputable def powerRadius (α : ℝ) (m : ℕ) : ℝ := (m : ℝ) ^ (-α)

noncomputable def localizationExponent (n : ℕ) : ℝ := 1 / 2 - 1 / (8 * ((n : ℝ) + 1))

noncomputable def gridExponent (n : ℕ) : ℝ := 1 / 2 + 1 / (8 * ((n : ℝ) + 1))

theorem localizationExponent_bounds (n : ℕ) :
    1 / 4 < localizationExponent n ∧ localizationExponent n < 1 / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hden : (0 : ℝ) < 8 * ((n : ℝ) + 1) := by positivity
  have hinv : 0 < 1 / (8 * ((n : ℝ) + 1)) := one_div_pos.mpr hden
  have hinvle : 1 / (8 * ((n : ℝ) + 1)) ≤ (1 : ℝ) / 8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  unfold localizationExponent
  constructor <;> linarith

theorem gridExponent_lower_bound (n : ℕ) : 1 / 2 < gridExponent n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold gridExponent
  have hpos : 0 < 1 / (8 * ((n : ℝ) + 1)) := by positivity
  linarith

theorem gridExponent_gap_condition (n : ℕ) :
    (n : ℝ) * (gridExponent n - localizationExponent n) < localizationExponent n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold gridExponent localizationExponent
  have hpos : 0 < 1 / (8 * ((n : ℝ) + 1)) := by positivity
  have heq : (1 / (8 * ((n : ℝ) + 1))) * (8 * ((n : ℝ) + 1)) = 1 :=
    one_div_mul_cancel (by positivity)
  nlinarith

theorem powerRadius_pos {m : ℕ} (hm : 0 < m) (α : ℝ) : 0 < powerRadius α m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem powerRadius_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (powerRadius α) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop

theorem powerRadius_antitone_exponent {m : ℕ} (hm : 1 ≤ m) {α β : ℝ} (hαβ : α ≤ β) :
    powerRadius β m ≤ powerRadius α m :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (neg_le_neg hαβ)

theorem gridRadius_le_localizationRadius (n : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    powerRadius (gridExponent n) m ≤ powerRadius (localizationExponent n) m :=
  powerRadius_antitone_exponent hm (by
    linarith [(localizationExponent_bounds n).2, gridExponent_lower_bound n])

theorem nat_mul_powerRadius_pow_eq {m : ℕ} (hm : 0 < m) (α : ℝ) (k : ℕ) :
    (m : ℝ) * powerRadius α m ^ k = (m : ℝ) ^ (1 - (k : ℝ) * α) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  unfold powerRadius
  rw [← Real.rpow_mul_natCast hmreal.le (-α) k]
  calc
    (m : ℝ) * (m : ℝ) ^ (-α * (k : ℝ)) =
        (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (-α * (k : ℝ)) := by rw [Real.rpow_one]
    _ = (m : ℝ) ^ (1 - (k : ℝ) * α) := by
      rw [← Real.rpow_add hmreal]
      congr 1
      ring

theorem nat_mul_powerRadius_pow_tendsto_zero (α : ℝ) (k : ℕ)
    (hα : 1 < (k : ℝ) * α) :
    Tendsto (fun m : ℕ => (m : ℝ) * powerRadius α m ^ k) atTop (𝓝 0) := by
  have hexp : 0 < (k : ℝ) * α - 1 := by linarith
  have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 - (k : ℝ) * α)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  rw [nat_mul_powerRadius_pow_eq hm]

theorem localizationRadius_quartic_rate (n : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) * powerRadius (localizationExponent n) m ^ 4)
      atTop (𝓝 0) :=
  nat_mul_powerRadius_pow_tendsto_zero _ 4 (by
    have h := (localizationExponent_bounds n).1
    norm_num
    linarith)

theorem gridRadius_quadratic_rate (n : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) * powerRadius (gridExponent n) m ^ 2)
      atTop (𝓝 0) :=
  nat_mul_powerRadius_pow_tendsto_zero _ 2 (by
    have h := gridExponent_lower_bound n
    norm_num
    linarith)

theorem powerRadius_div_eq {m : ℕ} (hm : 0 < m) (α β : ℝ) :
    powerRadius α m / powerRadius β m = (m : ℝ) ^ (β - α) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  unfold powerRadius
  rw [← Real.rpow_sub hmreal]
  congr 1
  ring

theorem grid_radius_rate {α β : ℝ} (n : ℕ) (hgap : α ≤ β)
    (hexp : (n : ℝ) * (β - α) < α) :
    Tendsto (fun m : ℕ => (2 * powerRadius α m / powerRadius β m + 4) ^ n *
      powerRadius α m) atTop (𝓝 0) := by
  let e := α - (n : ℝ) * (β - α)
  have he : 0 < e := sub_pos.mpr hexp
  have hlim : Tendsto (fun m : ℕ => (6 : ℝ) ^ n * (m : ℝ) ^ (-e)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop).const_mul ((6 : ℝ) ^ n)
  apply squeeze_zero' (Eventually.of_forall fun m => by
    unfold powerRadius
    positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let q := (m : ℝ) ^ (β - α)
  have hq : 1 ≤ q := Real.one_le_rpow hmone (sub_nonneg.mpr hgap)
  have hr : 0 ≤ powerRadius α m := (powerRadius_pos hmpos α).le
  have hratio : 2 * powerRadius α m / powerRadius β m = 2 * q := by
    rw [mul_div_assoc, powerRadius_div_eq hmpos]
  rw [hratio]
  calc
    (2 * q + 4) ^ n * powerRadius α m ≤ (6 * q) ^ n * powerRadius α m := by
      apply mul_le_mul_of_nonneg_right _ hr
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    _ = (6 : ℝ) ^ n * (m : ℝ) ^ (-e) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hmreal.le (β - α) n]
      unfold powerRadius
      rw [mul_assoc, ← Real.rpow_add hmreal]
      congr 1
      congr 1
      dsimp [e]
      ring

theorem localization_grid_radius_rate (n : ℕ) :
    Tendsto (fun m : ℕ =>
      (2 * powerRadius (localizationExponent n) m / powerRadius (gridExponent n) m + 4) ^ n *
        powerRadius (localizationExponent n) m) atTop (𝓝 0) :=
  grid_radius_rate n (by
    linarith [(localizationExponent_bounds n).2, gridExponent_lower_bound n])
    (gridExponent_gap_condition n)

theorem nat_rpow_mul_exp_neg_rpow_tendsto_zero (k κ γ : ℝ) (hκ : 0 < κ) (hγ : 0 < γ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k * Real.exp (-κ * (m : ℝ) ^ γ)) atTop (𝓝 0) := by
  have hgrowth : Tendsto (fun m : ℕ => (m : ℝ) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / γ) κ hκ).comp hgrowth
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hmreal.le]
  congr 2
  field_simp [hγ.ne']

/-- The localization tail remains negligible after any polynomial scaling
and the finite-net cardinality factor. The net and exponential constants
are independent. -/
theorem localization_tail_rate_general (n : ℕ) (k A c α : ℝ) (hA : 0 ≤ A) (hc : 0 < c)
    (hα : 0 ≤ α) (hαhalf : α < 1 / 2) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k *
      (A / powerRadius α m + 2) ^ n *
        Real.exp (-c * (m : ℝ) * powerRadius α m ^ 2)) atTop (𝓝 0) := by
  let C := A + 2
  let γ := 1 - 2 * α
  have hC : 0 < C := by dsimp [C]; positivity
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hlim : Tendsto (fun m : ℕ => C ^ n * (m : ℝ) ^ (k + α * (n : ℝ)) *
      Real.exp (-c * (m : ℝ) ^ γ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using
      (nat_rpow_mul_exp_neg_rpow_tendsto_zero (k + α * (n : ℝ)) c γ hc hγ).const_mul (C ^ n)
  apply squeeze_zero' (Eventually.of_forall fun m => by
    unfold powerRadius
    positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : (1 : ℝ) ≤ (m : ℝ) ^ α := Real.one_le_rpow hmone hα
  have hr : 0 < powerRadius α m := powerRadius_pos hmpos α
  have hratio : A / powerRadius α m = A * (m : ℝ) ^ α := by
    unfold powerRadius
    rw [Real.rpow_neg hmreal.le]
    simp only [div_inv_eq_mul]
  have hnet : A / powerRadius α m + 2 ≤ C * (m : ℝ) ^ α := by
    rw [hratio]
    dsimp [C]
    nlinarith
  have hscaled : (m : ℝ) ^ k * (A / powerRadius α m + 2) ^ n ≤
      C ^ n * (m : ℝ) ^ (k + α * (n : ℝ)) := by
    calc
      (m : ℝ) ^ k * (A / powerRadius α m + 2) ^ n ≤
          (m : ℝ) ^ k * (C * (m : ℝ) ^ α) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hmreal.le _)
        exact pow_le_pow_left₀ (by positivity) hnet n
      _ = C ^ n * (m : ℝ) ^ (k + α * (n : ℝ)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hmreal.le α n, Real.rpow_add hmreal]
        ring
  have hexp : -c * (m : ℝ) * powerRadius α m ^ 2 = -c * (m : ℝ) ^ γ := by
    rw [mul_assoc, nat_mul_powerRadius_pow_eq hmpos α 2]
    rfl
  rw [hexp]
  exact mul_le_mul_of_nonneg_right hscaled (Real.exp_pos _).le

theorem localization_tail_rate (n : ℕ) (k κ α : ℝ) (hκ : 0 < κ)
    (hα : 0 ≤ α) (hαhalf : α < 1 / 2) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k *
      (2 / (κ * powerRadius α m) + 2) ^ n *
        Real.exp (-κ * (m : ℝ) * powerRadius α m ^ 2)) atTop (𝓝 0) := by
  simpa only [div_mul_eq_div_div] using
    localization_tail_rate_general n k (2 / κ) κ α (by positivity) hκ hα hαhalf

theorem localization_exponential_tail_rate (n : ℕ) (k κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k *
      (2 / (κ * powerRadius (localizationExponent n) m) + 2) ^ n *
        Real.exp (-κ * (m : ℝ) * powerRadius (localizationExponent n) m ^ 2))
      atTop (𝓝 0) :=
  localization_tail_rate n k κ _ hκ (by linarith [(localizationExponent_bounds n).1])
    (localizationExponent_bounds n).2

theorem localization_exponential_tail_rate_general (n : ℕ) (k A c : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k *
      (A / powerRadius (localizationExponent n) m + 2) ^ n *
        Real.exp (-c * (m : ℝ) * powerRadius (localizationExponent n) m ^ 2))
      atTop (𝓝 0) :=
  localization_tail_rate_general n k A c _ hA hc
    (by linarith [(localizationExponent_bounds n).1]) (localizationExponent_bounds n).2

theorem uniformLittleO_of_eventually_scaled_bound (rmax k : ℕ) (f : ℕ → ℕ → ℝ)
    (b : ℕ → ℝ) (hf : ∀ m R, 0 ≤ f m R)
    (hbound : ∀ᶠ m : ℕ in atTop, ∀ R : ℕ, 1 ≤ R → R ≤ rmax →
      (m : ℝ) ^ k * f m R ≤ b m)
    (hb : Tendsto b atTop (𝓝 0)) :
    IsUniformLittleOInM rmax f (fun m => 1 / (m : ℝ) ^ k) := by
  intro δ hδ
  have hsmall : ∀ᶠ m in atTop, b m < δ :=
    (tendsto_order.1 hb).2 δ hδ
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hsmall.and hbound)
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hm)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hMm := hM m ((le_max_left M 1).trans hm)
  have hscaled := (hMm.2 R hR hRmax).trans hMm.1.le
  rw [abs_of_nonneg (hf m R), abs_of_nonneg (by positivity)]
  have hdiv : f m R ≤ δ / (m : ℝ) ^ k :=
    (le_div_iff₀ (pow_pos hmreal k)).2 (by simpa only [mul_comm] using hscaled)
  simpa only [div_eq_mul_inv, one_mul] using hdiv

theorem uniformLittleO_of_scaled_bound (rmax k : ℕ) (f : ℕ → ℕ → ℝ)
    (b : ℕ → ℝ) (hf : ∀ m R, 0 ≤ f m R)
    (hbound : ∀ {m : ℕ}, 0 < m → ∀ R : ℕ, 1 ≤ R → R ≤ rmax →
      (m : ℝ) ^ k * f m R ≤ b m)
    (hb : Tendsto b atTop (𝓝 0)) :
    IsUniformLittleOInM rmax f (fun m => 1 / (m : ℝ) ^ k) := by
  intro δ hδ
  have hsmall : ∀ᶠ m in atTop, b m < δ :=
    (tendsto_order.1 hb).2 δ hδ
  obtain ⟨M, hM⟩ := eventually_atTop.1 hsmall
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hm)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hscaled := (hbound hmpos R hR hRmax).trans
    (hM m ((le_max_left M 1).trans hm)).le
  rw [abs_of_nonneg (hf m R), abs_of_nonneg (by positivity)]
  have hdiv : f m R ≤ δ / (m : ℝ) ^ k :=
    (le_div_iff₀ (pow_pos hmreal k)).2 (by simpa only [mul_comm] using hscaled)
  simpa only [div_eq_mul_inv, one_mul] using hdiv

end DualGuided2026
