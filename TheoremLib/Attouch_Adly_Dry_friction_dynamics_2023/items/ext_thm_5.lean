import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_2
import Foundation.Analysis.ExtendedRealFunctions

namespace AttouchAdlyDryFrictionDynamics2023

private theorem rayleigh_coercive_of_posdef {n : ℕ} (hn : n ≠ 0)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m * ‖x‖ ^ 2 ≤ inner ℝ (A x) x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_iff_ne_zero.mpr hn)
  letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) (show 0 ≤ (1 : ℝ) by norm_num)
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hsphere
      A.reApplyInnerSelf_continuous.continuousOn
  refine ⟨inner ℝ (A u) u, ?_, ?_⟩
  · exact hpos u (by
      intro huz
      have : ‖u‖ = 0 := by simp [huz]
      linarith [mem_sphere_zero_iff_norm.mp hu])
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · let w : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x
      have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hwnorm : ‖w‖ = 1 := by
        rw [show w = ‖x‖⁻¹ • x by rfl, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (le_of_lt hxnorm))]
        exact inv_mul_cancel₀ (ne_of_gt hxnorm)
      have hw : w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        mem_sphere_zero_iff_norm.mpr hwnorm
      have hquad : inner ℝ (A u) u ≤ inner ℝ (A w) w := by
        simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hmin hw
      have hxrep : ‖x‖ • w = x := by
        dsimp [w]
        rw [smul_smul]
        rw [mul_inv_cancel₀ (ne_of_gt hxnorm)]
        exact one_smul ℝ x
      have hscale : inner ℝ (A (‖x‖ • w)) (‖x‖ • w) =
          ‖x‖ ^ 2 * inner ℝ (A w) w := by
        simpa [ContinuousLinearMap.reApplyInnerSelf_apply, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x)] using A.reApplyInnerSelf_smul w (c := ‖x‖)
      calc
        inner ℝ (A u) u * ‖x‖ ^ 2 ≤ inner ℝ (A w) w * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hquad (sq_nonneg ‖x‖)
        _ = inner ℝ (A x) x := by
          calc
            inner ℝ (A w) w * ‖x‖ ^ 2 = ‖x‖ ^ 2 * inner ℝ (A w) w := by ring
            _ = inner ℝ (A (‖x‖ • w)) (‖x‖ • w) := hscale.symm
            _ = inner ℝ (A x) x := by rw [hxrep]

/-- A local quadratic lower bound for a convex extended-real function propagates
to a linear lower bound along every ray. -/
private theorem convex_ray_lower_bound {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hconvex : Convex ℝ (ERealFunction.epigraph f))
    (hnot_bot : ∀ x, f x ≠ ⊥) (hf0 : f 0 = 0)
    {R ρ c : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hlocal : ∀ z, z ≠ 0 → ‖z‖ < R →
      ((c * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z) :
    ∀ x, ρ ≤ ‖x‖ → ((c * ρ * ‖x‖ : ℝ) : EReal) ≤ f x := by
  intro x hx
  by_cases htop : f x = ⊤
  · simp [htop]
  have hnx : x ≠ 0 := by
    intro hx0
    subst x
    have : ρ ≤ 0 := by simpa using hx
    linarith
  have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hnx
  let t : ℝ := ρ / ‖x‖
  have ht_pos : 0 < t := div_pos hρ hnorm_pos
  have ht_le : t ≤ 1 := (div_le_one₀ hnorm_pos).mpr hx
  have ht_nonneg : 0 ≤ t := ht_pos.le
  let u : EuclideanSpace ℝ (Fin n) := t • x
  have hu_norm : ‖u‖ = ρ := by
    rw [show u = t • x by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht_nonneg]
    exact div_mul_cancel₀ ρ hnorm_pos.ne'
  have hu_ne : u ≠ 0 := by
    intro hu
    have : ‖u‖ = 0 := by simp [hu]
    linarith [hu_norm, hρ]
  have hu_local : ((c * ‖u‖ ^ 2 : ℝ) : EReal) ≤ f u :=
    hlocal u hu_ne (by rw [hu_norm]; exact hρR)
  have hzero_epi : ((0, (0 : ℝ)) : EuclideanSpace ℝ (Fin n) × ℝ) ∈
      ERealFunction.epigraph f := by
    rw [ERealFunction.mem_epigraph_iff]
    simp [hf0]
  have hx_epi : (x, (f x).toReal) ∈ ERealFunction.epigraph f := by
    rw [ERealFunction.mem_epigraph_iff]
    exact EReal.le_coe_toReal htop
  have hcombo := (convex_iff_add_mem.mp hconvex) hzero_epi hx_epi
    (sub_nonneg.mpr ht_le) ht_nonneg (by ring)
  have hu_epi : (u, t * (f x).toReal) ∈ ERealFunction.epigraph f := by
    convert hcombo using 1
    all_goals simp [u, t]
  have hu_le : f u ≤ ((t * (f x).toReal : ℝ) : EReal) :=
    hu_epi
  have hreal : c * ρ ^ 2 ≤ t * (f x).toReal := by
    rw [hu_norm] at hu_local
    rw [← EReal.coe_toReal htop (hnot_bot x)] at hu_le
    exact_mod_cast hu_local.trans hu_le
  have hdiv : c * ρ * ‖x‖ ≤ (f x).toReal := by
    apply le_of_mul_le_mul_right _ ht_pos
    calc
      (c * ρ * ‖x‖) * t = c * ρ ^ 2 := by
        dsimp [t]
        field_simp
      _ ≤ (f x).toReal * t := by simpa [mul_comm] using hreal
  rw [← EReal.coe_toReal htop (hnot_bot x)]
  exact_mod_cast hdiv

/-- Converts a local real quadratic estimate into the extended-real coercive
bound used by the ray argument. -/
private theorem local_quadratic_coercive_lower {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hnot_bot : ∀ x, f x ≠ ⊥) {m η R : ℝ}
    (hm : ∀ x, m * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (hη : 0 < η)
    (hloc : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ‖x‖ < R →
      f x ≠ ⊤ ∧ inner ℝ (A x) x / 2 - η * ‖x‖ ^ 2 < (f x).toReal) :
    ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖z‖ < R →
      (((m / 2 - η) * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z := by
  intro z hz hzr
  rcases hloc z hz hzr with ⟨hztop, hlower⟩
  have hquad : (m / 2 - η) * ‖z‖ ^ 2 ≤ inner ℝ (A z) z / 2 - η * ‖z‖ ^ 2 := by
    exact if h : 0 < η then
      by nlinarith [hm z]
    else
      (h hη).elim
  have hreal : (m / 2 - η) * ‖z‖ ^ 2 ≤ (f z).toReal :=
    hquad.trans (le_of_lt hlower)
  rw [← EReal.coe_toReal hztop (hnot_bot z)]
  exact_mod_cast hreal

/-- The local upper quadratic estimate and lower semicontinuity fix the
normalization from above.  The converse inequality is the separate convex
midpoint part of the Gorni argument. -/
private theorem value_zero_le_of_local_quadratic {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hlsc : LowerSemicontinuous f) (hnot_bot : ∀ x, f x ≠ ⊥)
    (hfinite : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin n)), f x ≠ ⊤)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0)
    (hloc : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 < R ∧ ∀ x,
      x ≠ 0 → ‖x‖ < R → f x ≠ ⊤ ∧
        (f x).toReal < inner ℝ (A x) x / 2 + η * ‖x‖ ^ 2) :
    f 0 ≤ 0 := by
  have hf0top : f 0 ≠ ⊤ := mem_of_mem_nhds hfinite
  have hf0bot : f 0 ≠ ⊥ := hnot_bot 0
  have hf0real : f 0 = ((f 0).toReal : EReal) :=
    (EReal.coe_toReal hf0top hf0bot).symm
  by_contra hle
  have hb : 0 < (f 0).toReal := by
    by_contra hb
    have : f 0 ≤ 0 := by
      rw [hf0real]
      exact_mod_cast (le_of_not_gt hb)
    exact hle this
  let b : ℝ := (f 0).toReal / 2
  have hbpos : 0 < b := by dsimp [b]; linarith
  have hbelow : (b : EReal) < f 0 := by
    rw [hf0real]
    exact_mod_cast (show b < (f 0).toReal by dsimp [b]; linarith)
  have hnear : ∀ᶠ z in nhds (0 : EuclideanSpace ℝ (Fin n)), (b : EReal) < f z :=
    hlsc.lowerSemicontinuousAt 0 b hbelow
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨R, hRpos, hR⟩ := hloc 1 (by norm_num)
  let q : ℝ := inner ℝ (A u) u / 2
  let C : ℝ := |q| + ‖u‖ ^ 2
  have hCpos : 0 < C := by
    dsimp [C]
    have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  let t : ℝ := min (δ / (2 * ‖u‖)) (min (R / (2 * ‖u‖))
    (Real.sqrt (b / (2 * C))))
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htδ : t * ‖u‖ < δ := by
    have ht : t ≤ δ / (2 * ‖u‖) := by dsimp [t]; exact min_le_left _ _
    have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmul := mul_le_mul_of_nonneg_right ht hu_norm.le
    have hhalf : t * ‖u‖ ≤ δ / 2 := by
      calc
        t * ‖u‖ ≤ (δ / (2 * ‖u‖)) * ‖u‖ := hmul
        _ = δ / 2 := by field_simp
    linarith
  have htR : t * ‖u‖ < R := by
    have ht : t ≤ R / (2 * ‖u‖) := by
      dsimp [t]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmul := mul_le_mul_of_nonneg_right ht hu_norm.le
    have hhalf : t * ‖u‖ ≤ R / 2 := by
      calc
        t * ‖u‖ ≤ (R / (2 * ‖u‖)) * ‖u‖ := hmul
        _ = R / 2 := by field_simp
    linarith
  let x : EuclideanSpace ℝ (Fin n) := t • u
  have hxne : x ≠ 0 := by
    dsimp [x]
    exact smul_ne_zero htpos.ne' hu
  have hxnorm : ‖x‖ = t * ‖u‖ := by
    rw [show x = t • u by rfl, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hxδ : x ∈ Metric.ball 0 δ := by
    simpa [mem_ball_zero_iff, hxnorm] using htδ
  have hxR : ‖x‖ < R := by simpa [hxnorm] using htR
  have hupper := (hR x hxne hxR).2
  have hq : inner ℝ (A x) x / 2 = t ^ 2 * q := by
    dsimp [x, q]
    have hscale := A.reApplyInnerSelf_smul u (c := t)
    rw [Real.norm_eq_abs, abs_of_pos htpos] at hscale
    have hscale' : inner ℝ (A (t • u)) (t • u) =
        t ^ 2 * inner ℝ (A u) u := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hscale
    rw [hscale']
    ring
  have ht_sq : t ^ 2 ≤ b / (2 * C) := by
    have ht : t ≤ Real.sqrt (b / (2 * C)) := by
      dsimp [t]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hsqrt : 0 ≤ Real.sqrt (b / (2 * C)) := Real.sqrt_nonneg _
    have hratio : 0 ≤ b / (2 * C) := le_of_lt (div_pos hbpos (by positivity))
    nlinarith [Real.sq_sqrt hratio]
  have hsmall : inner ℝ (A x) x / 2 + ‖x‖ ^ 2 < b := by
    rw [hq, hxnorm]
    have hqle : q ≤ |q| := le_abs_self q
    have hbound : t ^ 2 * (|q| + ‖u‖ ^ 2) ≤ b / 2 := by
      calc
        t ^ 2 * (|q| + ‖u‖ ^ 2) ≤ (b / (2 * C)) * C :=
          mul_le_mul_of_nonneg_right ht_sq (le_of_lt hCpos)
        _ = b / 2 := by dsimp [C]; field_simp
    nlinarith [sq_nonneg t]
  have hreal_lt : (f x).toReal < b := by
    have hupper' : (f x).toReal < inner ℝ (A x) x / 2 + ‖x‖ ^ 2 := by
      simpa only [one_mul] using hupper
    exact lt_of_lt_of_le hupper' (le_of_lt hsmall)
  have hcast_lt : (f x : EReal) < (b : EReal) := by
    rw [← EReal.coe_toReal (hR x hxne hxR).1 (hnot_bot x)]
    exact_mod_cast hreal_lt
  exact (not_lt_of_ge (le_of_lt (hδball hxδ))) hcast_lt

/-- Convexity and a two-sided quadratic estimate force the value at the
origin to be nonnegative. -/
private theorem value_zero_ge_of_local_quadratic {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f))
    (hnot_bot : ∀ x, f x ≠ ⊥)
    (hfinite : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin n)), f x ≠ ⊤)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0)
    (hloc : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 < R ∧ ∀ x,
      x ≠ 0 → ‖x‖ < R → f x ≠ ⊤ ∧
        inner ℝ (A x) x / 2 - η * ‖x‖ ^ 2 < (f x).toReal ∧
        (f x).toReal < inner ℝ (A x) x / 2 + η * ‖x‖ ^ 2) :
    0 ≤ f 0 := by
  have hf0top : f 0 ≠ ⊤ := mem_of_mem_nhds hfinite
  have hf0bot : f 0 ≠ ⊥ := hnot_bot 0
  have hf0real : f 0 = ((f 0).toReal : EReal) :=
    (EReal.coe_toReal hf0top hf0bot).symm
  rw [hf0real]
  exact_mod_cast (by
    by_contra hnonneg
    have hneg : (f 0).toReal < 0 := lt_of_not_ge hnonneg
    let b : ℝ := -(f 0).toReal
    have hb : 0 < b := by dsimp [b]; linarith
    obtain ⟨R, hRpos, hR⟩ := hloc 1 (by norm_num)
    let q : ℝ := inner ℝ (A u) u / 2
    let C : ℝ := 2 * |q| + 6 * ‖u‖ ^ 2
    have hC : 0 < C := by
      dsimp [C]
      have : 0 < ‖u‖ := norm_pos_iff.mpr hu
      positivity
    let t : ℝ := min (R / (4 * ‖u‖)) (Real.sqrt (b / (2 * C)))
    have ht : 0 < t := by
      dsimp [t]
      positivity
    let x : EuclideanSpace ℝ (Fin n) := t • u
    have hxne : x ≠ 0 := by
      dsimp [x]
      exact smul_ne_zero ht.ne' hu
    have h2xne : (2 : ℝ) • x ≠ 0 := smul_ne_zero (by norm_num) hxne
    have hxnorm : ‖x‖ = t * ‖u‖ := by
      rw [show x = t • u by rfl, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have htR : 2 * t * ‖u‖ < R := by
      have htle : t ≤ R / (4 * ‖u‖) := by
        dsimp [t]
        exact min_le_left _ _
      have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hmul := mul_le_mul_of_nonneg_right htle hunorm.le
      have hhalf : t * ‖u‖ ≤ R / 4 := by
        calc
          t * ‖u‖ ≤ (R / (4 * ‖u‖)) * ‖u‖ := hmul
          _ = R / 4 := by field_simp
      linarith
    have h2xR : ‖(2 : ℝ) • x‖ < R := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num), hxnorm]
      simpa [mul_assoc] using htR
    have hxR : ‖x‖ < R := by
      rw [hxnorm]
      linarith [htR]
    have hqx : inner ℝ (A x) x / 2 = t ^ 2 * q := by
      dsimp [x, q]
      have hs := A.reApplyInnerSelf_smul u (c := t)
      rw [Real.norm_eq_abs, abs_of_pos ht] at hs
      have hs' : inner ℝ (A (t • u)) (t • u) =
          t ^ 2 * inner ℝ (A u) u := by
        simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hs
      rw [hs']
      ring
    have hq2x : inner ℝ (A ((2 : ℝ) • x)) ((2 : ℝ) • x) / 2 =
        4 * (inner ℝ (A x) x / 2) := by
      have hs := A.reApplyInnerSelf_smul x (c := (2 : ℝ))
      norm_num [ContinuousLinearMap.reApplyInnerSelf_apply] at hs ⊢
      linarith
    have hn2x : ‖(2 : ℝ) • x‖ ^ 2 = 4 * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      ring
    have h0epi : (0, (f 0).toReal) ∈ ERealFunction.epigraph f := by
      rw [ERealFunction.mem_epigraph_iff]
      exact le_of_eq hf0real
    have h2epi : ((2 : ℝ) • x, (f ((2 : ℝ) • x)).toReal) ∈ ERealFunction.epigraph f := by
      rw [ERealFunction.mem_epigraph_iff]
      exact EReal.le_coe_toReal (hR _ h2xne h2xR).1
    have hmid := (convex_iff_add_mem.mp hconvex) h0epi h2epi
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmidepi : (x, ((f 0).toReal + (f ((2 : ℝ) • x)).toReal) / 2) ∈
        ERealFunction.epigraph f := by
      convert hmid using 1
      all_goals simp [x]
      all_goals ring
    have hmidreal : (f x).toReal ≤ ((f 0).toReal + (f ((2 : ℝ) • x)).toReal) / 2 := by
      rw [ERealFunction.mem_epigraph_iff] at hmidepi
      rw [← EReal.coe_toReal (hR x hxne hxR).1 (hnot_bot x)] at hmidepi
      exact_mod_cast hmidepi
    have hlower := (hR x hxne hxR).2.1
    have hupper := (hR ((2 : ℝ) • x) h2xne h2xR).2.2
    have hmain : b < 2 * (inner ℝ (A x) x / 2) + 6 * ‖x‖ ^ 2 := by
      dsimp [b] at *
      rw [hq2x, hn2x] at hupper
      nlinarith
    have ht_sq : t ^ 2 ≤ b / (2 * C) := by
      have htle : t ≤ Real.sqrt (b / (2 * C)) := by
        dsimp [t]
        exact min_le_right _ _
      have hratio : 0 ≤ b / (2 * C) := le_of_lt (div_pos hb (by positivity))
      nlinarith [Real.sq_sqrt hratio, Real.sqrt_nonneg (b / (2 * C))]
    have hbound : 2 * (inner ℝ (A x) x / 2) + 6 * ‖x‖ ^ 2 ≤ b / 2 := by
      rw [hqx, hxnorm]
      have hqle : q ≤ |q| := le_abs_self q
      have hmul : t ^ 2 * C ≤ b / 2 := by
        calc
          t ^ 2 * C ≤ (b / (2 * C)) * C :=
            mul_le_mul_of_nonneg_right ht_sq hC.le
          _ = b / 2 := by field_simp
      nlinarith [sq_nonneg t]
    linarith)

private theorem quadratic_completion_with_inverse {n : ℕ}
    (A Ainv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : A.IsSymmetric)
    (hright : A.comp Ainv = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y x - inner ℝ (A x) x / 2 =
      inner ℝ (Ainv y) y / 2 - inner ℝ (A (x - Ainv y)) (x - Ainv y) / 2 := by
  have hy : A (Ainv y) = y := by
    simpa using congrArg (fun L => L y) hright
  have hcross : inner ℝ (A (Ainv y)) x = inner ℝ (A x) (Ainv y) := by
    calc
      inner ℝ (A (Ainv y)) x = inner ℝ (Ainv y) (A x) := by
        simpa using hsymm.apply_clm (Ainv y) x
      _ = inner ℝ (A x) (Ainv y) := real_inner_comm _ _
  have hquad : inner ℝ (Ainv y) y = inner ℝ (A (Ainv y)) (Ainv y) := by
    rw [hy]
    exact real_inner_comm _ _
  have hinner : inner ℝ y x = inner ℝ (A x) (Ainv y) := by
    calc
      inner ℝ y x = inner ℝ (A (Ainv y)) x := by rw [hy]
      _ = inner ℝ (A x) (Ainv y) := hcross
  rw [hinner, hquad]
  rw [A.map_sub]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [hcross]
  ring

private theorem sq_norm_sub_le_two_sq {n : ℕ}
    (x z : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 ≤ 2 * ‖x - z‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
  have hnorm : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
    calc
      ‖x‖ = ‖(x - z) + z‖ := by
        congr 1
        abel
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le (x - z) z
  have hright : 0 ≤ ‖x - z‖ + ‖z‖ := by positivity
  have hsquare : ‖x‖ ^ 2 ≤ (‖x - z‖ + ‖z‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hright).mpr hnorm
  nlinarith [sq_nonneg (‖x - z‖ - ‖z‖)]

private theorem local_supremand_upper_real {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (A Ainv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : A.IsSymmetric)
    (hright : A.comp Ainv = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    {m η M : ℝ} (hη : 0 ≤ η)
    (hm : ∀ z : EuclideanSpace ℝ (Fin n), m * ‖z‖ ^ 2 ≤ inner ℝ (A z) z)
    (hηm : 2 * η ≤ m / 2)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hAnorm : ‖Ainv y‖ ^ 2 ≤ M ^ 2 * ‖y‖ ^ 2)
    (hlower : inner ℝ (A x) x / 2 - η * ‖x‖ ^ 2 < (f x).toReal) :
    inner ℝ y x - (f x).toReal ≤
      inner ℝ (Ainv y) y / 2 + 2 * η * M ^ 2 * ‖y‖ ^ 2 := by
  have hcomp := quadratic_completion_with_inverse A Ainv hsymm hright x y
  have hcoercive : m / 2 * ‖x - Ainv y‖ ^ 2 ≤
      inner ℝ (A (x - Ainv y)) (x - Ainv y) / 2 := by
    nlinarith only [hm (x - Ainv y)]
  have hnorm := sq_norm_sub_le_two_sq x (Ainv y)
  have herror : η * ‖x‖ ^ 2 ≤
      2 * η * ‖x - Ainv y‖ ^ 2 + 2 * η * M ^ 2 * ‖y‖ ^ 2 := by
    calc
      η * ‖x‖ ^ 2 ≤ η * (2 * ‖x - Ainv y‖ ^ 2 + 2 * ‖Ainv y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm hη
      _ = 2 * η * ‖x - Ainv y‖ ^ 2 + 2 * η * ‖Ainv y‖ ^ 2 := by ring
      _ ≤ 2 * η * ‖x - Ainv y‖ ^ 2 + 2 * η * M ^ 2 * ‖y‖ ^ 2 := by
        have hmult : 2 * η * ‖Ainv y‖ ^ 2 ≤ 2 * η * (M ^ 2 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hAnorm (by positivity)
        linarith only [hmult]
  have hcancel : 2 * η * ‖x - Ainv y‖ ^ 2 ≤
      inner ℝ (A (x - Ainv y)) (x - Ainv y) / 2 := by
    calc
      2 * η * ‖x - Ainv y‖ ^ 2 ≤ (m / 2) * ‖x - Ainv y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hηm (sq_nonneg _)
      _ ≤ inner ℝ (A (x - Ainv y)) (x - Ainv y) / 2 := hcoercive
  have hstrict : inner ℝ y x - (f x).toReal <
      inner ℝ (Ainv y) y / 2 + 2 * η * M ^ 2 * ‖y‖ ^ 2 := by
    calc
      inner ℝ y x - (f x).toReal <
          inner ℝ y x - inner ℝ (A x) x / 2 + η * ‖x‖ ^ 2 := by
            linarith
      _ = inner ℝ (Ainv y) y / 2 -
          inner ℝ (A (x - Ainv y)) (x - Ainv y) / 2 + η * ‖x‖ ^ 2 := by
            rw [hcomp]
      _ ≤ inner ℝ (Ainv y) y / 2 + 2 * η * M ^ 2 * ‖y‖ ^ 2 := by
            linarith
  exact hstrict.le

private theorem outer_supremand_upper {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (x y : EuclideanSpace ℝ (Fin n)) {c q η M : ℝ}
    (hnot_bot : ∀ z, f z ≠ ⊥) (hxtop : f x ≠ ⊤)
    (hray : ((c * ‖x‖ : ℝ) : EReal) ≤ f x)
    (hc : 0 < c) (hyc : ‖y‖ < c / 2) (hq : 0 ≤ q) (hη : 0 ≤ η) :
    ((inner ℝ y x : ℝ) : EReal) - f x ≤
      ((q + 2 * η * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
  rw [← EReal.coe_toReal hxtop (hnot_bot x), ← EReal.coe_sub]
  apply EReal.coe_le_coe
  have hrreal : c * ‖x‖ ≤ (f x).toReal := by
    rw [← EReal.coe_toReal hxtop (hnot_bot x)] at hray
    exact_mod_cast hray
  have hinter : inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm _ _
  have hrest : 0 ≤ 2 * η * M ^ 2 * ‖y‖ ^ 2 := by positivity
  have hscale : (‖y‖ - c) * ‖x‖ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg x)
  have hdiff : inner ℝ y x - (f x).toReal ≤ (‖y‖ - c) * ‖x‖ := by
    nlinarith only [hinter, hrreal]
  exact (hdiff.trans hscale).trans (add_nonneg hq hrest)

private theorem real_lt_toReal_of_coe_lt {a : ℝ} {z : EReal}
    (h : (a : EReal) < z) (hz : z ≠ ⊤) : a < z.toReal := by
  apply lt_of_not_ge
  intro hza
  have hbot : z ≠ ⊥ := by
    intro hbot
    rw [hbot] at h
    exact (not_lt_bot) h
  have hzreal : z = (z.toReal : EReal) := (EReal.coe_toReal hz hbot).symm
  have hle : z ≤ (a : EReal) := by
    rw [hzreal]
    exact EReal.coe_le_coe hza
  exact (not_le_of_gt h) hle

private theorem toReal_le_real_of_le_coe {z : EReal} {a : ℝ}
    (h : z ≤ (a : EReal)) (hz : z ≠ ⊥) : z.toReal ≤ a := by
  have h' := EReal.toReal_le_toReal h hz (EReal.coe_ne_top _)
  simpa using h'

private theorem norm_sq_pos_of_ne_zero {n : ℕ}
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0) :
    (0 : ℝ) < ‖y‖ ^ 2 := by
  have hy_norm : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  exact sq_pos_of_pos hy_norm

private theorem quotient_abs_lt_of_ereal_bounds {z : EReal}
    {q η M s ε : ℝ}
    (hlower : ((q - η * M ^ 2 * s : ℝ) : EReal) < z)
    (hupper : z ≤ ((q + 2 * η * M ^ 2 * s : ℝ) : EReal))
    (hzbot : z ≠ ⊥) (hztop : z ≠ ⊤) (hs : 0 < s)
    (hε : 2 * η * M ^ 2 < ε) :
    |(z.toReal - q) / s| < ε := by
  have hlow_real : q - η * M ^ 2 * s < z.toReal :=
    real_lt_toReal_of_coe_lt hlower hztop
  have hupp_real : z.toReal ≤ q + 2 * η * M ^ 2 * s :=
    toReal_le_real_of_le_coe hupper hzbot
  apply abs_lt.mpr
  constructor
  · apply (lt_div_iff₀ hs).mpr
    have hsmall : η * M ^ 2 < ε := by nlinarith [hε]
    nlinarith
  · apply (div_lt_iff₀ hs).mpr
    nlinarith

/- EXTERNAL DEPENDENCY: Gorni conjugation and second-order expansion result
   Source: G. Gorni, Conjugation and second-order properties of convex functions, J. Math. Anal. Appl. 158 (1991) 293--315.
   Status: proof not available — provide referenced paper MD to fill.
   To resolve: place the referenced paper in todo/ and re-run the pipeline.
-/
set_option maxHeartbeats 800000 in
/-- Conjugation preserves the stated positive-definite second-order expansion. -/
theorem gorni_conjugation_second_order {n : ℕ}
    (f fstar : EuclideanSpace ℝ (Fin n) → EReal)
    (A Ainv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (hproper : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f)
    (hconjugate : fstar = ERealFunction.conjugate f)
    (hsymm : A.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x)
    (hAinv_right : A.comp Ainv = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (hAinv_left : Ainv.comp A = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (hfinite : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin n)), f x ≠ ⊤)
    (hexpansion : Filter.Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ((f x).toReal - inner ℝ (A x) x / 2) / ‖x‖ ^ 2)
      (nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) (nhds 0)) :
    Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) =>
      ((fstar y).toReal - inner ℝ (Ainv y) y / 2) / ‖y‖ ^ 2)
      (nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) (nhds 0) := by
  -- The source expansion is real-valued on a neighborhood of the origin.
  rcases hproper with ⟨hnot_bot, hdom⟩
  have hlocal_finite : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin n)),
      f x ≠ ⊤ := hfinite
  have hf_zero_ne_top : f 0 ≠ ⊤ :=
    mem_of_mem_nhds hlocal_finite
  have hf_zero_ne_bot : f 0 ≠ ⊥ := hnot_bot 0
  have hright_apply (y : EuclideanSpace ℝ (Fin n)) : A (Ainv y) = y := by
    simpa using congrArg (fun L => L y) hAinv_right
  have hleft_apply (x : EuclideanSpace ℝ (Fin n)) : Ainv (A x) = x := by
    simpa using congrArg (fun L => L x) hAinv_left
  -- The primal second-order hypothesis gives the quantitative estimate used in
  -- the Gorni ray-localization argument.
  have hlocal_remainder : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : EuclideanSpace ℝ (Fin n) in nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
        |((f x).toReal - inner ℝ (A x) x / 2) / ‖x‖ ^ 2| < ε := by
    intro ε hε
    have hmem : Set.Ioo (-ε) ε ∈ nhds (0 : ℝ) := by
      exact Ioo_mem_nhds (neg_lt_zero.mpr hε) hε
    filter_upwards [hexpansion.eventually hmem] with x hx
    exact abs_lt.mpr hx
  -- Package the punctured limit as explicit two-sided estimates on a ball.
  -- This is the real-valued input needed by the convex ray-localization step.
  have hlocal_quadratic_bounds : ∀ η : ℝ, 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ‖x‖ < r →
        f x ≠ ⊤ ∧
          inner ℝ (A x) x / 2 - η * ‖x‖ ^ 2 < (f x).toReal ∧
          (f x).toReal < inner ℝ (A x) x / 2 + η * ‖x‖ ^ 2 := by
    intro η hη
    have hfinite_within : ∀ᶠ x : EuclideanSpace ℝ (Fin n) in
        nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))), f x ≠ ⊤ :=
      hlocal_finite.filter_mono nhdsWithin_le_nhds
    have hboth := (hlocal_remainder η hη).and hfinite_within
    rw [eventually_nhdsWithin_iff] at hboth
    rcases (Metric.eventually_nhds_iff.1 hboth) with ⟨r, hr, hr_ball⟩
    refine ⟨r, hr, ?_⟩
    intro x hx0 hxr
    have hx := hr_ball (by simpa [dist_zero_right] using hxr) (by simpa using hx0)
    rcases abs_lt.mp hx.1 with ⟨hlo, hup⟩
    have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    constructor
    · exact hx.2
    constructor
    · have hlo' : -η * ‖x‖ ^ 2 < (f x).toReal - inner ℝ (A x) x / 2 :=
        (lt_div_iff₀ hsq).mp hlo
      linarith
    · have hup' : (f x).toReal - inner ℝ (A x) x / 2 < η * ‖x‖ ^ 2 :=
        (div_lt_iff₀ hsq).mp hup
      linarith
  by_cases hn : n = 0
  · subst n
    have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have hempty : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) = ∅ := by
      ext y
      simp [Subsingleton.elim y 0]
    rw [hempty]
    simpa only [nhdsWithin_empty] using
      (Filter.tendsto_bot : Filter.Tendsto
        (fun y : EuclideanSpace ℝ (Fin 0) =>
          ((fstar y).toReal - inner ℝ (Ainv y) y / 2) / ‖y‖ ^ 2) ⊥ (nhds 0))
  · have hcoercive := rayleigh_coercive_of_posdef hn A hpos
    rcases hcoercive with ⟨m, hm_pos, hm⟩
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_iff_ne_zero.mpr hn)
    letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
    obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
    let η : ℝ := m / 8
    have hη : 0 < η := by
      dsimp [η]
      positivity
    have hηm : 4 * η < m := by
      dsimp [η]
      linarith
    obtain ⟨R, hR_pos, hRlocal⟩ := hlocal_quadratic_bounds η hη
    have hlocal_coercive : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖z‖ < R →
        (((m / 2 - η) * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z := by
      apply local_quadratic_coercive_lower f A hnot_bot hm hη
      intro z hz hzr
      exact ⟨(hRlocal z hz hzr).1, (hRlocal z hz hzr).2.1⟩
    have hcoercive_const : 0 < m / 2 - η := by
      dsimp [η]
      linarith
    have hf_zero_le : f 0 ≤ 0 := by
      apply value_zero_le_of_local_quadratic f A hlsc hnot_bot hlocal_finite u hu
      intro ε hε
      obtain ⟨r, hr, hlocal⟩ := hlocal_quadratic_bounds ε hε
      refine ⟨r, hr, ?_⟩
      intro x hx hxr
      exact ⟨(hlocal x hx hxr).1, (hlocal x hx hxr).2.2⟩
    have hf_zero_ge : 0 ≤ f 0 := by
      exact value_zero_ge_of_local_quadratic f A hconvex hnot_bot hlocal_finite u hu
        hlocal_quadratic_bounds
    have hf0 : f 0 = 0 := le_antisymm hf_zero_le hf_zero_ge
    let ρ : ℝ := R / 2
    have hρ : 0 < ρ := by
      dsimp [ρ]
      linarith
    have hρR : ρ < R := by
      dsimp [ρ]
      linarith
    have hray : ∀ x : EuclideanSpace ℝ (Fin n), ρ ≤ ‖x‖ →
        (((m / 2 - η) * ρ * ‖x‖ : ℝ) : EReal) ≤ f x := by
      exact convex_ray_lower_bound f hconvex hnot_bot hf0 hρ hρR hlocal_coercive
    let c : ℝ := (m / 2 - η) * ρ
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hray' : ∀ x : EuclideanSpace ℝ (Fin n), ρ ≤ ‖x‖ →
        ((c * ‖x‖ : ℝ) : EReal) ≤ f x := by
      intro x hx
      simpa [c, mul_assoc] using hray x hx
    let M : ℝ := ‖Ainv‖
    have hMnonneg : 0 ≤ M := by
      exact norm_nonneg _
    have hAinv_norm (y : EuclideanSpace ℝ (Fin n)) : ‖Ainv y‖ ≤ M * ‖y‖ := by
      simpa [M] using Ainv.le_opNorm y
    have hAinv_ne (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0) : Ainv y ≠ 0 := by
      intro hzero
      apply hy
      rw [← hright_apply y, hzero, map_zero]
    have hquad_inv_nonneg (y : EuclideanSpace ℝ (Fin n)) :
        0 ≤ inner ℝ (Ainv y) y / 2 := by
      by_cases hy : y = 0
      · simp [hy]
      · have hval : inner ℝ (Ainv y) y = inner ℝ (A (Ainv y)) (Ainv y) := by
          rw [hright_apply y]
          exact real_inner_comm _ _
        rw [hval]
        exact div_nonneg (hpos (Ainv y) (hAinv_ne y hy)).le (by norm_num)
    -- Use an error depending on the requested final neighbourhood; the fixed
    -- `η` above is retained only for the global coercive ray estimate.
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η' : ℝ := min (m / 8) (ε / (8 * (M ^ 2 + 1)))
    have hη' : 0 < η' := by
      dsimp [η']
      apply lt_min
      · positivity
      · positivity
    have hη'm : 2 * η' ≤ m / 2 := by
      have hle : η' ≤ m / 8 := min_le_left _ _
      linarith
    have hη'eps : 2 * η' * M ^ 2 < ε := by
      have hle : η' ≤ ε / (8 * (M ^ 2 + 1)) := min_le_right _ _
      have hden : 0 < M ^ 2 + 1 := by positivity
      have hsq : 0 ≤ M ^ 2 := sq_nonneg M
      have hfrac : M ^ 2 / (M ^ 2 + 1) < 1 := by
        apply (div_lt_one hden).mpr
        linarith
      calc
        2 * η' * M ^ 2 ≤ 2 * (ε / (8 * (M ^ 2 + 1))) * M ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) hsq
        _ = ε / 4 * (M ^ 2 / (M ^ 2 + 1)) := by field_simp; ring
        _ < ε / 4 * 1 := mul_lt_mul_of_pos_left hfrac (by linarith)
        _ = ε / 4 := by ring
        _ < ε := by linarith
    obtain ⟨r0, hr0pos, hlocal0⟩ := hlocal_quadratic_bounds η' hη'
    let r : ℝ := r0
    have hrpos : 0 < r := by simpa [r] using hr0pos
    have hlocal : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ‖x‖ < r →
        f x ≠ ⊤ ∧ inner ℝ (A x) x / 2 - η' * ‖x‖ ^ 2 < (f x).toReal ∧
          (f x).toReal < inner ℝ (A x) x / 2 + η' * ‖x‖ ^ 2 := by
      intro x hx hxr
      apply hlocal0 x hx
      simpa [r] using hxr
    have hlocal_coercive' : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖z‖ < r →
        (((m / 2 - η') * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z := by
      apply local_quadratic_coercive_lower f A hnot_bot hm hη'
      intro z hz hzr
      exact ⟨(hlocal z hz hzr).1, (hlocal z hz hzr).2.1⟩
    let ρ' : ℝ := r / 2
    have hρ' : 0 < ρ' := by dsimp [ρ']; linarith
    have hρ'r : ρ' < r := by dsimp [ρ']; linarith
    have hc'base : 0 < m / 2 - η' := by linarith [hη'm]
    have hray'' : ∀ x : EuclideanSpace ℝ (Fin n), ρ' ≤ ‖x‖ →
        (((m / 2 - η') * ρ' * ‖x‖ : ℝ) : EReal) ≤ f x := by
      exact convex_ray_lower_bound f hconvex hnot_bot hf0 hρ' hρ'r hlocal_coercive'
    let c' : ℝ := (m / 2 - η') * ρ'
    have hc' : 0 < c' := by dsimp [c']; positivity
    have hray''' : ∀ x : EuclideanSpace ℝ (Fin n), ρ' ≤ ‖x‖ →
        ((c' * ‖x‖ : ℝ) : EReal) ≤ f x := by
      intro x hx
      simpa [c', mul_assoc] using hray'' x hx
    let δ : ℝ := min (r / (2 * (M + 1))) (c' / 4)
    have hδ : 0 < δ := by
      dsimp [δ]
      apply lt_min <;> positivity
    simp only [dist_zero_right]
    rw [eventually_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, ?_⟩
    intro y hyδ hy0
    have hyδ' : ‖y‖ < δ := by simpa only [dist_zero_right] using hyδ
    have hy : y ≠ 0 := by simpa using hy0
    have hyc : ‖y‖ < c' / 2 := by
      have hd : δ ≤ c' / 4 := min_le_right _ _
      linarith [hyδ']
    have hyA : ‖Ainv y‖ < r := by
      have hd : δ ≤ r / (2 * (M + 1)) := min_le_left _ _
      have hbound := hAinv_norm y
      have hM : 0 ≤ M := hMnonneg
      have hyhalf : ‖y‖ < r / (2 * (M + 1)) := lt_of_lt_of_le hyδ' hd
      have hMle : M * ‖y‖ ≤ M * (r / (2 * (M + 1))) :=
        mul_le_mul_of_nonneg_left hyhalf.le hM
      calc
        ‖Ainv y‖ ≤ M * ‖y‖ := hbound
        _ ≤ M * (r / (2 * (M + 1))) := hMle
        _ < r := by
          have hden : 0 < 2 * (M + 1) := by positivity
          apply (lt_of_mul_lt_mul_right _ hden.le)
          field_simp
          nlinarith
    have hyAne : Ainv y ≠ 0 := hAinv_ne y hy
    have hyAlocal := hlocal (Ainv y) hyAne hyA
    -- First obtain the candidate lower bound in real arithmetic.
    have hA_sq : ‖Ainv y‖ ^ 2 ≤ M ^ 2 * ‖y‖ ^ 2 := by
      have := sq_le_sq₀ (norm_nonneg (Ainv y)) (mul_nonneg hMnonneg (norm_nonneg y)) |>.mpr
        (hAinv_norm y)
      nlinarith
    have hqA : inner ℝ (A (Ainv y)) (Ainv y) / 2 = inner ℝ (Ainv y) y / 2 := by
      rw [hright_apply y]
      exact congrArg (fun z : ℝ => z / 2) (real_inner_comm _ _)
    have hinnerA : inner ℝ y (Ainv y) = 2 * (inner ℝ (Ainv y) y / 2) := by
      rw [← real_inner_comm y (Ainv y), ← hright_apply y]
      ring
    have hlower_real : inner ℝ (Ainv y) y / 2 - η' * M ^ 2 * ‖y‖ ^ 2 <
        inner ℝ y (Ainv y) - (f (Ainv y)).toReal := by
      rw [hinnerA, ← hqA] at *
      nlinarith [hyAlocal.2.2]
    have hlower_e :
        ((inner ℝ (Ainv y) y / 2 - η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) <
          ((inner ℝ y (Ainv y) : ℝ) : EReal) - f (Ainv y) := by
      rw [← EReal.coe_toReal hyAlocal.1 (hnot_bot _), ← EReal.coe_sub]
      exact_mod_cast hlower_real
    have hlocal_upper : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ < r →
        ((inner ℝ y x : ℝ) : EReal) - f x ≤
          ((inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        rw [hf0]
        simp only [inner_zero_right, EReal.coe_zero, sub_zero]
        have hrest : 0 ≤ 2 * η' * M ^ 2 * ‖y‖ ^ 2 := by positivity
        exact_mod_cast (by nlinarith [hquad_inv_nonneg y] :
          0 ≤ inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2)
      have hxl := hlocal x hx0 hx
      have hreal := local_supremand_upper_real f A Ainv hsymm hAinv_right
        hη'.le hm hη'm hA_sq hxl.2.1
      rw [← EReal.coe_toReal hxl.1 (hnot_bot x), ← EReal.coe_sub]
      exact EReal.coe_le_coe hreal
    have houter_upper : ∀ x : EuclideanSpace ℝ (Fin n), ρ' ≤ ‖x‖ →
        ((inner ℝ y x : ℝ) : EReal) - f x ≤
          ((inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
      intro x hx
      by_cases hxtop : f x = ⊤
      · simp [hxtop]
      exact outer_supremand_upper f x y hnot_bot hxtop (hray''' x hx) hc' hyc
        (hquad_inv_nonneg y) hη'.le
    have hfstar_lower :
        ((inner ℝ (Ainv y) y / 2 - η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) < fstar y := by
      rw [hconjugate, ERealFunction.conjugate_apply]
      apply lt_of_lt_of_le hlower_e
      rw [real_inner_comm (Ainv y) y]
      exact le_iSup (fun x : EuclideanSpace ℝ (Fin n) =>
        ((inner ℝ x y : ℝ) : EReal) - f x) (Ainv y)
    have hfstar_upper : fstar y ≤
        ((inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
      rw [hconjugate, ERealFunction.conjugate_apply]
      apply iSup_le
      intro x
      by_cases hx : ‖x‖ < r
      · rw [real_inner_comm y x]
        exact hlocal_upper x hx
      · rw [real_inner_comm y x]
        apply houter_upper x
        have hrle : r ≤ ‖x‖ := le_of_not_gt hx
        have hhalf : r / 2 ≤ r := by nlinarith only [hrpos]
        change r / 2 ≤ ‖x‖
        exact hhalf.trans hrle
    have hfstar_bot : fstar y ≠ ⊥ := by
      intro hbot
      rw [hbot] at hfstar_lower
      exact (not_lt_bot) hfstar_lower
    have hfstar_top : fstar y ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hfstar_upper (by exact EReal.coe_lt_top _))
    have hynorm : (0 : ℝ) < ‖y‖ ^ 2 := norm_sq_pos_of_ne_zero y hy
    exact quotient_abs_lt_of_ereal_bounds hfstar_lower hfstar_upper hfstar_bot
      hfstar_top hynorm hη'eps

end AttouchAdlyDryFrictionDynamics2023
