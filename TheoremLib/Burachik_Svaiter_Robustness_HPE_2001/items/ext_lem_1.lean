import Mathlib

open Filter

namespace BurachikSvaiterRobustnessHPE2001

private theorem polyak_tail_properties (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (hsu : Summable u) :
    (let t : ℕ → ℝ := fun k => ∑' i : ℕ, u (i + k);
    (∀ k, 0 ≤ t k) ∧ (∀ k, t k = u k + t (k + 1)) ∧ Tendsto t Filter.atTop (nhds 0)) := by
  dsimp
  constructor
  · intro k
    exact tsum_nonneg fun i => hu (i + k)
  constructor
  · intro k
    have hprefix_k := hsu.sum_add_tsum_nat_add k
    have hprefix_succ := hsu.sum_add_tsum_nat_add (k + 1)
    simp only [Finset.sum_range_succ] at hprefix_succ
    simpa [Nat.add_assoc] using (sub_eq_iff_eq_add'.mp (by linarith [hprefix_k, hprefix_succ]))
  · exact _root_.tendsto_sum_nat_add u

private theorem polyak_sqrt_bridge {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    Real.sqrt ((u + Real.sqrt v) ^ 2 + w) ≤ u + Real.sqrt (v + w) := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg hu (Real.sqrt_nonneg _)
  have hvsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  have hvwsq : Real.sqrt (v + w) ^ 2 = v + w := Real.sq_sqrt (add_nonneg hv hw)
  have hs : Real.sqrt v ≤ Real.sqrt (v + w) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right hw)
  nlinarith [Real.sqrt_nonneg v, Real.sqrt_nonneg (v + w)]

private theorem polyak_sqrt_add_tail {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) :
    Real.sqrt (x ^ 2 + q) ≤ x + Real.sqrt q := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg hx (Real.sqrt_nonneg _)
  have hqsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  nlinarith [mul_nonneg hx (Real.sqrt_nonneg q)]

/-- Lemma 3.2 (Polyak): the scalar convergence estimate used by HPE. -/
theorem polyak_scalar_convergence (α δ γ : ℕ → ℝ)
    (hα : ∀ k, 0 ≤ α k) (hδ : ∀ k, 0 ≤ δ k) (hγ : ∀ k, 0 ≤ γ k)
    (hsα : Summable α) (hsδ : Summable δ)
    (hrec : ∀ k, γ (k + 1) ≤ α k + Real.sqrt (γ k ^ 2 + δ k)) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto γ Filter.atTop (nhds L) := by
  let q : ℕ → ℝ := fun k => ∑' i : ℕ, δ (i + k)
  let a : ℕ → ℝ := fun k => ∑' i : ℕ, α (i + k)
  obtain ⟨hq_nonneg, hq_shift, hq_zero⟩ := polyak_tail_properties δ hδ hsδ
  obtain ⟨ha_nonneg, ha_shift, ha_zero⟩ := polyak_tail_properties α hα hsα
  have hq_nonneg' : ∀ k, 0 ≤ q k := by simpa [q] using hq_nonneg
  have ha_nonneg' : ∀ k, 0 ≤ a k := by simpa [a] using ha_nonneg
  have hq_shift' : ∀ k, q k = δ k + q (k + 1) := by simpa [q] using hq_shift
  have ha_shift' : ∀ k, a k = α k + a (k + 1) := by simpa [a] using ha_shift
  have hq_zero' : Tendsto q Filter.atTop (nhds 0) := by simpa [q] using hq_zero
  have ha_zero' : Tendsto a Filter.atTop (nhds 0) := by simpa [a] using ha_zero
  let s : ℕ → ℝ := fun k => Real.sqrt (γ k ^ 2 + q k)
  have hs_step : ∀ k, s (k + 1) ≤ α k + s k := by
    intro k
    have hsq : γ (k + 1) ^ 2 ≤ (α k + Real.sqrt (γ k ^ 2 + δ k)) ^ 2 :=
      (sq_le_sq₀ (hγ (k + 1)) (add_nonneg (hα k) (Real.sqrt_nonneg _))).2 (hrec k)
    have hrad : γ (k + 1) ^ 2 + q (k + 1) ≤
        (α k + Real.sqrt (γ k ^ 2 + δ k)) ^ 2 + q (k + 1) := by linarith
    calc
      s (k + 1) ≤ Real.sqrt ((α k + Real.sqrt (γ k ^ 2 + δ k)) ^ 2 + q (k + 1)) := by
        exact Real.sqrt_le_sqrt hrad
      _ ≤ α k + Real.sqrt ((γ k ^ 2 + δ k) + q (k + 1)) :=
        polyak_sqrt_bridge (hα k) (add_nonneg (sq_nonneg _) (hδ k)) (hq_nonneg' _)
      _ = α k + s k := by
        simp only [s]
        rw [show γ k ^ 2 + δ k + q (k + 1) = γ k ^ 2 + (δ k + q (k + 1)) by ring,
          ← hq_shift' k]
  let r : ℕ → ℝ := fun k => s k + a k
  have hr_succ : ∀ k, r (k + 1) ≤ r k := by
    intro k
    dsimp [r]
    linarith [hs_step k, ha_shift' k]
  have hr_anti : Antitone r := antitone_nat_of_succ_le hr_succ
  have hr_nonneg : ∀ k, 0 ≤ r k := fun k => add_nonneg (Real.sqrt_nonneg _) (ha_nonneg' k)
  have hr_bdd : BddBelow (Set.range r) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hr_nonneg k
  let L : ℝ := ⨅ k, r k
  have hr_lim : Tendsto r Filter.atTop (nhds L) := tendsto_atTop_ciInf hr_anti hr_bdd
  have hs_lim : Tendsto s Filter.atTop (nhds L) := by
    simpa [r, sub_eq_add_neg] using hr_lim.sub ha_zero'
  have hL_nonneg : 0 ≤ L := by
    exact ge_of_tendsto' hs_lim fun k => Real.sqrt_nonneg _
  have hdiff : ∀ k, 0 ≤ s k - γ k ∧ s k - γ k ≤ Real.sqrt (q k) := by
    intro k
    have hle : γ k ≤ s k := by
      have hsq : γ k ^ 2 ≤ γ k ^ 2 + q k := le_add_of_nonneg_right (hq_nonneg' k)
      simpa [s, Real.sqrt_sq (hγ k)] using Real.sqrt_le_sqrt hsq
    constructor
    · exact sub_nonneg.mpr hle
    · have hupper := polyak_sqrt_add_tail (hγ k) (hq_nonneg' k)
      change Real.sqrt (γ k ^ 2 + q k) ≤ γ k + Real.sqrt (q k) at hupper
      linarith
  have hsqrtq_zero : Tendsto (fun k => Real.sqrt (q k)) Filter.atTop (nhds 0) := by
    simpa using hq_zero'.sqrt
  have hdiff_zero : Tendsto (fun k => s k - γ k) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrtq_zero
    · exact Filter.Eventually.of_forall fun k => (hdiff k).1
    · exact Filter.Eventually.of_forall fun k => (hdiff k).2
  refine ⟨L, hL_nonneg, ?_⟩
  simpa [sub_eq_add_neg] using hs_lim.sub hdiff_zero

end BurachikSvaiterRobustnessHPE2001
