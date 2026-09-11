import Foundation.Hilbert.WeakConvergence

open scoped Topology
open Filter

namespace BurachikSvaiterRobustnessHPE2001

/-- Opial's lemma, recalled from Foundation. -/
theorem opial_lemma_paper {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (x : ℕ → H) (xLimit z : H)
    (hx : Tendsto (fun j ↦ toWeakSpace ℝ H (x j)) Filter.atTop
      (nhds (toWeakSpace ℝ H xLimit))) (hz : z ≠ xLimit) :
    Filter.liminf (fun j ↦ ‖x j - z‖) Filter.atTop >
      Filter.liminf (fun j ↦ ‖x j - xLimit‖) Filter.atTop := by
  let r : ℕ → ℝ := fun j ↦ ‖x j - xLimit‖
  let s : ℕ → ℝ := fun j ↦ ‖x j - z‖
  let q : ℕ → ℝ := fun j ↦ r j ^ 2
  let d : H := xLimit - z
  have hx_bdd : Bornology.IsBounded (Set.range x) :=
    bounded_range_of_tendsto_weakly hx
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨R, hR⟩
  have hr_nonneg : ∀ j, 0 ≤ r j := fun j ↦ norm_nonneg _
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ norm_nonneg _
  have hr_upper : ∀ j, r j ≤ R + ‖xLimit‖ := by
    intro j
    dsimp [r]
    exact (norm_sub_le _ _).trans (by
      simpa [add_comm] using add_le_add_left (hR _ (Set.mem_range_self j)) ‖xLimit‖)
  have hs_upper : ∀ j, s j ≤ R + ‖z‖ := by
    intro j
    dsimp [s]
    exact (norm_sub_le _ _).trans (by
      simpa [add_comm] using add_le_add_left (hR _ (Set.mem_range_self j)) ‖z‖)
  have hr_bddbelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop r :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hr_nonneg)
  have hs_bddbelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop s :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hs_nonneg)
  have hr_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop r :=
    isCoboundedUnder_ge_of_le Filter.atTop hr_upper
  have hs_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop s :=
    isCoboundedUnder_ge_of_le Filter.atTop hs_upper
  have hlim_r_nonneg : 0 ≤ Filter.liminf r Filter.atTop :=
    Filter.le_liminf_of_le hr_cobdd (Filter.Eventually.of_forall hr_nonneg)
  let g : ℝ → ℝ := fun t ↦ max t 0 ^ 2
  have hg_mono : Monotone g := by
    intro a b hab
    dsimp [g]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ hab) 2
  have hg_cont : ContinuousAt g (Filter.liminf r Filter.atTop) :=
    ((continuousAt_id.max continuousAt_const).pow 2)
  have hq_eq : Filter.liminf q Filter.atTop = (Filter.liminf r Filter.atTop) ^ 2 := by
    have hmap := hg_mono.map_liminf_of_continuousAt r hg_cont hr_cobdd hr_bddbelow
    rw [show g (Filter.liminf r Filter.atTop) = (Filter.liminf r Filter.atTop) ^ 2 by
      simp [g, hlim_r_nonneg], show g ∘ r = q by
      funext j
      simp [g, q, hr_nonneg j]] at hmap
    exact hmap.symm
  have hq_nonneg : ∀ j, 0 ≤ q j := by
    intro j
    dsimp [q]
    positivity
  have hq_bddbelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop q :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hq_nonneg)
  have hB_nonneg : 0 ≤ R + ‖xLimit‖ :=
    (hr_nonneg 0).trans (hr_upper 0)
  have hq_upper : ∀ j, q j ≤ (R + ‖xLimit‖) ^ 2 := by
    intro j
    dsimp [q]
    exact pow_le_pow_left₀ (hr_nonneg j) (hr_upper j) 2
  have hq_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop q :=
    isCoboundedUnder_ge_of_le Filter.atTop hq_upper
  obtain ⟨φ, hφs, hφ⟩ :=
    exists_seq_tendsto_liminf (f := Filter.atTop) (u := s) hs_cobdd hs_bddbelow
  have hxφ : Tendsto (fun n ↦ toWeakSpace ℝ H (x (φ n))) Filter.atTop
      (nhds (toWeakSpace ℝ H xLimit)) := hx.comp hφ
  have hinner : Tendsto (fun n ↦ 2 * inner ℝ (x (φ n) - xLimit) d) Filter.atTop
      (nhds 0) := by
    have h := (weakConvergence_iff_forall_tendsto_inner_right (fun n ↦ x (φ n)) xLimit).1 hxφ d
    have hsub := h.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ inner ℝ xLimit d) Filter.atTop
      (nhds (inner ℝ xLimit d)))
    have hzero : Tendsto (fun n ↦ inner ℝ (x (φ n) - xLimit) d) Filter.atTop (nhds 0) := by
      simpa [inner_sub_left] using hsub
    simpa using hzero.const_mul 2
  have hsq (n : ℕ) : s (φ n) ^ 2 = q (φ n) + 2 * inner ℝ (x (φ n) - xLimit) d + ‖d‖ ^ 2 := by
    dsimp [s, q, r, d]
    rw [show x (φ n) - z = (x (φ n) - xLimit) + (xLimit - z) by abel]
    rw [norm_add_sq_real]
  have hs_sq : Tendsto (fun n ↦ s (φ n) ^ 2) Filter.atTop
      (nhds ((Filter.liminf s Filter.atTop) ^ 2)) := by
    simpa [Function.comp_def] using hφs.pow 2
  have hqφ : Tendsto (q ∘ φ) Filter.atTop
      (nhds ((Filter.liminf s Filter.atTop) ^ 2 - ‖d‖ ^ 2)) := by
    have hsub := (hs_sq.sub hinner).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖d‖ ^ 2) Filter.atTop (nhds (‖d‖ ^ 2)))
    convert hsub using 1
    · ext n
      change q (φ n) = _
      rw [hsq]
      ring_nf
    · ring_nf
  have hqφ_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (q ∘ φ) :=
    isCoboundedUnder_ge_of_le Filter.atTop (fun n ↦ hq_upper (φ n))
  have hq_le : Filter.liminf q Filter.atTop ≤ (Filter.liminf s Filter.atTop) ^ 2 - ‖d‖ ^ 2 := by
    calc
      Filter.liminf q Filter.atTop ≤ Filter.liminf (q ∘ φ) Filter.atTop :=
        hφ.liminf_le_liminf_comp hqφ_cobdd hq_bddbelow
      _ = (Filter.liminf s Filter.atTop) ^ 2 - ‖d‖ ^ 2 := hqφ.liminf_eq
  have hd : d ≠ 0 := by
    intro hd
    apply hz
    dsimp [d] at hd
    exact sub_eq_zero.mp hd |>.symm
  have hc_pos : 0 < ‖d‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hs_sq_lt : (Filter.liminf r Filter.atTop) ^ 2 < (Filter.liminf s Filter.atTop) ^ 2 := by
    rw [← hq_eq]
    nlinarith
  have hlim_s_nonneg : 0 ≤ Filter.liminf s Filter.atTop :=
    Filter.le_liminf_of_le hs_cobdd (Filter.Eventually.of_forall hs_nonneg)
  exact (sq_lt_sq₀ hlim_r_nonneg hlim_s_nonneg).mp hs_sq_lt

end BurachikSvaiterRobustnessHPE2001
