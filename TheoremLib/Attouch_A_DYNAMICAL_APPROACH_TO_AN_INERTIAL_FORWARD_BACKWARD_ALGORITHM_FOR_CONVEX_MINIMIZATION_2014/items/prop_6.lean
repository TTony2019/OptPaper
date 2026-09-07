import Mathlib
import Foundation.Hilbert.WeakTopology
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.lem_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_3

namespace AttouchPeypouquetRedont2014

private theorem contract_eventually_lt (p e : ℕ → ℝ) (η : ℝ)
    (hη : 0 < η ∧ η < 1) (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (hrec : ∀ k, p (k + 1) ≤ η * p k + e k) :
    ∀ r : ℝ, 0 < r → ∀ᶠ k in Filter.atTop, p k < r := by
  intro r hr
  let q : ℝ := r * (1 - η) / 2
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos hr (sub_pos.mpr hη.2)) (by norm_num)
  have htail : ∀ᶠ k in Filter.atTop, e k ≤ q := he.eventually_le_const hq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  have hqdiv : q / (1 - η) < r := by
    have hgap : 1 - η ≠ 0 := ne_of_gt (sub_pos.mpr hη.2)
    dsimp [q]
    field_simp [hgap]
    linarith
  exact eventually_lt_of_contract_recurrence p η q N hη.1.le hη.2 hq
    (fun k hk => (hrec k).trans (by gcongr; exact hN k hk)) r hqdiv

private theorem tendsto_zero_of_contract_eq (p e : ℕ → ℝ) (η : ℝ)
    (hη : 0 < η ∧ η < 1) (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (hrec : ∀ k, p (k + 1) = η * p k + e k) :
    Filter.Tendsto p Filter.atTop (nhds 0) := by
  have hup := contract_eventually_lt p e η hη he (fun k => (hrec k).le)
  have hneg_rec : ∀ k, (-p) (k + 1) ≤ η * (-p) k + (-e) k := by
    intro k
    simp only [Pi.neg_apply, hrec]
    ring_nf
    exact le_rfl
  have hneg := contract_eventually_lt (-p) (-e) η hη (by simpa using he.neg) hneg_rec
  rw [tendsto_order]
  constructor
  · intro r hr
    have h := hneg (-r) (by linarith)
    filter_upwards [h] with k hk
    dsimp at hk
    linarith
  · intro r hr
    exact hup r hr

private theorem tendsto_zero_of_contract_nonneg (p e : ℕ → ℝ) (η : ℝ)
    (hη : 0 < η ∧ η < 1) (hp : ∀ k, 0 ≤ p k)
    (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (hrec : ∀ k, p (k + 1) ≤ η * p k + e k) :
    Filter.Tendsto p Filter.atTop (nhds 0) := by
  have hlim := contract_eventually_lt p e η hη he hrec
  rw [tendsto_order]
  constructor
  · intro r hr
    filter_upwards with k
    exact lt_of_lt_of_le hr (hp k)
  · intro r hr
    exact hlim r hr

/-- Proposition 12: convergence transfer from `u_k` to `y_k` for IFB trajectories. -/
theorem proposition12 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam : ℝ) (u y : ℕ → H)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hgrad_cont : Continuous gradPsi)
    (uLimit : H) :
    ((Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
        (nhds (toWeakSpace ℝ H uLimit)) ∧ IsWeakToWeakSequentiallyContinuous gradPsi) →
      ∃ yLim : H, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (y k)) Filter.atTop
        (nhds (toWeakSpace ℝ H yLim)) ∧ gradPsi uLimit - a • uLimit + b • yLim = 0) ∧
    (Filter.Tendsto u Filter.atTop (nhds uLimit) →
      ∃ yLim : H, Filter.Tendsto y Filter.atTop (nhds yLim) ∧
        gradPsi uLimit - a • uLimit + b • yLim = 0) := by
  have hb_pos := hIFB.b_pos
  have hlam_pos := hIFB.lambda_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hden_pos : 0 < 1 + lam * b := by nlinarith [mul_pos hlam_pos hb_pos]
  have hden_ne : 1 + lam * b ≠ 0 := ne_of_gt hden_pos
  let η : ℝ := (1 + lam * b)⁻¹
  have hη : 0 < η ∧ η < 1 := by
    constructor
    · dsimp [η]
      positivity
    · dsimp [η]
      rw [inv_lt_one₀ hden_pos]
      nlinarith [mul_pos hlam_pos hb_pos]
  let yLim : H := b⁻¹ • (a • uLimit - gradPsi uLimit)
  have hyLim : gradPsi uLimit - a • uLimit + b • yLim = 0 := by
    dsimp [yLim]
    rw [smul_smul]
    field_simp [hb_ne]
    module
  let w : ℕ → H := fun k => b⁻¹ • (a • u (k + 1) - gradPsi (u (k + 1)))
  have hw : ∀ k, b • w k = a • u (k + 1) - gradPsi (u (k + 1)) := by
    intro k
    simp [w, smul_smul, hb_ne]
  have hrec : ∀ k, y (k + 1) - yLim = η • (y k - yLim) +
      (lam * b * η) • (w k - yLim) := by
    intro k
    have hs := hIFB.second_update k
    have hmiddle : gradPsi (u (k + 1)) - a • u (k + 1) = -(b • w k) := by
      rw [hw k]
      abel
    have hs' : (1 / lam) • (y (k + 1) - y k) +
        (gradPsi (u (k + 1)) - a • u (k + 1)) + b • y (k + 1) = 0 := by
      convert hs using 1; abel
    rw [hmiddle] at hs'
    have hscaled := congrArg (fun z : H => lam • z) hs'
    have hraw : (y (k + 1) - y k) + (lam * b) • (y (k + 1) - w k) = 0 := by
      convert hscaled using 1 <;>
        simp [smul_add, smul_sub, smul_smul, div_eq_mul_inv, hlam_ne]; module
    have hbase : (1 + lam * b) • y (k + 1) = y k + (lam * b) • w k := by
      have hsubbase : (1 + lam * b) • y (k + 1) - (lam * b) • w k = y k := by
        calc
        (1 + lam * b) • y (k + 1) - (lam * b) • w k =
            y k + ((y (k + 1) - y k) + (lam * b) • (y (k + 1) - w k)) := by
              simp only [add_smul, one_smul, smul_sub]
              abel
        _ = y k := by rw [hraw]; abel
      exact eq_add_of_sub_eq hsubbase
    have hlimbase : (1 + lam * b) • yLim = yLim + (lam * b) • yLim := by
      module
    have hsub : (1 + lam * b) • (y (k + 1) - yLim) =
        (y k - yLim) + (lam * b) • (w k - yLim) := by
      rw [smul_sub, hbase, hlimbase]
      module
    have hinv : η * (1 + lam * b) = 1 := by
      dsimp [η]
      field_simp
    have := congrArg (fun z : H => η • z) hsub
    change η • ((1 + lam * b) • (y (k + 1) - yLim)) =
      η • ((y k - yLim) + (lam * b) • (w k - yLim)) at this
    rw [smul_smul, hinv, one_smul] at this
    convert this using 1; rw [smul_add, smul_smul]; module
  constructor
  · rintro ⟨huweak, hww⟩
    have husucc := huweak.comp (Filter.tendsto_add_atTop_nat 1)
    have hgradsucc := hww _ _ husucc
    have hwwlim : Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (w k)) Filter.atTop
        (nhds (toWeakSpace ℝ H yLim)) := by
      apply (weakConvergence_iff_forall_tendsto_inner_right w yLim).2
      intro ξ
      have hucoord := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 husucc ξ
      have hgcoord := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 hgradsucc ξ
      simpa [w, yLim, real_inner_smul_left, inner_sub_left] using
        (hucoord.const_smul a).sub hgcoord |>.const_smul b⁻¹
    refine ⟨yLim, ?_, hyLim⟩
    apply (weakConvergence_iff_forall_tendsto_inner_right y yLim).2
    intro ξ
    let p : ℕ → ℝ := fun k => inner ℝ (y k - yLim) ξ
    let e : ℕ → ℝ := fun k => (lam * b * η) * inner ℝ (w k - yLim) ξ
    have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
      have hc := (weakConvergence_iff_forall_tendsto_inner_right w yLim).1 hwwlim ξ
      simpa [e, inner_sub_left] using
        (hc.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => inner ℝ yLim ξ)
          Filter.atTop (nhds (inner ℝ yLim ξ)))).const_mul (lam * b * η)
    have hp_rec : ∀ k, p (k + 1) = η * p k + e k := by
      intro k
      dsimp [p, e]
      have := congrArg (fun z : H => inner ℝ z ξ) (hrec k)
      simpa [inner_sub_left, inner_add_left, real_inner_smul_left] using this
    have hp0 := tendsto_zero_of_contract_eq p e η hη he hp_rec
    simpa [p, inner_sub_left] using hp0.add
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => inner ℝ yLim ξ)
        Filter.atTop (nhds (inner ℝ yLim ξ)))
  · intro hu
    have husucc := hu.comp (Filter.tendsto_add_atTop_nat 1)
    have hgradsucc := (hgrad_cont.tendsto uLimit).comp husucc
    have hwlim : Filter.Tendsto w Filter.atTop (nhds yLim) := by
      simpa [w, yLim] using ((husucc.const_smul a).sub hgradsucc).const_smul b⁻¹
    refine ⟨yLim, ?_, hyLim⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    let p : ℕ → ℝ := fun k => ‖y k - yLim‖
    let e : ℕ → ℝ := fun k => (lam * b * η) * ‖w k - yLim‖
    have hcoeff : 0 ≤ lam * b * η := by positivity
    have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
      have hz' := hwlim.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => yLim)
          Filter.atTop (nhds yLim))
      have hz : Filter.Tendsto (fun k => w k - yLim) Filter.atTop (nhds 0) := by
        simpa using hz'
      simpa [e] using hz.norm.const_mul (lam * b * η)
    have hp_rec : ∀ k, p (k + 1) ≤ η * p k + e k := by
      intro k
      dsimp [p, e]
      rw [hrec k]
      calc
        ‖η • (y k - yLim) + (lam * b * η) • (w k - yLim)‖ ≤
            ‖η • (y k - yLim)‖ + ‖(lam * b * η) • (w k - yLim)‖ := norm_add_le _ _
        _ = η * ‖y k - yLim‖ + (lam * b * η) * ‖w k - yLim‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hη.1,
            abs_of_nonneg hcoeff]
    simpa [p] using tendsto_zero_of_contract_nonneg p e η hη (fun k => norm_nonneg _) he hp_rec

end AttouchPeypouquetRedont2014
