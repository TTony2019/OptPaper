import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_5

namespace AttouchAdlyDryFrictionDynamics2023

/-- The potential `ψ(v)=φ(v)+½‖v‖²`. -/
noncomputable def dualPotential {H : Type*} [NormedAddCommGroup H] (r : ℝ) (_hr : 0 < r) (v : H) : ℝ :=
  dryFrictionPotential (H := H) r v + ‖v‖ ^ 2 / 2

/-- The Fenchel conjugate `ψ*` of the dual potential. -/
noncomputable def dualPotentialConjugate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r : ℝ) (hr : 0 < r) : H → EReal :=
  ERealFunction.conjugate (fun v => (dualPotential r hr v : EReal))

/-- The displayed identity `ψ*(ξ) = 1/2 dist²(ξ, B(0,r))`. -/
private theorem dualPotentialConjugate_radial_sup {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (r : ℝ) (hr : 0 < r) (ξ : H) :
    (⨆ v : H, ((inner ℝ ξ v - r * ‖v‖ - ‖v‖ ^ 2 / 2 : ℝ) : EReal)) =
      ((max (‖ξ‖ - r) 0 ^ 2 / 2 : ℝ) : EReal) := by
  by_cases hball : ‖ξ‖ ≤ r
  · have ha : ‖ξ‖ - r ≤ 0 := sub_nonpos.mpr hball
    have hupper : (⨆ v : H, ((inner ℝ ξ v - r * ‖v‖ - ‖v‖ ^ 2 / 2 : ℝ) : EReal)) ≤ 0 := by
      refine iSup_le fun v => ?_
      apply EReal.coe_nonpos.mpr
      have hinner : inner ℝ ξ v ≤ ‖ξ‖ * ‖v‖ := real_inner_le_norm ξ v
      have hmul : (‖ξ‖ - r) * ‖v‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha (norm_nonneg v)
      have hsq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg ‖v‖
      nlinarith
    have hlower : (0 : EReal) ≤ ⨆ v : H, ((inner ℝ ξ v - r * ‖v‖ - ‖v‖ ^ 2 / 2 : ℝ) : EReal) := by
      refine le_iSup_of_le (0 : H) ?_
      simp
    have hsup := le_antisymm hupper hlower
    rw [hsup]
    have : max (‖ξ‖ - r) 0 = 0 := max_eq_right ha
    simp [this]
  · have houtside : r < ‖ξ‖ := lt_of_not_ge hball
    have ha : 0 < ‖ξ‖ - r := sub_pos.mpr houtside
    have hnorm : 0 < ‖ξ‖ := lt_trans hr houtside
    let v0 : H := ((‖ξ‖ - r) / ‖ξ‖) • ξ
    have hvnorm : ‖v0‖ = ‖ξ‖ - r := by
      dsimp [v0]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      · field_simp
      · exact div_nonneg (le_of_lt ha) (le_of_lt hnorm)
    have hvinner : inner ℝ ξ v0 = (‖ξ‖ - r) * ‖ξ‖ := by
      dsimp [v0]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hvalue : inner ℝ ξ v0 - r * ‖v0‖ - ‖v0‖ ^ 2 / 2 = (‖ξ‖ - r) ^ 2 / 2 := by
      rw [hvnorm, hvinner]
      ring
    have hupper : (⨆ v : H, ((inner ℝ ξ v - r * ‖v‖ - ‖v‖ ^ 2 / 2 : ℝ) : EReal)) ≤
        (((‖ξ‖ - r) ^ 2 / 2 : ℝ) : EReal) := by
      refine iSup_le fun v => ?_
      exact EReal.coe_le_coe (by
        have hinner : inner ℝ ξ v ≤ ‖ξ‖ * ‖v‖ := real_inner_le_norm ξ v
        have hsq : 0 ≤ (‖v‖ - (‖ξ‖ - r)) ^ 2 := sq_nonneg _
        nlinarith)
    have hlower : (((‖ξ‖ - r) ^ 2 / 2 : ℝ) : EReal) ≤
        ⨆ v : H, ((inner ℝ ξ v - r * ‖v‖ - ‖v‖ ^ 2 / 2 : ℝ) : EReal) := by
      refine le_iSup_of_le v0 ?_
      exact EReal.coe_le_coe hvalue.symm.le
    have hsup := le_antisymm hupper hlower
    rw [max_eq_left (le_of_lt ha)]
    exact hsup

private theorem infDist_frictionBall_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (r : ℝ) (hr : 0 < r) (ξ : H) :
    Metric.infDist ξ (frictionBall (H := H) r) = max (‖ξ‖ - r) 0 := by
  have hnonempty : (frictionBall (H := H) r).Nonempty := by
    refine ⟨0, ?_⟩
    simp [frictionBall, le_of_lt hr]
  have hlower : max (‖ξ‖ - r) 0 ≤ Metric.infDist ξ (frictionBall (H := H) r) := by
    apply (Metric.le_infDist hnonempty).mpr
    intro y hy
    have hy' : ‖y‖ ≤ r := by
      simpa [frictionBall, dist_eq_norm] using hy
    have htri : ‖ξ‖ ≤ ‖ξ - y‖ + ‖y‖ := by
      calc
        ‖ξ‖ = ‖(ξ - y) + y‖ := by congr 1; abel
        _ ≤ ‖ξ - y‖ + ‖y‖ := norm_add_le _ _
    have hdiff : ‖ξ‖ - r ≤ ‖ξ - y‖ := by linarith
    rw [dist_eq_norm]
    exact max_le hdiff (norm_nonneg _)
  by_cases hball : ‖ξ‖ ≤ r
  · have hmem : ξ ∈ frictionBall (H := H) r := by
      simpa [frictionBall, dist_eq_norm] using hball
    have hzero : Metric.infDist ξ (frictionBall (H := H) r) = 0 := by
      apply le_antisymm
      · simpa using (Metric.infDist_le_dist_of_mem (x := ξ) hmem)
      · exact Metric.infDist_nonneg
    rw [hzero, max_eq_right (sub_nonpos.mpr hball)]
  · have houtside : r < ‖ξ‖ := lt_of_not_ge hball
    have hnorm : 0 < ‖ξ‖ := lt_trans hr houtside
    let y : H := (r / ‖ξ‖) • ξ
    have hynorm : ‖y‖ = r := by
      dsimp [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      · field_simp
      · exact div_nonneg (le_of_lt hr) (le_of_lt hnorm)
    have hymem : y ∈ frictionBall (H := H) r := by
      simpa [frictionBall, dist_eq_norm] using hynorm.le
    have hfactor : 0 ≤ 1 - r / ‖ξ‖ := by
      rw [sub_nonneg]
      exact (div_le_iff₀ hnorm).mpr (by simpa using houtside.le)
    have hdist : dist ξ y = ‖ξ‖ - r := by
      calc
        dist ξ y = ‖ξ - y‖ := dist_eq_norm _ _
        _ = ‖(1 - r / ‖ξ‖) • ξ‖ := by
          congr 1
          dsimp [y]
          calc
            ξ - (r / ‖ξ‖) • ξ = (1 : ℝ) • ξ - (r / ‖ξ‖) • ξ := by rw [one_smul]
            _ = (1 - r / ‖ξ‖) • ξ := by rw [← sub_smul]
        _ = (1 - r / ‖ξ‖) * ‖ξ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfactor]
        _ = ‖ξ‖ - r := by field_simp
    apply le_antisymm
    · calc
        Metric.infDist ξ (frictionBall (H := H) r) ≤ dist ξ y :=
          Metric.infDist_le_dist_of_mem hymem
        _ = ‖ξ‖ - r := hdist
        _ = max (‖ξ‖ - r) 0 := (max_eq_left (sub_nonneg.mpr houtside.le)).symm
    · exact hlower

theorem dualPotentialConjugate_formula {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r : ℝ) (hr : 0 < r) :
    ∀ ξ, dualPotentialConjugate r hr ξ = ((Metric.infDist ξ (frictionBall (H := H) r) ^ 2 / 2 : ℝ) : EReal) := by
  intro ξ
  change (⨆ v : H, (inner ℝ v ξ : EReal) -
      ((r * ‖v‖ + ‖v‖ ^ 2 / 2 : ℝ) : EReal)) = _
  have hterms :
      (fun v : H => (inner ℝ v ξ : EReal) - ((r * ‖v‖ + ‖v‖ ^ 2 / 2 : ℝ) : EReal)) =
        fun v : H => ((inner ℝ ξ v - r * ‖v‖ - ‖v‖ ^ 2 / 2 : ℝ) : EReal) := by
    funext v
    rw [← EReal.coe_sub, real_inner_comm]
    congr 1
    ring
  rw [hterms, dualPotentialConjugate_radial_sup r hr ξ, infDist_frictionBall_eq r hr ξ]

/-- The paper's Bregman distance in equation (3.10). -/
def dualBregmanDistance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (fstar : H → ℝ) (gradFstar : H → H)
    (g gLimit : H) : ℝ :=
  bregmanDistance fstar gradFstar g gLimit

end AttouchAdlyDryFrictionDynamics2023
