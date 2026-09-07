import Mathlib.Tactic

/-!
# Lemma 2.3
-/

open Filter
open scoped Topology

namespace Alvarez2004

/-- Positive part `[t]_+ = max {t, 0}`. -/
def posPart (t : ℝ) : ℝ :=
  max t 0

private lemma posPart_nonneg (t : ℝ) : 0 ≤ posPart t := by
  dsimp [posPart]
  exact le_max_right _ _

private lemma posPart_ge_self (t : ℝ) : t ≤ posPart t := by
  dsimp [posPart]
  exact le_max_left _ _

private lemma posPart_mul_of_nonneg {c t : ℝ} (hc : 0 ≤ c) :
    posPart (c * t) = c * posPart t := by
  dsimp [posPart]
  by_cases ht : t ≤ 0
  · have hct : c * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc ht
    rw [max_eq_right hct, max_eq_right ht, mul_zero]
  · have hpos_t : 0 ≤ t := le_of_not_ge ht
    have hct : 0 ≤ c * t := mul_nonneg hc hpos_t
    rw [max_eq_left hct, max_eq_left hpos_t]

private lemma posPart_add_le_add_of_nonneg {x y : ℝ} (hy : 0 ≤ y) :
    posPart (x + y) ≤ posPart x + y := by
  dsimp [posPart]
  by_cases hsum : x + y ≤ 0
  · rw [max_eq_right hsum]
    have hx : 0 ≤ max x 0 := le_max_right _ _
    linarith
  · have hsum_nonneg : 0 ≤ x + y := le_of_not_ge hsum
    rw [max_eq_left hsum_nonneg]
    have hx : x ≤ max x 0 := le_max_left _ _
    linarith

private lemma posPart_mono {a b : ℝ} (h : a ≤ b) : posPart a ≤ posPart b := by
  dsimp [posPart]
  exact max_le_max h (le_refl 0)

/-- Lemma 2.3: convergence of an inertial scalar recursion with summable errors. -/
lemma lemma_2_3
    (phi delta alphaSeq : ℕ → ℝ) (alphaBar : ℝ)
    (hphi_nonneg : ∀ k : ℕ, 0 ≤ phi k)
    (hdelta_nonneg : ∀ k : ℕ, 0 ≤ delta k)
    (hrec :
      ∀ k : ℕ,
        phi (k + 1) ≤
          phi k + alphaSeq k * (phi k - phi (k - 1)) + delta k)
    (hdelta_sum : Summable delta)
    (halpha : ∀ k : ℕ, 0 ≤ alphaSeq k ∧ alphaSeq k ≤ alphaBar)
    (halphaBar : alphaBar < 1) :
    Summable (fun k : ℕ ↦ posPart (phi k - phi (k - 1))) ∧
      ∃ phiStar : ℝ, 0 ≤ phiStar ∧ Tendsto phi atTop (𝓝 phiStar) := by
  set theta := fun k : ℕ => phi k - phi (k - 1) with htheta_def
  have htheta_zero : theta 0 = 0 := by
    dsimp [theta]
    simp
  have hpos_theta_zero : posPart (theta 0) = 0 := by
    rw [htheta_zero]
    dsimp [posPart]
    simp
  have halphaBar_nonneg : 0 ≤ alphaBar := by
    exact le_trans (halpha 0).1 (halpha 0).2
  have hone_sub_pos : 0 < 1 - alphaBar := by linarith
  have htheta_rec (k : ℕ) : theta (k + 1) ≤ alphaSeq k * theta k + delta k := by
    dsimp [theta]
    have h := hrec k
    linarith
  have hpos_rec (k : ℕ) :
      posPart (theta (k + 1)) ≤ alphaBar * posPart (theta k) + delta k := by
    have hmono : posPart (theta (k + 1)) ≤
        posPart (alphaSeq k * theta k + delta k) :=
      posPart_mono (htheta_rec k)
    have hsplit : posPart (alphaSeq k * theta k + delta k) ≤
        posPart (alphaSeq k * theta k) + delta k :=
      posPart_add_le_add_of_nonneg (hdelta_nonneg k)
    have hhom : posPart (alphaSeq k * theta k) = alphaSeq k * posPart (theta k) :=
      posPart_mul_of_nonneg (halpha k).1
    have hbound : alphaSeq k * posPart (theta k) ≤ alphaBar * posPart (theta k) := by
      exact mul_le_mul_of_nonneg_right (halpha k).2 (posPart_nonneg _)
    linarith
  set Dtotal := ∑' k, delta k with hDtotal_def
  have hDpartial_le_total (n : ℕ) :
      (Finset.range n).sum delta ≤ Dtotal := by
    simpa [Dtotal] using hdelta_sum.sum_le_tsum (Finset.range n)
      (fun i _hi => hdelta_nonneg i)
  have hsum_rec (n : ℕ) :
      (Finset.range n).sum (fun k => posPart (theta (k + 1))) ≤
        alphaBar * (Finset.range n).sum (fun k => posPart (theta k)) +
          (Finset.range n).sum delta := by
    calc
      (Finset.range n).sum (fun k => posPart (theta (k + 1)))
          ≤ (Finset.range n).sum
              (fun k => alphaBar * posPart (theta k) + delta k) := by
            exact Finset.sum_le_sum (fun k _hk => hpos_rec k)
      _ = alphaBar * (Finset.range n).sum (fun k => posPart (theta k)) +
          (Finset.range n).sum delta := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hS_bound (n : ℕ) :
      (Finset.range n).sum (fun k => posPart (theta k)) ≤
        Dtotal / (1 - alphaBar) := by
    have hDtotal_nonneg : 0 ≤ Dtotal := by
      simpa [Dtotal] using tsum_nonneg (fun k => hdelta_nonneg k)
    have hquot_nonneg : 0 ≤ Dtotal / (1 - alphaBar) := by
      exact div_nonneg hDtotal_nonneg hone_sub_pos.le
    by_cases hn : n = 0
    · subst n
      simpa using hquot_nonneg
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      set S : ℝ := (Finset.range (m + 1)).sum (fun k => posPart (theta k)) with hS_def
      have hsum := hsum_rec (m + 1)
      have hshift :
          (Finset.range (m + 1)).sum (fun k => posPart (theta (k + 1))) =
            (Finset.range (m + 2)).sum (fun k => posPart (theta k)) -
              posPart (theta 0) := by
        rw [Finset.sum_range_succ' (f := fun k => posPart (theta k)) (n := m + 1)]
        ring
      have hSsucc :
          (Finset.range (m + 2)).sum (fun k => posPart (theta k)) =
            S + posPart (theta (m + 1)) := by
        rw [hS_def]
        exact Finset.sum_range_succ _ _
      have hsum' :
          S + posPart (theta (m + 1)) ≤ alphaBar * S +
            (Finset.range (m + 1)).sum delta := by
        rw [hshift, hSsucc, hpos_theta_zero, sub_zero] at hsum
        simpa [S, hS_def] using hsum
      have hmain : (1 - alphaBar) * S ≤ (Finset.range (m + 1)).sum delta := by
        have hdrop : S ≤ alphaBar * S + (Finset.range (m + 1)).sum delta := by
          nlinarith [hsum', posPart_nonneg (theta (m + 1))]
        nlinarith
      have hmain_total : (1 - alphaBar) * S ≤ Dtotal :=
        le_trans hmain (hDpartial_le_total (m + 1))
      have hdiv : S ≤ Dtotal / (1 - alphaBar) := by
        exact (le_div_iff₀' hone_sub_pos).2 hmain_total
      simpa [S, hS_def] using hdiv
  have h_summable_theta : Summable (fun k : ℕ => posPart (theta k)) := by
    exact summable_of_sum_range_le (fun k => posPart_nonneg (theta k)) hS_bound
  have h_goal_i : Summable (fun k : ℕ ↦ posPart (phi k - phi (k - 1))) := by
    simpa [theta] using h_summable_theta
  set T := ∑' k, posPart (theta k) with hT_def
  set w := fun k : ℕ =>
    phi k - (Finset.range (k + 1)).sum (fun j => posPart (theta j)) with hw_def
  have hw_step (k : ℕ) : w (k + 1) ≤ w k := by
    have hcalc : w (k + 1) - w k = theta (k + 1) - posPart (theta (k + 1)) := by
      dsimp [w, theta]
      rw [Finset.sum_range_succ]
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      ring
    have hdiff : theta (k + 1) - posPart (theta (k + 1)) ≤ 0 := by
      linarith [posPart_ge_self (theta (k + 1))]
    linarith
  have hw_antitone : Antitone w := by
    intro a b hab
    induction' hab with b hb ih
    · exact le_rfl
    · exact le_trans (hw_step b) ih
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using tsum_nonneg (fun k => posPart_nonneg (theta k))
  have hpartial_le_T (k : ℕ) :
      (Finset.range (k + 1)).sum (fun j => posPart (theta j)) ≤ T := by
    simpa [T] using h_summable_theta.sum_le_tsum (Finset.range (k + 1))
      (fun i _hi => posPart_nonneg (theta i))
  have hw_lower (k : ℕ) : -T ≤ w k := by
    dsimp [w]
    have hsum := hpartial_le_T k
    have hphi := hphi_nonneg k
    linarith
  have hw_bdd : BddBelow (Set.range w) := by
    refine ⟨-T, ?_⟩
    rintro y ⟨k, rfl⟩
    exact hw_lower k
  set L := ⨅ k, w k with hL_def
  have hw_tendsto : Tendsto w atTop (𝓝 L) := by
    simpa [L] using tendsto_atTop_ciInf hw_antitone hw_bdd
  have hpartial_tendsto :
      Tendsto (fun k : ℕ => (Finset.range (k + 1)).sum
        (fun j => posPart (theta j))) atTop (𝓝 T) := by
    have ht := h_summable_theta.hasSum.tendsto_sum_nat
    have hcomp := ht.comp (tendsto_add_atTop_nat 1)
    simpa [T, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcomp
  have hphi_tendsto : Tendsto phi atTop (𝓝 (L + T)) := by
    have hadd := hw_tendsto.add hpartial_tendsto
    have heq : (fun k : ℕ =>
        w k + (Finset.range (k + 1)).sum (fun j => posPart (theta j))) = phi := by
      funext k
      dsimp [w]
      ring
    simpa [heq] using hadd
  have h_limit_nonneg : 0 ≤ L + T := by
    exact ge_of_tendsto hphi_tendsto (Filter.Eventually.of_forall hphi_nonneg)
  exact ⟨h_goal_i, ⟨L + T, h_limit_nonneg, hphi_tendsto⟩⟩

end Alvarez2004
