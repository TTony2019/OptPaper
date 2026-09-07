import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_5
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_6
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_7
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_2

namespace AttouchPeypouquetRedont2014

open ERealFunction

private theorem z_neg_mem_convexSubdifferential
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (u y : ℕ → H) (a b lam : ℝ)
    (hIFB : IsIFBTrajectory Φ psi gradPsi a b lam u y) (j : ℕ) (hj : 1 ≤ j) :
    -zSequence u y a b lam j hj ∈ subdifferential Φ (u j) := by
  obtain ⟨g, hg, hupdate⟩ := hIFB.first_update (j - 1)
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  rw [hj'] at hg hupdate
  have hupdate' :
      (1 / lam) • velocity u j hj + g + a • u (j - 1) - b • y (j - 1) = 0 := by
    simpa using hupdate
  have hg_eq : g = -zSequence u y a b lam j hj := by
    apply eq_neg_of_add_eq_zero_left
    change g + ((1 / lam) • velocity u j hj + a • u (j - 1) - b • y (j - 1)) = 0
    calc
      g + ((1 / lam) • velocity u j hj + a • u (j - 1) - b • y (j - 1)) =
          (1 / lam) • velocity u j hj + g + a • u (j - 1) - b • y (j - 1) := by abel
      _ = 0 := hupdate'
  simpa [hg_eq] using hg

private theorem subgradient_value_ne_top
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Φ : H → EReal} (hproper : ERealFunction.IsProper Φ)
    {x g : H} (hg : g ∈ subdifferential Φ x) : Φ x ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hproper.2
  have hwtop : Φ w < ⊤ := (ERealFunction.mem_dom_iff Φ w).mp hw
  intro hxtop
  have hs : Φ x + (inner ℝ g (w - x) : EReal) ≤ Φ w := by
    simpa [real_inner_comm, add_comm] using hg w
  rw [hxtop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hs
  exact (not_le_of_gt hwtop) hs

private theorem trajectory_value_finite
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis Φ Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory Φ psi gradPsi a b lam u y) (n : ℕ) :
    Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥ ∧ Θ (u (n + 1)) ≠ ⊤ ∧
      Θ (u (n + 1)) ≠ ⊥ := by
  obtain ⟨g, hg, -⟩ := hIFB.first_update n
  have hΦtop : Φ (u (n + 1)) ≠ ⊤ := subgradient_value_ne_top hH.phi_proper hg
  have hΦbot : Φ (u (n + 1)) ≠ ⊥ := hH.phi_proper.1 _
  have hΘtop : Θ (u (n + 1)) ≠ ⊤ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_top hΦtop (EReal.coe_ne_top _)
  have hΘbot : Θ (u (n + 1)) ≠ ⊥ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_bot_iff.mpr ⟨hΦbot, EReal.coe_ne_bot _⟩
  exact ⟨hΦtop, hΦbot, hΘtop, hΘbot⟩

private theorem auxiliaryG_summation_by_parts
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 2 ≤ k) :
    auxiliaryG u y a b lam q k hk =
      inner ℝ (zSequence u y a b lam k (by omega)) (u k - q) -
        ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam (i.1 - 1) (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)) (velocity u i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega)) -
        ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ
            (zSequence u y a b lam i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega) - zSequence u y a b lam (i.1 - 1) (by
                have hi := (Finset.mem_Icc.mp i.2).1
                omega))
            (velocity u i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega)) := by
  rw [auxiliaryG_defined_of_two_le]
  have hsum :
      ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)) (velocity u i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega)) =
        ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam (i.1 - 1) (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)) (velocity u i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega)) +
        ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ
            (zSequence u y a b lam i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega) - zSequence u y a b lam (i.1 - 1) (by
                have hi := (Finset.mem_Icc.mp i.2).1
                omega))
            (velocity u i.1 (by
              have hi := (Finset.mem_Icc.mp i.2).1
              omega)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi2 : 2 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
    have hinner :
        inner ℝ (zSequence u y a b lam i.1 (by omega))
            (velocity u i.1 (by omega)) =
          inner ℝ (zSequence u y a b lam (i.1 - 1) (by omega))
              (velocity u i.1 (by omega)) +
            inner ℝ
              (zSequence u y a b lam i.1 (by omega) -
                zSequence u y a b lam (i.1 - 1) (by omega))
              (velocity u i.1 (by omega)) := by
      rw [inner_sub_left]
      ring
    exact hinner
  rw [hsum]
  ring

private theorem endpoint_subgradient_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (u y : ℕ → H) (a b lam : ℝ) (q : H)
    (hfinite : ∀ n : ℕ, Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥)
    (hsub : ∀ j (hj : 1 ≤ j),
      -zSequence u y a b lam j hj ∈ subdifferential Φ (u j))
    (hqtop : Φ q ≠ ⊤) (j : ℕ) (hj : 1 ≤ j) :
    inner ℝ (zSequence u y a b lam j hj) (u j - q) ≤
      (Φ q).toReal - (Φ (u j)).toReal := by
  have hs : Φ (u j) + (inner ℝ (-zSequence u y a b lam j hj) (q - u j) : EReal) ≤ Φ q := by
    simpa [real_inner_comm, add_comm] using (hsub j hj) q
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hleftbot : Φ (u j) +
      (inner ℝ (-zSequence u y a b lam j hj) (q - u j) : ℝ) ≠ ⊥ := by
    have hΦbot : Φ (u j) ≠ ⊥ := by
      simpa only [hj'] using (hfinite (j - 1)).2
    exact EReal.add_ne_bot_iff.mpr ⟨hΦbot, EReal.coe_ne_bot _⟩
  have hsr := EReal.toReal_le_toReal hs hleftbot hqtop
  rw [EReal.toReal_add (by simpa only [hj'] using (hfinite (j - 1)).1)
    (by simpa only [hj'] using (hfinite (j - 1)).2)
    (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsr
  have hinner : inner ℝ (-zSequence u y a b lam j hj) (q - u j) =
      inner ℝ (zSequence u y a b lam j hj) (u j - q) := by
    rw [inner_neg_left, show q - u j = -(u j - q) by abel, inner_neg_right]
    ring
  rw [hinner] at hsr
  norm_num at hsr
  linarith

private theorem predecessor_subgradient_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (u y : ℕ → H) (a b lam : ℝ)
    (hfinite : ∀ n : ℕ, Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥)
    (hsub : ∀ j (hj : 1 ≤ j),
      -zSequence u y a b lam j hj ∈ subdifferential Φ (u j))
    (i : ℕ) (hi : 2 ≤ i) :
    -inner ℝ (zSequence u y a b lam (i - 1) (by omega))
        (velocity u i (by omega)) ≤
      (Φ (u i)).toReal - (Φ (u (i - 1))).toReal := by
  have hs : Φ (u (i - 1)) +
      (inner ℝ (-zSequence u y a b lam (i - 1) (by omega)) (u i - u (i - 1)) : EReal) ≤
      Φ (u i) := by
    rw [real_inner_comm, add_comm]
    exact (hsub (i - 1) (by omega)) (u i)
  have hleftbot : Φ (u (i - 1)) +
      (inner ℝ (-zSequence u y a b lam (i - 1) (by omega))
        (u i - u (i - 1)) : ℝ) ≠ ⊥ := by
    have hi' : i - 2 + 1 = i - 1 := by omega
    have hΦbot : Φ (u (i - 1)) ≠ ⊥ := by
      simpa only [hi'] using (hfinite (i - 2)).2
    exact EReal.add_ne_bot_iff.mpr ⟨hΦbot, EReal.coe_ne_bot _⟩
  have hrighttop : Φ (u i) ≠ ⊤ := by
    have hi' : i - 1 + 1 = i := by omega
    simpa only [hi'] using (hfinite (i - 1)).1
  have hsr := EReal.toReal_le_toReal hs hleftbot hrighttop
  rw [EReal.toReal_add (by
      have hi' : i - 2 + 1 = i - 1 := by omega
      simpa only [hi'] using (hfinite (i - 2)).1)
    (by
      have hi' : i - 2 + 1 = i - 1 := by omega
      simpa only [hi'] using (hfinite (i - 2)).2)
    (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsr
  change -inner ℝ (zSequence u y a b lam (i - 1) (by omega))
      (u i - u (i - 1)) ≤ _
  rw [inner_neg_left] at hsr
  norm_num at hsr
  linarith

private theorem theta_descent_previous_step
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis Φ Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory Φ psi gradPsi a b lam u y)
    (i : ℕ) (hi : 2 ≤ i) :
    (Θ (u i)).toReal - (Θ (u (i - 1))).toReal +
        (1 / lam - Lpsi / 2) * ‖velocity u i (by omega)‖ ^ 2 ≤
      -(1 / lam) * inner ℝ (zeta y (i - 1) (by omega))
        (velocity u i (by omega)) := by
  have hfinite (n : ℕ) :=
    trajectory_value_finite Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB n
  obtain ⟨g, hg, hu⟩ := hIFB.first_update (i - 1)
  have hi' : i - 1 + 1 = i := by omega
  rw [hi'] at hg hu
  have hΦi : Φ (u i) ≠ ⊤ ∧ Φ (u i) ≠ ⊥ := by
    exact ⟨by simpa only [hi'] using (hfinite (i - 1)).1,
      by simpa only [hi'] using (hfinite (i - 1)).2.1⟩
  have hΦprev : Φ (u (i - 1)) ≠ ⊤ ∧ Φ (u (i - 1)) ≠ ⊥ := by
    have hprev : i - 2 + 1 = i - 1 := by omega
    exact ⟨by simpa only [hprev] using (hfinite (i - 2)).1,
      by simpa only [hprev] using (hfinite (i - 2)).2.1⟩
  have hsr := EReal.toReal_le_toReal
      (by simpa [real_inner_comm, add_comm] using hg (u (i - 1)))
    (EReal.add_ne_bot_iff.mpr ⟨hΦi.2, EReal.coe_ne_bot _⟩) hΦprev.1
  rw [EReal.toReal_add hΦi.1 hΦi.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsr
  have hg_eq : g = -((1 / lam) • velocity u i (by omega) +
      a • u (i - 1) - b • y (i - 1)) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      g + ((1 / lam) • velocity u i (by omega) + a • u (i - 1) - b • y (i - 1)) =
          (1 / lam) • velocity u i (by omega) + g + a • u (i - 1) - b • y (i - 1) := by abel
      _ = 0 := by simpa [velocity] using hu
  rw [hg_eq] at hsr
  have hvel : velocity u i (by omega) = u i - u (i - 1) :=
    velocity_eq_sub_of_one_le u i (by omega)
  have hinner : inner ℝ (-((1 / lam) • velocity u i (by omega) +
      a • u (i - 1) - b • y (i - 1))) (u (i - 1) - u i) =
      (1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
        inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega)) := by
    rw [show u (i - 1) - u i = -velocity u i (by omega) by rw [hvel]; abel]
    simp only [inner_neg_left, inner_neg_right, neg_neg]
    rw [inner_sub_left, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
    rw [add_sub_assoc, ← inner_sub_left]
  rw [hinner] at hsr
  norm_num at hsr
  have hsr' : (Φ (u i)).toReal +
      ((1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
        inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega))) ≤
      (Φ (u (i - 1))).toReal := by
    simpa [hvel] using hsr
  have h35 : (Φ (u i)).toReal - (Φ (u (i - 1))).toReal +
      (1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
      inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega)) ≤ 0 := by
    linarith
  have hd := descent_lemma psi gradPsi Lpsi hH.psi_differentiable hH.psi_gradient
    hH.psi_lipschitz (u (i - 1)) (u i)
  have hsecond := hIFB.second_update (i - 2)
  have hggrad : gradPsi (u (i - 1)) = a • u (i - 1) - b • y (i - 1) -
      (1 / lam) • zeta y (i - 1) (by omega) := by
    have hzero : gradPsi (u (i - 1)) +
        ((1 / lam) • zeta y (i - 1) (by omega) - a • u (i - 1) + b • y (i - 1)) = 0 := by
      calc
        gradPsi (u (i - 1)) + ((1 / lam) • zeta y (i - 1) (by omega) -
            a • u (i - 1) + b • y (i - 1)) =
            (1 / lam) • zeta y (i - 1) (by omega) + gradPsi (u (i - 1)) -
              a • u (i - 1) + b • y (i - 1) := by abel
        _ = 0 := by
          have hidx : i - 2 + 1 = i - 1 := by omega
          simpa only [hidx, Nat.sub_sub] using hsecond
    calc
      gradPsi (u (i - 1)) = -((1 / lam) • zeta y (i - 1) (by omega) -
          a • u (i - 1) + b • y (i - 1)) := eq_neg_of_add_eq_zero_left hzero
      _ = a • u (i - 1) - b • y (i - 1) -
          (1 / lam) • zeta y (i - 1) (by omega) := by abel
  rw [hggrad] at hd
  simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at hd
  have h36 : psi (u i) - psi (u (i - 1)) - (Lpsi / 2) *
      ‖velocity u i (by omega)‖ ^ 2 -
      inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega)) ≤
      -(1 / lam) * inner ℝ (zeta y (i - 1) (by omega)) (velocity u i (by omega)) := by
    have hab : inner ℝ (a • u (i - 1) - b • y (i - 1))
        (u i - u (i - 1)) =
        a * inner ℝ (u (i - 1)) (u i - u (i - 1)) -
          b * inner ℝ (y (i - 1)) (u i - u (i - 1)) := by
      simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
    rw [hvel]
    rw [hab]
    linarith [hd]
  have hΘi : (Θ (u i)).toReal = (Φ (u i)).toReal + psi (u i) := by
    rw [hH.theta_eq, EReal.toReal_add hΦi.1 hΦi.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp
  have hΘprev : (Θ (u (i - 1))).toReal =
      (Φ (u (i - 1))).toReal + psi (u (i - 1)) := by
    rw [hH.theta_eq, EReal.toReal_add hΦprev.1 hΦprev.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp
  rw [hΘi, hΘprev]
  linarith [h35, h36]
/-
  have hfinite (n : ℕ) :
      Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥ ∧ Θ (u (n + 1)) ≠ ⊤ ∧
        Θ (u (n + 1)) ≠ ⊥ :=
    trajectory_value_finite Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB n
  obtain ⟨g, hg, hu⟩ := hIFB.first_update (i - 1)
  have hi' : i - 1 + 1 = i := by omega
  rw [hi'] at hg hu
  have hs := hg.2 (u (i - 1))
  have hΦi : Φ (u i) ≠ ⊤ ∧ Φ (u i) ≠ ⊥ := by
    exact ⟨by simpa only [hi'] using (hfinite (i - 1)).1,
      by simpa only [hi'] using (hfinite (i - 1)).2.1⟩
  have hΦprev : Φ (u (i - 1)) ≠ ⊤ ∧ Φ (u (i - 1)) ≠ ⊥ := by
    have hprev : i - 2 + 1 = i - 1 := by omega
    exact ⟨by simpa only [hprev] using (hfinite (i - 2)).1,
      by simpa only [hprev] using (hfinite (i - 2)).2.1⟩
  have hsr := EReal.toReal_le_toReal hs
    (EReal.add_ne_bot_iff.mpr ⟨hΦi.2, EReal.coe_ne_bot _⟩) hΦprev.1
  rw [EReal.toReal_add hΦi.1 hΦi.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsr
  have hg_eq : g = -((1 / lam) • velocity u i (by omega) +
      a • u (i - 1) - b • y (i - 1)) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      g + ((1 / lam) • velocity u i (by omega) + a • u (i - 1) - b • y (i - 1)) =
          (1 / lam) • velocity u i (by omega) + g + a • u (i - 1) - b • y (i - 1) := by abel
      _ = 0 := by simpa [velocity] using hu
  rw [hg_eq] at hsr
  have hvel : velocity u i (by omega) = u i - u (i - 1) :=
    velocity_eq_sub_of_one_le u i (by omega)
  have h35 : (Φ (u i)).toReal - (Φ (u (i - 1))).toReal +
      (1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
      inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega)) ≤ 0 := by
    have hinner : inner ℝ (-((1 / lam) • velocity u i (by omega) +
        a • u (i - 1) - b • y (i - 1))) (u (i - 1) - u i) =
        (1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
          inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega)) := by
      rw [show u (i - 1) - u i = -velocity u i (by omega) by rw [hvel]; abel]
      simp only [inner_neg_left, inner_neg_right, neg_neg]
      rw [inner_sub_left, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      rw [add_sub_assoc, ← inner_sub_left]
    rw [hinner] at hsr
    norm_num at hsr
    rw [hvel] at hsr ⊢
    linarith
  have hd := descent_lemma psi gradPsi Lpsi hH.psi_differentiable hH.psi_gradient
    hH.psi_lipschitz (u (i - 1)) (u i)
  have hsecond := hIFB.second_update (i - 2)
  have hggrad : gradPsi (u (i - 1)) = a • u (i - 1) - b • y (i - 1) -
      (1 / lam) • zeta y (i - 1) (by omega) := by
    have hzero : gradPsi (u (i - 1)) +
        ((1 / lam) • zeta y (i - 1) (by omega) - a • u (i - 1) + b • y (i - 1)) = 0 := by
      calc
        gradPsi (u (i - 1)) + ((1 / lam) • zeta y (i - 1) (by omega) -
            a • u (i - 1) + b • y (i - 1)) =
            (1 / lam) • zeta y (i - 1) (by omega) + gradPsi (u (i - 1)) -
              a • u (i - 1) + b • y (i - 1) := by abel
        _ = 0 := by
          have hidx : i - 2 + 1 = i - 1 := by omega
          simpa only [hidx, Nat.sub_sub] using hsecond
    calc
      gradPsi (u (i - 1)) = -((1 / lam) • zeta y (i - 1) (by omega) -
          a • u (i - 1) + b • y (i - 1)) := eq_neg_of_add_eq_zero_left hzero
      _ = a • u (i - 1) - b • y (i - 1) -
          (1 / lam) • zeta y (i - 1) (by omega) := by abel
  rw [hggrad] at hd
  rw [hvel] at hd
  simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at hd
  have h36 : psi (u i) - psi (u (i - 1)) - (Lpsi / 2) *
      ‖velocity u i (by omega)‖ ^ 2 -
      inner ℝ (a • u (i - 1) - b • y (i - 1)) (velocity u i (by omega)) ≤
      -(1 / lam) * inner ℝ (zeta y (i - 1) (by omega)) (velocity u i (by omega)) := by
    rw [hvel]
    linarith [hd]
  have hΘi : (Θ (u i)).toReal = (Φ (u i)).toReal + psi (u i) := by
    rw [hH.theta_eq, EReal.toReal_add hΦi.1 hΦi.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp
  have hΘprev : (Θ (u (i - 1))).toReal =
      (Φ (u (i - 1))).toReal + psi (u (i - 1)) := by
    rw [hH.theta_eq, EReal.toReal_add hΦprev.1 hΦprev.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp
  rw [hΘi, hΘprev]
  linarith [h35, h36]
-/

private theorem z_difference_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis Φ Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory Φ psi gradPsi a b lam u y)
    (i : ℕ) (hi : 2 ≤ i) :
    -inner ℝ (zSequence u y a b lam i (by omega) -
        zSequence u y a b lam (i - 1) (by omega)) (velocity u i (by omega)) ≤
      (b * lam ^ 2 * Lpsi - (a + 2 * b) * lam - 1) / (2 * lam) *
          ‖velocity u i (by omega)‖ ^ 2 +
        (1 - a * lam) / (2 * lam) * ‖velocity u (i - 1) (by omega)‖ ^ 2 +
        b * lam * ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal) := by
  have hpos : 0 < 1 - a * lam := by
    have hlt : lam < 1 / a := lt_of_lt_of_le hH.step_lt (min_le_left _ _)
    have hla : lam * a < 1 := (lt_div_iff₀ hH.a_pos).mp (by simpa [mul_comm] using hlt)
    nlinarith [show a * lam = lam * a by ring]
  have hden : 0 < 2 * lam := by nlinarith [hH.step_pos]
  have hC : 0 ≤ (1 - a * lam) / (2 * lam) :=
    div_nonneg (le_of_lt hpos) (le_of_lt hden)
  have hvec : zSequence u y a b lam i (by omega) -
      zSequence u y a b lam (i - 1) (by omega) =
      (1 / lam) • (velocity u i (by omega) - velocity u (i - 1) (by omega)) +
        a • velocity u (i - 1) (by omega) - b • zeta y (i - 1) (by omega) := by
    simp only [zSequence, velocity, zeta]
    have h1 : i - 1 - 1 = i - 2 := by omega
    rw [h1]
    module
  rw [hvec]
  have hpair : -inner ℝ ((1 / lam) •
      (velocity u i (by omega) - velocity u (i - 1) (by omega)) +
        a • velocity u (i - 1) (by omega) - b • zeta y (i - 1) (by omega))
      (velocity u i (by omega)) =
      -(1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
        ((1 - a * lam) / lam) *
          inner ℝ (velocity u (i - 1) (by omega)) (velocity u i (by omega)) +
        b * inner ℝ (zeta y (i - 1) (by omega)) (velocity u i (by omega)) := by
    rw [inner_sub_left, inner_add_left, inner_smul_left, inner_sub_left,
      inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [hH.step_pos.ne']
    ring
  rw [hpair]
  have hyoung0 : 2 * inner ℝ (velocity u (i - 1) (by omega)) (velocity u i (by omega)) ≤
      ‖velocity u (i - 1) (by omega)‖ ^ 2 + ‖velocity u i (by omega)‖ ^ 2 := by
    have hn := sq_nonneg (‖velocity u (i - 1) (by omega) - velocity u i (by omega)‖)
    rw [norm_sub_sq_real] at hn
    nlinarith
  have hyoung : ((1 - a * lam) / lam) *
      inner ℝ (velocity u (i - 1) (by omega)) (velocity u i (by omega)) ≤
      (1 - a * lam) / (2 * lam) * ‖velocity u (i - 1) (by omega)‖ ^ 2 +
        (1 - a * lam) / (2 * lam) * ‖velocity u i (by omega)‖ ^ 2 := by
    have hfac : 0 ≤ (1 - a * lam) / lam :=
      div_nonneg (le_of_lt hpos) (le_of_lt hH.step_pos)
    have hmul := mul_le_mul_of_nonneg_left hyoung0 hfac
    have hfac_eq : (1 - a * lam) / lam =
        2 * ((1 - a * lam) / (2 * lam)) := by
      field_simp [hH.step_pos.ne']
    rw [hfac_eq] at hmul
    nlinarith [hmul]
  have htheta := theta_descent_previous_step Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB i hi
  have hzeta : b * inner ℝ (zeta y (i - 1) (by omega)) (velocity u i (by omega)) ≤
      b * lam * ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal) -
        b * lam * (1 / lam - Lpsi / 2) * ‖velocity u i (by omega)‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left htheta
      (le_of_lt (mul_pos hH.b_pos hH.step_pos))
    have hleft : b * lam * ((Θ (u i)).toReal - (Θ (u (i - 1))).toReal +
        (1 / lam - Lpsi / 2) * ‖velocity u i (by omega)‖ ^ 2) =
        b * lam * ((Θ (u i)).toReal - (Θ (u (i - 1))).toReal) +
          b * lam * (1 / lam - Lpsi / 2) * ‖velocity u i (by omega)‖ ^ 2 := by ring
    have hright : b * lam * (-(1 / lam) *
        inner ℝ (zeta y (i - 1) (by omega)) (velocity u i (by omega))) =
        -b * inner ℝ (zeta y (i - 1) (by omega)) (velocity u i (by omega)) := by
      field_simp [hH.step_pos.ne']
    rw [hleft, hright] at hmul
    linarith [hmul]
  have hcoef :
      -(1 / lam) * ‖velocity u i (by omega)‖ ^ 2 +
        (1 - a * lam) / (2 * lam) * ‖velocity u i (by omega)‖ ^ 2 -
        b * lam * (1 / lam - Lpsi / 2) * ‖velocity u i (by omega)‖ ^ 2 =
      (b * lam ^ 2 * Lpsi - (a + 2 * b) * lam - 1) / (2 * lam) *
        ‖velocity u i (by omega)‖ ^ 2 := by
    field_simp [hH.step_pos.ne']
    ring
  rw [← hcoef]
  linarith

private theorem velocity_Icc_sum_le_tsum {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (hsq : Summable (fun n : ℕ ↦ ‖u (n + 1) - u n‖ ^ 2))
    (k : ℕ) (hk : 2 ≤ k) :
    ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤
      ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2 := by
  let f : ℕ → ℝ := fun n ↦ ‖u (n + 1) - u n‖ ^ 2
  have hsum : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 (k - 1), f n := by
    apply Finset.sum_bij (fun i _ ↦ i.1 - 1)
    · intro i hi
      apply Finset.mem_Icc.mpr
      have hii := Finset.mem_Icc.mp i.2
      omega
    · intro i hi j hj heq
      apply Subtype.ext
      have hii := Finset.mem_Icc.mp i.2
      have hjj := Finset.mem_Icc.mp j.2
      omega
    · intro n hn
      have hnn := Finset.mem_Icc.mp hn
      refine ⟨⟨n + 1, Finset.mem_Icc.mpr (by omega)⟩,
        Finset.mem_attach _ _, ?_⟩
      simp
    · intro i hi
      have hi2 : 2 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      rw [velocity_eq_sub_of_one_le]
      simp only [f]
      have heq : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel (by omega)
      rw [heq]
  rw [hsum]
  exact hsq.sum_le_tsum _ (fun n _ ↦ sq_nonneg _)

private theorem predecessor_velocity_Icc_sum_le_tsum {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (hsq : Summable (fun n : ℕ ↦ ‖u (n + 1) - u n‖ ^ 2))
    (k : ℕ) (hk : 2 ≤ k) :
    ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤
      ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2 := by
  let f : ℕ → ℝ := fun n ↦ ‖u (n + 1) - u n‖ ^ 2
  have hsum : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 =
      ∑ n ∈ Finset.Icc 0 (k - 2), f n := by
    apply Finset.sum_bij (fun i _ ↦ i.1 - 2)
    · intro i hi
      apply Finset.mem_Icc.mpr
      have hii := Finset.mem_Icc.mp i.2
      omega
    · intro i hi j hj heq
      apply Subtype.ext
      have hii := Finset.mem_Icc.mp i.2
      have hjj := Finset.mem_Icc.mp j.2
      omega
    · intro n hn
      have hnn := Finset.mem_Icc.mp hn
      refine ⟨⟨n + 2, Finset.mem_Icc.mpr (by omega)⟩,
        Finset.mem_attach _ _, ?_⟩
      simp
    · intro i hi
      have hi2 : 2 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      rw [velocity_eq_sub_of_one_le]
      simp only [f]
      have heq : i.1 - 2 + 1 = i.1 - 1 := by omega
      rw [heq]
      simp only [Nat.sub_sub]
  rw [hsum]
  exact hsq.sum_le_tsum _ (fun n _ ↦ sq_nonneg _)

/-- Proposition 4: `G_k(q)` is bounded above for `q ∈ dom Φ`. -/
theorem proposition4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (u y : ℕ → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis Φ Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory Φ psi gradPsi a b lam u y) (q : H)
    (hq : q ∈ ERealFunction.dom Φ) :
    ∃ M : ℝ, ∀ k (hk : 2 ≤ k), auxiliaryG u y a b lam q k hk ≤ M := by
  have hfinite (n : ℕ) :
      Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥ ∧ Θ (u (n + 1)) ≠ ⊤ ∧
        Θ (u (n + 1)) ≠ ⊥ :=
    trajectory_value_finite Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB n
  have hsub (j : ℕ) (hj : 1 ≤ j) :
      -zSequence u y a b lam j hj ∈ subdifferential Φ (u j) :=
    z_neg_mem_convexSubdifferential Φ psi gradPsi u y a b lam hIFB j hj
  obtain ⟨_, hsq, _⟩ := proposition2 Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB
  obtain ⟨m, hm⟩ := hH.theta_bounded_below
  classical
  have htelPhi : ∀ k : ℕ, 2 ≤ k → ∑ i ∈ Finset.Icc 2 k,
      ((Φ (u i)).toReal - (Φ (u (i - 1))).toReal) =
        (Φ (u k)).toReal - (Φ (u 1)).toReal := by
    intro k hk
    refine Nat.le_induction ?_ ?_ k hk
    · norm_num
    · intro n hn ih
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      norm_num
  have htelTheta : ∀ k : ℕ, 2 ≤ k → ∑ i ∈ Finset.Icc 2 k,
      ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal) =
        (Θ (u 1)).toReal - (Θ (u k)).toReal := by
    intro k hk
    refine Nat.le_induction ?_ ?_ k hk
    · norm_num
    · intro n hn ih
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      norm_num
  have hqtop : Φ q ≠ ⊤ := ne_of_lt ((ERealFunction.mem_dom_iff Φ q).mp hq)
  let A : ℝ := (b * lam ^ 2 * Lpsi - (a + 2 * b) * lam - 1) / (2 * lam)
  let B : ℝ := (1 - a * lam) / (2 * lam)
  let S : ℝ := ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2
  refine ⟨(Φ q).toReal - (Φ (u 1)).toReal +
      b * lam * ((Θ (u 1)).toReal - m) + (|A| + |B|) * S, ?_⟩
  intro k hk
  have hS : 0 ≤ S := tsum_nonneg (fun n ↦ sq_nonneg _)
  have hsum1 : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ S :=
    velocity_Icc_sum_le_tsum u hsq k hk
  have hsum0 : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ S :=
    predecessor_velocity_Icc_sum_le_tsum u hsq k hk
  have hend := endpoint_subgradient_bound Φ u y a b lam q
    (fun n ↦ ⟨(hfinite n).1, (hfinite n).2.1⟩) hsub hqtop k (by omega)
  have hpred : -∑ i ∈ (Finset.Icc 2 k).attach,
      inner ℝ (zSequence u y a b lam (i.1 - 1) (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega))
        (velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)) ≤
      (Φ (u k)).toReal - (Φ (u 1)).toReal := by
    calc
      -∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam (i.1 - 1) (by
            have hi := (Finset.mem_Icc.mp i.2).1; omega))
            (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) =
          ∑ i ∈ (Finset.Icc 2 k).attach, -inner ℝ
            (zSequence u y a b lam (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega))
            (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) := by
              rw [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ (Finset.Icc 2 k).attach,
          ((Φ (u i.1)).toReal - (Φ (u (i.1 - 1))).toReal) := by
        apply Finset.sum_le_sum
        intro i hi
        exact predecessor_subgradient_bound Φ u y a b lam
          (fun n ↦ ⟨(hfinite n).1, (hfinite n).2.1⟩) hsub i.1
          ((Finset.mem_Icc.mp i.2).1)
      _ = _ := by
        have hattach : ∑ i ∈ (Finset.Icc 2 k).attach,
            ((Φ (u i.1)).toReal - (Φ (u (i.1 - 1))).toReal) =
            ∑ i ∈ Finset.Icc 2 k,
              ((Φ (u i)).toReal - (Φ (u (i - 1))).toReal) := by
          simpa only using Finset.sum_attach (Finset.Icc 2 k)
            (fun i : ℕ ↦ ((Φ (u i)).toReal - (Φ (u (i - 1))).toReal))
        rw [hattach, htelPhi k hk]
  have hdiff : -∑ i ∈ (Finset.Icc 2 k).attach,
      inner ℝ (zSequence u y a b lam i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega) - zSequence u y a b lam (i.1 - 1) (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega))
        (velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)) ≤
      A * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2 +
        B * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 +
        b * lam * ((Θ (u 1)).toReal - (Θ (u k)).toReal) := by
    calc
      -∑ i ∈ (Finset.Icc 2 k).attach, inner ℝ
          (zSequence u y a b lam i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega) -
            zSequence u y a b lam (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega))
          (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) =
          ∑ i ∈ (Finset.Icc 2 k).attach, -inner ℝ
            (zSequence u y a b lam i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega) -
              zSequence u y a b lam (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega))
            (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) := by
              rw [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ (Finset.Icc 2 k).attach,
          (A * ‖velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)‖ ^ 2 +
            B * ‖velocity u (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega)‖ ^ 2 +
            b * lam * ((Θ (u (i.1 - 1))).toReal - (Θ (u i.1)).toReal)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [A, B] using z_difference_bound Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB i.1
          ((Finset.mem_Icc.mp i.2).1)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
        have hattach : ∑ i ∈ (Finset.Icc 2 k).attach,
            ((Θ (u (i.1 - 1))).toReal - (Θ (u i.1)).toReal) =
            ∑ i ∈ Finset.Icc 2 k,
              ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal) := by
          simpa only using Finset.sum_attach (Finset.Icc 2 k)
            (fun i : ℕ ↦ ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal))
        rw [hattach, htelTheta k hk]
  have hmreal : m ≤ (Θ (u k)).toReal := by
    have hkm1 : k - 1 + 1 = k := by omega
    exact EReal.toReal_le_toReal (hm (u k))
      (EReal.coe_ne_bot m)
      (by simpa only [hkm1] using (hfinite (k - 1)).2.2.1)
  have htheta : b * lam * ((Θ (u 1)).toReal - (Θ (u k)).toReal) ≤
      b * lam * ((Θ (u 1)).toReal - m) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact le_of_lt (mul_pos hH.b_pos hH.step_pos)
  have hA : A * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ |A| * S := by
    calc
      A * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 ≤
          |A| * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ ≤ |A| * S := mul_le_mul_of_nonneg_left hsum1 (abs_nonneg A)
  have hB : B * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ |B| * S := by
    calc
      B * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 ≤
          |B| * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ ≤ |B| * S := mul_le_mul_of_nonneg_left hsum0 (abs_nonneg B)
  rw [auxiliaryG_summation_by_parts]
  linarith

end AttouchPeypouquetRedont2014
