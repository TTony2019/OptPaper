import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_4
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_5
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_6
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_thm_2

namespace AttouchPeypouquetRedont2014

open ERealFunction

/-- Positivity of the coercive coefficient in the energy estimate of Proposition 2. -/
theorem proposition2_beta_pos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (Ψ : H → ℝ) (gradPsi : H → H) (a b lam L : ℝ)
    (hH : IFBHypothesis Φ Θ Ψ gradPsi a b lam L) :
    0 < 1 / lam - L / 2 + 1 / (b * lam ^ 2) - 2 * gamma a b lam := by
  have hnum : 0 < 2 * (a + b) := by nlinarith [hH.a_pos, hH.b_pos]
  have hupper : lam < 2 * (a + b) / (b * L) :=
    lt_of_lt_of_le hH.step_lt (min_le_right _ _)
  have hquot_pos : 0 < 2 * (a + b) / (b * L) := lt_trans hH.step_pos hupper
  have hbL_pos : 0 < b * L := by
    by_contra h
    have hnonpos : b * L ≤ 0 := le_of_not_gt h
    have : 2 * (a + b) / (b * L) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (le_of_lt hnum) hnonpos
    linarith
  have hstrict : b * L * lam < 2 * (a + b) :=
    by simpa [mul_comm] using (lt_div_iff₀ hbL_pos).mp hupper
  have hden_pos : 0 < 2 * b * lam := by nlinarith [hH.b_pos, hH.step_pos]
  have hratio :
      1 / lam - L / 2 + 1 / (b * lam ^ 2) - 2 * gamma a b lam =
        (2 * (a + b) - b * lam * L) / (2 * b * lam) := by
    have hb_ne : b ≠ 0 := ne_of_gt hH.b_pos
    have hlam_ne : lam ≠ 0 := ne_of_gt hH.step_pos
    rw [gamma]
    field_simp
    ring
  rw [hratio]
  apply div_pos
  · nlinarith
  · exact hden_pos

private theorem descent_summable_real (E q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hbelow : BddBelow (Set.range E)) (hdesc : ∀ n, E (n + 1) + q n ≤ E n) :
    Antitone E ∧ (∃ l : ℝ, Filter.Tendsto E Filter.atTop (nhds l)) ∧ Summable q := by
  have hbdd := hbelow
  obtain ⟨lower, hlower⟩ := hbelow
  have hstep : ∀ n, E (n + 1) ≤ E n := by
    intro n
    linarith [hdesc n, hq n]
  have hanti : Antitone E := by
    intro m n hmn
    induction hmn with
    | refl => rfl
    | step hmn ih => exact le_trans (hstep _) ih
  have hconv : ∃ l : ℝ, Filter.Tendsto E Filter.atTop (nhds l) :=
    ⟨⨅ n, E n, tendsto_atTop_ciInf hanti hbdd⟩
  have htel : ∀ n, (∑ i ∈ Finset.range n, q i) + E n ≤ E 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hdesc n]
  have hsumbdd : ∀ n, ∑ i ∈ Finset.range n, q i ≤ E 0 - lower := by
    intro n
    have hEn : lower ≤ E n := hlower ⟨n, rfl⟩
    linarith [htel n]
  exact ⟨hanti, hconv, summable_of_sum_range_le hq hsumbdd⟩

private theorem subgradient_value_ne_top {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Φ : H → EReal} (hproper : ERealFunction.IsProper Φ)
    {x g : H} (hg : g ∈ subdifferential Φ x) : Φ x ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hproper.2
  have hwtop : Φ w < ⊤ := (ERealFunction.mem_dom_iff Φ w).mp hw
  intro hxtop
  have hs : Φ x + (inner ℝ g (w - x) : EReal) ≤ Φ w := by
    simpa [real_inner_comm, add_comm] using hg w
  rw [hxtop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hs
  exact (not_le_of_gt hwtop) hs

private theorem trajectory_phi_theta_finite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Φ Θ : H → EReal) (Ψ : H → ℝ) (gradPsi : H → H)
    (a b lam L : ℝ) (u y : ℕ → H) (hH : IFBHypothesis Φ Θ Ψ gradPsi a b lam L)
    (hIFB : IsIFBTrajectory Φ Ψ gradPsi a b lam u y) (n : ℕ) :
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

/-- Proposition 2: IFB mechanical energy decreases, velocities are square-summable, and both
energy and objective have the same limit. -/
theorem proposition2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (Ψ : H → ℝ) (gradPsi : H → H) (a b lam L : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis Φ Θ Ψ gradPsi a b lam L) (hIFB : IsIFBTrajectory Φ Ψ gradPsi a b lam u y) :
    (∀ k : ℕ,
      mechanicalEnergy Θ u (gamma a b lam) (k + 2) (by omega) ≤
        mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega)) ∧
    Summable (fun k : ℕ ↦ ‖u (k + 1) - u k‖ ^ 2) ∧
    ∃ e : EReal,
      Filter.Tendsto
        (fun k : ℕ ↦ mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega))
        Filter.atTop (nhds e) ∧
      Filter.Tendsto (fun k : ℕ ↦ Θ (u (k + 1))) Filter.atTop (nhds e) := by
  have hbeta : 0 < 1 / lam - L / 2 + 1 / (b * lam ^ 2) - 2 * gamma a b lam :=
    proposition2_beta_pos Φ Θ Ψ gradPsi a b lam L hH
  have hgamma : 0 < gamma a b lam := gamma_pos Φ Θ Ψ gradPsi a b lam L hH
  have hfirst (k : ℕ) :
      ∃ g ∈ subdifferential Φ (u (k + 2)),
        (1 / lam) • (u (k + 2) - u (k + 1)) + g + a • u (k + 1) - b • y (k + 1) = 0 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIFB.first_update (k + 1)
  have hsecond (k : ℕ) :
      (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) - a • u (k + 1) +
          b • y (k + 1) = 0 :=
    hIFB.second_update k
  have hfinite (n : ℕ) :
      Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥ ∧ Θ (u (n + 1)) ≠ ⊤ ∧
        Θ (u (n + 1)) ≠ ⊥ :=
    trajectory_phi_theta_finite Φ Θ Ψ gradPsi a b lam L u y hH hIFB n
  have hsub (k : ℕ) :
      ∃ g, g ∈ subdifferential Φ (u (k + 2)) ∧
        (1 / lam) • (u (k + 2) - u (k + 1)) + g + a • u (k + 1) -
            b • y (k + 1) = 0 := by
    obtain ⟨g, hg, hu⟩ := hfirst k
    exact ⟨g, hg, hu⟩
  have h35 (k : ℕ) :
      (Φ (u (k + 2))).toReal - (Φ (u (k + 1))).toReal +
          (1 / lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 +
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1)) ≤ 0 := by
    obtain ⟨g, hg, hu⟩ := hsub k
    have hs : Φ (u (k + 2)) + (inner ℝ g (u (k + 1) - u (k + 2)) : EReal) ≤
        Φ (u (k + 1)) := by
      simpa [real_inner_comm, add_comm] using hg (u (k + 1))
    have hleftbot : Φ (u (k + 2)) +
        (inner ℝ g (u (k + 1) - u (k + 2)) : ℝ) ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨(hfinite (k + 1)).2.1, EReal.coe_ne_bot _⟩
    have hsr := EReal.toReal_le_toReal hs hleftbot (hfinite k).1
    rw [EReal.toReal_add (hfinite (k + 1)).1 (hfinite (k + 1)).2.1
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsr
    have hg_eq : g = - ((1 / lam) • (u (k + 2) - u (k + 1)) +
        a • u (k + 1) - b • y (k + 1)) := by
      apply eq_neg_of_add_eq_zero_left
      calc
        g + ((1 / lam) • (u (k + 2) - u (k + 1)) + a • u (k + 1) -
            b • y (k + 1)) =
            (1 / lam) • (u (k + 2) - u (k + 1)) + g + a • u (k + 1) -
              b • y (k + 1) := by abel
        _ = 0 := hu
    rw [hg_eq] at hsr
    have hinner : inner ℝ (- ((1 / lam) • (u (k + 2) - u (k + 1)) +
        a • u (k + 1) - b • y (k + 1))) (u (k + 1) - u (k + 2)) =
        (1 / lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 +
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1)) := by
      rw [show u (k + 1) - u (k + 2) = -(u (k + 2) - u (k + 1)) by abel]
      simp only [inner_neg_left, inner_neg_right, neg_neg]
      rw [inner_sub_left, inner_add_left, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      rw [add_sub_assoc, ← inner_sub_left]
    rw [hinner] at hsr
    norm_num at hsr
    have hsr' : (Φ (u (k + 2))).toReal +
        ((1 / lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 +
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1))) ≤ (Φ (u (k + 1))).toReal := by
      simpa [Nat.add_assoc] using hsr
    linarith
  have h36 (k : ℕ) :
      Ψ (u (k + 2)) - Ψ (u (k + 1)) - (L / 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1)) ≤
        -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) := by
    have hd := descent_lemma Ψ gradPsi L hH.psi_differentiable hH.psi_gradient
      hH.psi_lipschitz (u (k + 1)) (u (k + 2))
    have hg : gradPsi (u (k + 1)) = a • u (k + 1) - b • y (k + 1) -
        (1 / lam) • (y (k + 1) - y k) := by
      have hz : gradPsi (u (k + 1)) +
          ((1 / lam) • (y (k + 1) - y k) - a • u (k + 1) + b • y (k + 1)) = 0 := by
        calc
          gradPsi (u (k + 1)) +
              ((1 / lam) • (y (k + 1) - y k) - a • u (k + 1) + b • y (k + 1)) =
              (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) -
                a • u (k + 1) + b • y (k + 1) := by abel
          _ = 0 := hsecond k
      calc
        gradPsi (u (k + 1)) = - ((1 / lam) • (y (k + 1) - y k) -
            a • u (k + 1) + b • y (k + 1)) := eq_neg_of_add_eq_zero_left hz
        _ = a • u (k + 1) - b • y (k + 1) -
            (1 / lam) • (y (k + 1) - y k) := by abel
    rw [hg] at hd
    simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at hd
    have hr : inner ℝ (a • u (k + 1) - b • y (k + 1))
        (u (k + 2) - u (k + 1)) =
        a * inner ℝ (u (k + 1)) (u (k + 2) - u (k + 1)) -
          b * inner ℝ (y (k + 1)) (u (k + 2) - u (k + 1)) := by
      simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
    have hz : inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) =
        inner ℝ (y (k + 1)) (u (k + 2) - u (k + 1)) -
          inner ℝ (y k) (u (k + 2) - u (k + 1)) := by rw [inner_sub_left]
    rw [hr, hz]
    linarith [hd]
  have h37 (k : ℕ) :
      (Θ (u (k + 2))).toReal - (Θ (u (k + 1))).toReal +
          (1 / lam - L / 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 ≤
        -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) := by
    have ht2 : (Θ (u (k + 2))).toReal = (Φ (u (k + 2))).toReal + Ψ (u (k + 2)) := by
      rw [hH.theta_eq, EReal.toReal_add (hfinite (k + 1)).1 (hfinite (k + 1)).2.1
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    have ht1 : (Θ (u (k + 1))).toReal = (Φ (u (k + 1))).toReal + Ψ (u (k + 1)) := by
      rw [hH.theta_eq, EReal.toReal_add (hfinite k).1 (hfinite k).2.1
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    rw [ht2, ht1]
    linarith [h35 k, h36 k]
  have h38 (k : ℕ) :
      -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) +
          1 / (b * lam ^ 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
            2 * gamma a b lam * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) ≤ 0 := by
    obtain ⟨g0, hg0, hu0⟩ := hIFB.first_update k
    obtain ⟨g1, hg1, hu1⟩ := hfirst k
    have hs0 : Φ (u (k + 1)) + (inner ℝ g0 (u (k + 2) - u (k + 1)) : EReal) ≤
        Φ (u (k + 2)) := by
      simpa [real_inner_comm, add_comm] using hg0 (u (k + 2))
    have hs1 : Φ (u (k + 2)) + (inner ℝ g1 (u (k + 1) - u (k + 2)) : EReal) ≤
        Φ (u (k + 1)) := by
      simpa [real_inner_comm, add_comm] using hg1 (u (k + 1))
    have hr0 := EReal.toReal_le_toReal hs0
      (EReal.add_ne_bot_iff.mpr ⟨(hfinite k).2.1, EReal.coe_ne_bot _⟩)
      (hfinite (k + 1)).1
    have hr1 := EReal.toReal_le_toReal hs1
      (EReal.add_ne_bot_iff.mpr ⟨(hfinite (k + 1)).2.1, EReal.coe_ne_bot _⟩)
      (hfinite k).1
    rw [EReal.toReal_add (hfinite k).1 (hfinite k).2.1
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hr0
    rw [EReal.toReal_add (hfinite (k + 1)).1 (hfinite (k + 1)).2.1
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hr1
    have hmono : inner ℝ (g0 - g1) (u (k + 2) - u (k + 1)) ≤ 0 := by
      norm_num at hr0 hr1
      rw [show u (k + 1) - u (k + 2) =
        -(u (k + 2) - u (k + 1)) by abel, inner_neg_right] at hr1
      rw [inner_sub_left]
      linarith
    have hg0 : g0 = - ((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) := by
      apply eq_neg_of_add_eq_zero_left
      calc
        g0 + ((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) =
            (1 / lam) • (u (k + 1) - u k) + g0 + a • u k - b • y k := by abel
        _ = 0 := hu0
    have hg1 : g1 = - ((1 / lam) • (u (k + 2) - u (k + 1)) +
        a • u (k + 1) - b • y (k + 1)) := by
      apply eq_neg_of_add_eq_zero_left
      calc
        g1 + ((1 / lam) • (u (k + 2) - u (k + 1)) +
            a • u (k + 1) - b • y (k + 1)) =
            (1 / lam) • (u (k + 2) - u (k + 1)) + g1 +
              a • u (k + 1) - b • y (k + 1) := by abel
        _ = 0 := hu1
    rw [hg0, hg1] at hmono
    have hvec : -((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) -
        -((1 / lam) • (u (k + 2) - u (k + 1)) + a • u (k + 1) - b • y (k + 1)) =
        (1 / lam) • (u (k + 2) - u (k + 1)) -
          (1 / lam) • (u (k + 1) - u k) + a • (u (k + 1) - u k) -
            b • (y (k + 1) - y k) := by
      module
    rw [hvec] at hmono
    let v0 : H := u (k + 1) - u k
    let v1 : H := u (k + 2) - u (k + 1)
    let z : H := y (k + 1) - y k
    change inner ℝ ((1 / lam) • v1 - (1 / lam) • v0 + a • v0 - b • z) v1 ≤ 0 at hmono
    have hinner : inner ℝ ((1 / lam) • v1 - (1 / lam) • v0 + a • v0 - b • z) v1 =
        (1 / lam) * (‖v1‖ ^ 2 - inner ℝ v0 v1) + a * inner ℝ v0 v1 -
          b * inner ℝ z v1 := by
      rw [inner_sub_left, inner_add_left, inner_sub_left, inner_smul_left,
        inner_smul_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      ring
    rw [hinner] at hmono
    have hscalar :
        (1 / lam) * (‖u (k + 2) - u (k + 1)‖ ^ 2 -
          inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1))) +
          a * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) -
            b * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) ≤ 0 := by
      change (1 / lam) * (‖v1‖ ^ 2 - inner ℝ v0 v1) + a * inner ℝ v0 v1 -
        b * inner ℝ z v1 ≤ 0
      exact hmono
    have hcoef :
        -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) +
            1 / (b * lam ^ 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
              2 * gamma a b lam * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) =
          (1 / (b * lam)) *
            ((1 / lam) * (‖u (k + 2) - u (k + 1)‖ ^ 2 -
              inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1))) +
              a * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) -
                b * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1))) := by
      rw [gamma]
      field_simp [hH.b_pos.ne', hH.step_pos.ne']
      ring
    rw [hcoef]
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (one_div_pos.mpr (mul_pos hH.b_pos hH.step_pos))) hscalar
  have h39 (k : ℕ) :
      -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) +
          (1 / (b * lam ^ 2) - gamma a b lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
            gamma a b lam * ‖u (k + 1) - u k‖ ^ 2 ≤ 0 := by
    have hsq : 0 ≤ ‖(u (k + 2) - u (k + 1)) - (u (k + 1) - u k)‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at hsq
    have hcross : 2 * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) ≤
        ‖u (k + 1) - u k‖ ^ 2 + ‖u (k + 2) - u (k + 1)‖ ^ 2 := by
      rw [real_inner_comm] at hsq
      nlinarith [hsq]
    have hcross' := mul_le_mul_of_nonneg_left hcross (le_of_lt hgamma)
    linarith [h38 k]
  let E : ℕ → ℝ := fun n =>
    (mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega)).toReal
  let q : ℕ → ℝ := fun n =>
    (1 / lam - L / 2 + 1 / (b * lam ^ 2) - 2 * gamma a b lam) *
      ‖u (n + 2) - u (n + 1)‖ ^ 2
  have hq : ∀ n, 0 ≤ q n := by
    intro n
    dsimp [q]
    exact mul_nonneg (le_of_lt hbeta) (sq_nonneg _)
  have hdesc : ∀ n, E (n + 1) + q n ≤ E n := by
    intro n
    have hs := add_le_add (h37 n) (h39 n)
    dsimp [E, q, mechanicalEnergy, velocity]
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    rw [EReal.toReal_add (hfinite (n + 1)).2.2.1 (hfinite (n + 1)).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    rw [EReal.toReal_add (hfinite n).2.2.1 (hfinite n).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp only [EReal.toReal_coe]
    norm_num
    ring_nf at hs ⊢
    linarith
  obtain ⟨m, hm⟩ := hH.theta_bounded_below
  have hbelow : BddBelow (Set.range E) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp [E, mechanicalEnergy, velocity]
    rw [← EReal.coe_mul]
    rw [EReal.toReal_add (hfinite n).2.2.1 (hfinite n).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp only [EReal.toReal_coe]
    have htm := EReal.toReal_le_toReal (hm (u (n + 1)))
      (EReal.coe_ne_bot _) (hfinite n).2.2.1
    norm_num at htm
    have hcorr : 0 ≤ gamma a b lam * ‖u (n + 1) - u n‖ ^ 2 :=
      mul_nonneg (le_of_lt hgamma) (sq_nonneg _)
    linarith
  obtain ⟨hanti, ⟨l, hlim⟩, hsumq⟩ := descent_summable_real E q hq hbelow hdesc
  have hsumshift : Summable (fun n : ℕ => ‖u (n + 2) - u (n + 1)‖ ^ 2) := by
    apply (summable_mul_left_iff hbeta.ne').mp
    convert hsumq using 1
  have hsum : Summable (fun k : ℕ => ‖u (k + 1) - u k‖ ^ 2) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.add_assoc] using hsumshift
  have hEfinite (n : ℕ) :
      mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega) ≠ ⊤ ∧
        mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega) ≠ ⊥ := by
    unfold mechanicalEnergy
    constructor
    · exact EReal.add_ne_top (hfinite n).2.2.1 (EReal.coe_ne_top _)
    · exact EReal.add_ne_bot_iff.mpr ⟨(hfinite n).2.2.2, EReal.coe_ne_bot _⟩
  have hEeq (n : ℕ) : mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega) =
      (E n : EReal) := by
    dsimp [E]
    exact (EReal.coe_toReal (hEfinite n).1 (hEfinite n).2).symm
  have hmonoEnergy : ∀ k : ℕ,
      mechanicalEnergy Θ u (gamma a b lam) (k + 2) (by omega) ≤
        mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega) := by
    intro k
    rw [hEeq (k + 1), hEeq k]
    exact_mod_cast hanti (Nat.le_succ k)
  have hElim : Filter.Tendsto (fun n : ℕ => (E n : EReal)) Filter.atTop (nhds (l : EReal)) :=
    (continuous_coe_real_ereal.tendsto l).comp hlim
  have henergy_lim : Filter.Tendsto
      (fun n : ℕ => mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega))
        Filter.atTop (nhds (l : EReal)) := by
    simpa only [hEeq] using hElim
  refine ⟨hmonoEnergy, hsum, (l : EReal), henergy_lim, ?_⟩
  have hcorr_lim : Filter.Tendsto
      (fun n : ℕ => gamma a b lam * ‖u (n + 1) - u n‖ ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (Summable.tendsto_atTop_zero hsum))
  have hEform (n : ℕ) : E n = (Θ (u (n + 1))).toReal +
      gamma a b lam * ‖u (n + 1) - u n‖ ^ 2 := by
    dsimp [E, mechanicalEnergy, velocity]
    rw [← EReal.coe_mul]
    rw [EReal.toReal_add (hfinite n).2.2.1 (hfinite n).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp only [EReal.toReal_coe]
  have hsub_lim : Filter.Tendsto
      (fun n : ℕ => E n - gamma a b lam * ‖u (n + 1) - u n‖ ^ 2)
        Filter.atTop (nhds (l - 0)) := hlim.sub hcorr_lim
  have hthetaR : Filter.Tendsto (fun n : ℕ => (Θ (u (n + 1))).toReal)
      Filter.atTop (nhds l) := by
    rw [sub_zero] at hsub_lim
    apply hsub_lim.congr'
    filter_upwards [] with n
    rw [hEform n]
    ring
  have hthetaEL : Filter.Tendsto (fun n : ℕ => ((Θ (u (n + 1))).toReal : EReal))
      Filter.atTop (nhds (l : EReal)) :=
    (continuous_coe_real_ereal.tendsto l).comp hthetaR
  apply hthetaEL.congr'
  filter_upwards [] with n
  exact EReal.coe_toReal (hfinite n).2.2.1 (hfinite n).2.2.2

end AttouchPeypouquetRedont2014
