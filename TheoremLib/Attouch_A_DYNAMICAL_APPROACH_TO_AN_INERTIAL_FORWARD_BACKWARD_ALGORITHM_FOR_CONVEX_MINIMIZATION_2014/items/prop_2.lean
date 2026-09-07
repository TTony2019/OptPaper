import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_5
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_6
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_7
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_8
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_2

namespace AttouchPeypouquetRedont2014

open ERealFunction

/-- The polarization identity used in the algebraic part of Proposition 3. -/
private theorem norm_difference_polarization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x q d : H) :
    2 * inner ℝ d (x + d - q) = ‖x + d - q‖ ^ 2 - ‖x - q‖ ^ 2 + ‖d‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

/-- Combining the two IFB updates yields equation (3.14) in vector form. -/
private theorem ifb_update_vector_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (u y : ℕ → H) (a b lam : ℝ)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (k : ℕ) :
    ∃ g ∈ subdifferential phi (u (k + 1)),
      g + gradPsi (u (k + 1)) =
        - ((1 / lam - a) • velocity u (k + 1) (by omega) +
          (1 / lam + b) • zeta y (k + 1) (by omega)) := by
  obtain ⟨g, hg, hfirst⟩ := hIFB.first_update k
  refine ⟨g, hg, ?_⟩
  have hsecond := hIFB.second_update k
  change (1 / lam) • (u (k + 1) - u k) + g + a • u k - b • y k = 0 at hfirst
  change (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) -
    a • u (k + 1) + b • y (k + 1) = 0 at hsecond
  have hu : u (k + 1) = u k + (u (k + 1) - u k) := by abel
  have hy : y (k + 1) = y k + (y (k + 1) - y k) := by abel
  rw [hu, hy] at hsecond
  rw [velocity_eq_sub_of_one_le, zeta_eq_sub_of_one_le]
  rw [hu, hy]
  simp only [Nat.add_sub_cancel]
  apply eq_neg_of_add_eq_zero_right
  calc
    ((1 / lam - a) • (u k + (u (k + 1) - u k) - u k) +
        (1 / lam + b) • (y k + (y (k + 1) - y k) - y k)) +
        (g + gradPsi (u k + (u (k + 1) - u k))) =
        ((1 / lam) • (u (k + 1) - u k) + g + a • u k - b • y k) +
          ((1 / lam) • (y k + (y (k + 1) - y k) - y k) +
            gradPsi (u k + (u (k + 1) - u k)) - a • (u k + (u (k + 1) - u k)) +
              b • (y k + (y (k + 1) - y k))) := by module
    _ = 0 := by rw [hfirst, hsecond]; simp

/-- A supporting vector can only occur at a finite upper value of a proper
extended-real-valued function. -/
private theorem subgradient_value_ne_top {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {phi : H → EReal} (hproper : ERealFunction.IsProper phi)
    {x g : H} (hg : g ∈ subdifferential phi x) : phi x ≠ ⊤ := by
  obtain ⟨r, hr⟩ := hproper.2
  have hr_top : phi r < ⊤ := (ERealFunction.mem_dom_iff phi r).mp hr
  intro hx_top
  have hs : phi x + (inner ℝ g (r - x) : EReal) ≤ phi r := by
    simpa [real_inner_comm, add_comm] using hg r
  rw [hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hs
  exact (not_le_of_gt hr_top) hs

/-- The IFB hypotheses turn a subgradient of `phi` into the finite-value fact
needed for the EReal support calculation at a trajectory point. -/
private theorem theta_value_finite_of_phi_subgradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Theta psi gradPsi a b lam Lpsi)
    {x g : H} (hg : g ∈ subdifferential phi x) :
    Theta x ≠ ⊤ ∧ Theta x ≠ ⊥ ∧ ((Theta x).toReal : EReal) = Theta x := by
  have hphi_top : phi x ≠ ⊤ := subgradient_value_ne_top hH.phi_proper hg
  have hphi_bot : phi x ≠ ⊥ := hH.phi_proper.1 x
  have htheta_top : Theta x ≠ ⊤ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_top hphi_top (EReal.coe_ne_top _)
  have htheta_bot : Theta x ≠ ⊥ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_bot_iff.mpr ⟨hphi_bot, EReal.coe_ne_bot _⟩
  refine ⟨htheta_top, htheta_bot, ?_⟩
  exact EReal.coe_toReal htheta_top htheta_bot

/-- Properness of the objective follows from properness of the nonsmooth part:
adding a real-valued smooth term neither creates `-∞` nor destroys a finite
domain point. -/
private theorem theta_proper_of_hypothesis {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Theta psi gradPsi a b lam Lpsi) :
    ERealFunction.IsProper Theta := by
  constructor
  · intro x
    rw [hH.theta_eq x]
    exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 x, EReal.coe_ne_bot _⟩
  · obtain ⟨x, hx⟩ := hH.phi_proper.2
    refine ⟨x, ?_⟩
    rw [ERealFunction.mem_dom_iff] at hx ⊢
    rw [hH.theta_eq x]
    exact (EReal.add_ne_top (ne_of_lt hx) (EReal.coe_ne_top _)).lt_top

/-- The ordinary interval-sum endpoint formula used after proof-irrelevance
normalizes the dependent sums in `auxiliaryG` and `liapunovF`. -/
private theorem sum_Icc_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.Icc 2 (k + 1), f i) =
      (∑ i ∈ Finset.Icc 2 k, f i) + f (k + 1) := by
  exact Finset.sum_Icc_succ_top (a := 2) (b := k) (by omega) f

/-- Split the dependent inner-product sum in `auxiliaryG` at its last index.
The auxiliary `if` makes the summand an ordinary function on `ℕ`; on the
interval all proof arguments are then identified by proof irrelevance. -/
private theorem sum_inner_Icc_succ {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ (Finset.Icc 2 (n + 1)).attach,
      inner ℝ (zSequence u y a b lam i (by
        have hi := (Finset.mem_Icc.mp i.property).1
        omega))
        (velocity u i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega))) =
      (∑ i ∈ (Finset.Icc 2 n).attach,
        inner ℝ (zSequence u y a b lam i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega))
          (velocity u i (by
            have hi := (Finset.mem_Icc.mp i.property).1
            omega))) +
      inner ℝ (zSequence u y a b lam (n + 1) (by omega))
        (velocity u (n + 1) (by omega)) := by
  let f : ℕ → ℝ := fun i => if hi : 1 ≤ i then
    inner ℝ (zSequence u y a b lam i hi) (velocity u i hi) else 0
  have hlarge :
      (∑ i ∈ (Finset.Icc 2 (n + 1)).attach,
        inner ℝ (zSequence u y a b lam i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega))
          (velocity u i (by
            have hi := (Finset.mem_Icc.mp i.property).1
            omega))) = ∑ i ∈ Finset.Icc 2 (n + 1), f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 (n + 1)).attach, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
        have hi_one : 1 ≤ (i : ℕ) := by omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  have hsmall :
      (∑ i ∈ (Finset.Icc 2 n).attach,
        inner ℝ (zSequence u y a b lam i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega))
          (velocity u i (by
            have hi := (Finset.mem_Icc.mp i.property).1
            omega))) = ∑ i ∈ Finset.Icc 2 n, f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 n).attach, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
        have hi_one : 1 ≤ (i : ℕ) := by omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  rw [hlarge, hsmall, sum_Icc_succ f n hn]
  simp [f]

/-- Split the proof-indexed squared-velocity sum at its final index. -/
private theorem sum_norm_sq_Icc_succ {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u : ℕ → H) (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ (Finset.Icc 2 (n + 1)).attach,
      ‖velocity u i (by
        have hi := (Finset.mem_Icc.mp i.property).1
        omega)‖ ^ 2) =
      (∑ i ∈ (Finset.Icc 2 n).attach,
        ‖velocity u i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega)‖ ^ 2) + ‖velocity u (n + 1) (by omega)‖ ^ 2 := by
  let f : ℕ → ℝ := fun i => if hi : 1 ≤ i then ‖velocity u i hi‖ ^ 2 else 0
  have hlarge :
      (∑ i ∈ (Finset.Icc 2 (n + 1)).attach,
        ‖velocity u i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega)‖ ^ 2) = ∑ i ∈ Finset.Icc 2 (n + 1), f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 (n + 1)).attach, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_one : 1 ≤ (i : ℕ) := by
          have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
          omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  have hsmall :
      (∑ i ∈ (Finset.Icc 2 n).attach,
        ‖velocity u i (by
          have hi := (Finset.mem_Icc.mp i.property).1
          omega)‖ ^ 2) = ∑ i ∈ Finset.Icc 2 n, f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 n).attach, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi_one : 1 ≤ (i : ℕ) := by
          have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
          omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  rw [hlarge, hsmall, sum_Icc_succ f n hn]
  simp [f]

/-- The increment of `auxiliaryG` is its endpoint contribution. -/
private theorem auxiliaryG_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ)
    (hk : 1 ≤ k) :
    auxiliaryG u y a b lam q (k + 2) (by omega) -
        auxiliaryG u y a b lam q (k + 1) (by omega) =
      inner ℝ (zSequence u y a b lam (k + 2) (by omega)) (u (k + 2) - q) -
        inner ℝ (zSequence u y a b lam (k + 1) (by omega)) (u (k + 1) - q) -
          inner ℝ (zSequence u y a b lam (k + 2) (by omega))
            (velocity u (k + 2) (by omega)) := by
  unfold auxiliaryG
  rw [sum_inner_Icc_succ u y a b lam (k + 1) (by omega)]
  ring

private theorem liapunovF_increment_normal_form {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ)
    (hk : 1 ≤ k) :
    liapunovF u y a b lam q (k + 1) (by omega) - liapunovF u y a b lam q k hk =
      (a + b) / (2 * lam) * (‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2) +
      (1 / lam + b) * inner ℝ (zSequence u y a b lam (k + 2) (by omega))
        (velocity u (k + 2) (by omega)) -
      ((2 + (b - a) * lam) / (2 * lam ^ 2)) * ‖velocity u (k + 1) (by omega)‖ ^ 2 -
      (1 / lam + b) *
        (inner ℝ (zSequence u y a b lam (k + 2) (by omega)) (u (k + 2) - q) -
          inner ℝ (zSequence u y a b lam (k + 1) (by omega)) (u (k + 1) - q)) +
      2 * ((1 + b * lam) / (2 * lam ^ 2)) *
        (inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) -
          inner ℝ (velocity u (k + 1) (by omega)) (u k - q)) := by
  dsimp only [liapunovF]
  simp only [Nat.add_assoc]
  norm_num1
  have hG := auxiliaryG_increment u y a b lam q k hk
  have hnorm := sum_norm_sq_Icc_succ u k hk
  linear_combination -(1 / lam + b) * hG -
    ((2 + (b - a) * lam) / (2 * lam ^ 2)) * hnorm

/-- Equation (3.17), written in the same endpoint coordinates as the
Liapunov increment. -/
private theorem scalar_product_normal_form {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ)
    (hk : 1 ≤ k) :
    b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
      (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) =
      (a + b) / (2 * lam) * (‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2) +
      (1 / lam + b) * inner ℝ (zSequence u y a b lam (k + 1) (by omega))
        (velocity u (k + 1) (by omega)) -
      ((2 + (b - a) * lam) / (2 * lam ^ 2)) * ‖velocity u (k + 1) (by omega)‖ ^ 2 -
      (1 / lam + b) *
        (inner ℝ (a • u (k + 1) - b • y (k + 1)) (u (k + 1) - q) -
          inner ℝ (a • u k - b • y k) (u k - q)) := by
  rw [velocity_eq_sub_of_one_le, zeta_eq_sub_of_one_le]
  simp only [Nat.add_sub_cancel]
  unfold zSequence
  rw [velocity_eq_sub_of_one_le]
  simp only [Nat.add_sub_cancel]
  have hpolar := norm_difference_polarization (u k) q (u (k + 1) - u k)
  have hu : u (k + 1) = u k + (u (k + 1) - u k) := by abel
  rw [← hu] at hpolar
  rw [← real_inner_self_eq_norm_sq (u (k + 1) - u k)] at hpolar ⊢
  simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
    starRingEnd_apply, star_trivial] at hpolar ⊢
  rw [real_inner_comm (u (k + 1)) (u k)] at hpolar ⊢
  by_cases hlam : lam = 0
  · subst lam
    norm_num
    ring
  · field_simp [hlam]
    linear_combination (a + b) * lam * hpolar

/-- The elementary sum rule needed here: a subgradient of the nonsmooth term,
together with the derivative of the smooth term, supports the objective.  The
proof uses only chords of the epigraph, so it is also valid for extended-real
valued `phi`. -/
private theorem hasDerivAt_line_restrict_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (psi : H → ℝ) (gradPsi : H → H) (x d : H)
    (hpsi : Differentiable ℝ psi)
    (hgrad : ∀ x d, fderiv ℝ psi x d = inner ℝ (gradPsi x) d) :
    HasDerivAt (fun t : ℝ => psi (x + t • d)) (inner ℝ (gradPsi x) d) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hfd : HasFDerivAt psi (fderiv ℝ psi x) (x + (0 : ℝ) • d) := by
    simpa using hpsi x |>.hasFDerivAt
  have hcomp := hfd.comp_hasDerivAt 0 hline
  simpa [hgrad x d] using hcomp

private theorem theta_support_of_phi_subgradient {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hΘconvex : Convex ℝ (ERealFunction.epigraph Θ))
    {x g q : H} (hg : g ∈ subdifferential phi x) :
    Θ q ≥ Θ x + (inner ℝ (g + gradPsi x) (q - x) : ℝ) := by
  obtain ⟨hx_top, hx_bot, hx_coe⟩ :=
    theta_value_finite_of_phi_subgradient phi Θ psi gradPsi a b lam Lpsi hH hg
  by_cases hq_top : Θ q = ⊤
  · rw [hq_top]
    simp
  have hq_bot : Θ q ≠ ⊥ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 q, EReal.coe_ne_bot _⟩
  let d : H := q - x
  let X : ℝ := (Θ x).toReal
  let Q : ℝ := (Θ q).toReal
  let P : ℝ → ℝ := fun t => psi (x + t • d)
  have hxE : Θ x = (X : EReal) := by simpa [X] using hx_coe.symm
  have hqE : Θ q = (Q : EReal) := by
    symm
    exact EReal.coe_toReal hq_top hq_bot
  have hchord : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (Θ (x + t • d)).toReal ≤ (1 - t) * X + t * Q := by
    intro t ht0 ht1
    have hxepi : (x, X) ∈ ERealFunction.epigraph Θ := by
      rw [ERealFunction.mem_epigraph_iff, hxE]
    have hqepi : (q, Q) ∈ ERealFunction.epigraph Θ := by
      rw [ERealFunction.mem_epigraph_iff, hqE]
    have hs0 : 0 ≤ 1 - t := by linarith
    have hs : (1 - t) + t = 1 := by ring
    have hcomb := hΘconvex hxepi hqepi hs0 ht0 hs
    have hpoint : (1 - t) • x + t • q = x + t • d := by
      dsimp [d]
      module
    change ((1 - t) • x + t • q, (1 - t) * X + t * Q) ∈
      ERealFunction.epigraph Θ at hcomb
    rw [hpoint] at hcomb
    rw [ERealFunction.mem_epigraph_iff] at hcomb
    have htop : Θ (x + t • d) ≠ ⊤ := by
      intro htop
      rw [htop] at hcomb
      apply EReal.coe_ne_top ((1 - t) * X + t * Q)
      simpa using hcomb
    have hbot : Θ (x + t • d) ≠ ⊥ := by
      rw [hH.theta_eq]
      exact EReal.add_ne_bot_iff.mpr
        ⟨hH.phi_proper.1 _, EReal.coe_ne_bot _⟩
    exact EReal.toReal_le_toReal hcomb hbot (EReal.coe_ne_top _)
  have hphi_finite : ∀ z : H, Θ z ≠ ⊤ → Θ z ≠ ⊥ →
      phi z ≠ ⊤ ∧ phi z ≠ ⊥ := by
    intro z hz_top hz_bot
    rw [hH.theta_eq] at hz_top hz_bot
    constructor
    · intro hp
      rw [hp, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hz_top
      exact hz_top rfl
    · exact hH.phi_proper.1 z
  have hlower : ∀ t : ℝ, 0 < t → t ≤ 1 →
      X + t * inner ℝ g d + (P t - P 0) ≤ (Θ (x + t • d)).toReal := by
    intro t ht ht1
    have hc := hchord t ht.le ht1
    have hz_top : Θ (x + t • d) ≠ ⊤ := by
      intro hz
      have hxepi : (x, X) ∈ ERealFunction.epigraph Θ := by
        rw [ERealFunction.mem_epigraph_iff, hxE]
      have hqepi : (q, Q) ∈ ERealFunction.epigraph Θ := by
        rw [ERealFunction.mem_epigraph_iff, hqE]
      have hs0 : 0 ≤ 1 - t := by linarith
      have hs1 : (1 - t) + t = 1 := by ring
      have hseg := hΘconvex hxepi hqepi hs0 ht.le hs1
      change ((1 - t) • x + t • q, (1 - t) * X + t * Q) ∈
        ERealFunction.epigraph Θ at hseg
      rw [show (1 - t) • x + t • q = x + t • d by dsimp [d]; module,
        ERealFunction.mem_epigraph_iff, hz] at hseg
      apply EReal.coe_ne_top ((1 - t) * X + t * Q)
      simpa using hseg
    have hz_bot : Θ (x + t • d) ≠ ⊥ := by
      rw [hH.theta_eq]
      exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 _, EReal.coe_ne_bot _⟩
    have hpx := hphi_finite x hx_top hx_bot
    have hpz := hphi_finite (x + t • d) hz_top hz_bot
    have hs : phi x + (inner ℝ g (x + t • d - x) : EReal) ≤ phi (x + t • d) := by
      simpa [real_inner_comm, add_comm] using hg (x + t • d)
    have hsub : x + t • d - x = t • d := by abel
    have hsreal := EReal.toReal_le_toReal hs
      (EReal.add_ne_bot_iff.mpr ⟨hpx.2, EReal.coe_ne_bot _⟩) hpz.1
    rw [EReal.toReal_add hpx.1 hpx.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsreal
    rw [hsub, inner_smul_right] at hsreal
    norm_num at hsreal
    rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe] at hsreal
    have hxreal : X = (phi x).toReal + psi x := by
      dsimp [X]
      rw [hH.theta_eq, EReal.toReal_add hpx.1 hpx.2
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    have hzreal : (Θ (x + t • d)).toReal =
        (phi (x + t • d)).toReal + psi (x + t • d) := by
      rw [hH.theta_eq, EReal.toReal_add hpz.1 hpz.2
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    rw [hzreal]
    dsimp [P]
    simp only [zero_smul, add_zero] at *
    linarith
  have hquot : ∀ t : ℝ, 0 < t → t < 1 →
      inner ℝ g d + (P t - P 0) / t ≤ Q - X := by
    intro t ht ht1
    have h1 := hlower t ht ht1.le
    have h2 := hchord t ht.le ht1.le
    have htne : t ≠ 0 := ne_of_gt ht
    dsimp [X, Q] at h1 h2 ⊢
    calc
      inner ℝ g d + (P t - P 0) / t =
          (t * inner ℝ g d + (P t - P 0)) / t := by
            field_simp [htne]
      _ ≤ t * (Q - X) / t := (div_le_div_iff_of_pos_right ht).mpr (by linarith)
      _ = Q - X := by field_simp [htne]
  have hPderiv : HasDerivAt P (inner ℝ (gradPsi x) d) 0 := by
    exact hasDerivAt_line_restrict_local psi gradPsi x d hH.psi_differentiable
      hH.psi_gradient
  have hslope : Filter.Tendsto (fun t : ℝ => (P t - P 0) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ (gradPsi x) d)) := by
    have ht := hPderiv.tendsto_slope_zero_right
    simpa [one_div, div_eq_inv_mul] using ht
  have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      inner ℝ g d + (P t - P 0) / t ≤ Q - X := by
    have hlt : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with t htpos htone
    exact hquot t htpos htone
  have hlim := le_of_tendsto (hslope.const_add (inner ℝ g d)) hevent
  have hreal : inner ℝ (g + gradPsi x) d ≤ Q - X := by
    simpa [inner_add_left] using hlim
  rw [hxE, hqE]
  norm_cast
  dsimp [d, X, Q] at hreal
  linarith

/-- Proposition 3: the Liapunov difference identity and its minimizer monotonicity consequence. -/
theorem proposition3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (u y : ℕ → H)
    (a b lam Lpsi : ℝ) (q : H) (k : ℕ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hk : 1 ≤ k)
    (hconvex : Convex ℝ (ERealFunction.epigraph Θ)) :
    ((b : EReal) * (Θ q - Θ (u (k + 1))) ≥
      ((b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) : EReal)) ∧
    (b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
      (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) =
      liapunovF u y a b lam q (k + 1) (by omega) - liapunovF u y a b lam q k hk) ∧
    (q ∈ Optimization.argminSet Θ →
      liapunovF u y a b lam q (k + 1) (by omega) ≤ liapunovF u y a b lam q k hk) := by
  obtain ⟨g, hg, hvector⟩ :=
    ifb_update_vector_identity phi psi gradPsi u y a b lam hIFB k
  have htheta_finite :=
    theta_value_finite_of_phi_subgradient phi Θ psi gradPsi a b lam Lpsi hH hg
  -- The next required fact is the EReal-valued differentiable perturbation rule:
  -- `hg` and `hH.theta_eq` must show that `g + gradPsi (u (k+1))` supports `Θ`.
  have hfirst :
      (b : EReal) * (Θ q - Θ (u (k + 1))) ≥
        ((b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
          (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) : EReal) := by
    have hsupp := theta_support_of_phi_subgradient phi Θ psi gradPsi a b lam Lpsi hH hconvex
      (q := q) hg
    rw [hvector] at hsupp
    have hsupp' :
        Θ q ≥ Θ (u (k + 1)) +
          (inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
            (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) := by
      have hinner :
          inner ℝ (-((1 / lam - a) • velocity u (k + 1) (by omega) +
            (1 / lam + b) • zeta y (k + 1) (by omega))) (q - u (k + 1)) =
          inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
            (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) := by
        rw [inner_neg_left]
        have hsub : q - u (k + 1) = -(u (k + 1) - q) := by abel
        rw [hsub, inner_neg_right]
        ring
      rw [hinner] at hsupp
      exact hsupp
    by_cases hq : Θ q = ⊤
    · rw [hq]
      rw [EReal.top_sub htheta_finite.1]
      rw [EReal.mul_top_of_pos (by exact_mod_cast hIFB.b_pos)]
      exact le_top
    have hqbot : Θ q ≠ ⊥ := by
      rw [hH.theta_eq]
      exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 q, EReal.coe_ne_bot _⟩
    have hreal :
        inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
          (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) ≤
          (Θ q).toReal - (Θ (u (k + 1))).toReal := by
      rw [← htheta_finite.2.2, ← EReal.coe_toReal hq hqbot] at hsupp'
      linarith [EReal.coe_le_coe_iff.mp hsupp']
    have hmul := mul_le_mul_of_nonneg_left hreal hIFB.b_pos.le
    rw [← htheta_finite.2.2, ← EReal.coe_toReal hq hqbot]
    exact_mod_cast hmul
  have hsecond :
      b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) =
        liapunovF u y a b lam q (k + 1) (by omega) - liapunovF u y a b lam q k hk := by
    have hscalar := scalar_product_normal_form u y a b lam q k hk
    have hF := liapunovF_increment_normal_form u y a b lam q k hk
    rw [hscalar, hF]
    have hv1 : velocity u (k + 1) (by omega) = u (k + 1) - u k := by
      rw [velocity_eq_sub_of_one_le]
      simp only [Nat.add_sub_cancel]
    have hnat : k + 2 - 1 = k + 1 := by omega
    have hv2 : velocity u (k + 2) (by omega) = u (k + 2) - u (k + 1) := by
      rw [velocity_eq_sub_of_one_le]
      rw [hnat]
    rw [hv1, hv2]
    unfold zSequence
    rw [hv1, hv2]
    rw [hnat]
    simp only [Nat.add_sub_cancel]
    rw [← real_inner_self_eq_norm_sq (u (k + 1) - u k)]
    simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [real_inner_comm (u (k + 1)) (u k)]
    by_cases hlam : lam = 0
    · subst lam
      norm_num
      ring
    · field_simp [hlam]
      ring
  refine ⟨hfirst, hsecond, ?_⟩
  intro hq
  rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
  have hq_le : Θ q ≤ Θ (u (k + 1)) := by
    rw [hq]
    exact sInf_le (Set.mem_range_self _)
  have hleft_nonpos : (b : EReal) * (Θ q - Θ (u (k + 1))) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact_mod_cast hIFB.b_pos.le
    · exact EReal.sub_nonpos.mpr hq_le
  have hscalar_ereal :
      ((b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) : EReal) ≤ 0 :=
    hfirst.trans hleft_nonpos
  have hscalar :
      b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) ≤ 0 := by
    exact_mod_cast hscalar_ereal
  rw [hsecond] at hscalar
  linarith

end AttouchPeypouquetRedont2014
