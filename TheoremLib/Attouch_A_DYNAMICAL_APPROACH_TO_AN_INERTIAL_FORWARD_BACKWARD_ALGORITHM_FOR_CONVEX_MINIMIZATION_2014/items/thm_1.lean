import Mathlib
import Foundation.Hilbert.WeakConvergence
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_4
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_5
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_3

open scoped InnerProductSpace
open ERealFunction

namespace AttouchPeypouquetRedont2014

/-- The first two terms of the Liapunov sequence, written locally because the source item for
`auxiliaryA` depends on a currently non-buildable declaration. -/
private noncomputable def theorem1AuxiliaryA {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) : ℝ :=
  (a + b) / (2 * lam) * ‖u (k + 1) - q‖ ^ 2 -
    (1 / lam + b) * auxiliaryG u y a b lam q (k + 2) (by omega)

/-- The four-term cancellation identity for the auxiliary sequence (3.24). -/
private theorem auxiliaryA_four_term {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (p q : H) (m n : ℕ) :
    theorem1AuxiliaryA u y a b lam p m - theorem1AuxiliaryA u y a b lam p n -
        theorem1AuxiliaryA u y a b lam q m + theorem1AuxiliaryA u y a b lam q n =
      ((a + b) / lam) * inner ℝ (u (m + 1) - u (n + 1)) (q - p) -
        (1 / lam + b) * inner ℝ
          (zSequence u y a b lam (m + 2) (by omega) -
            zSequence u y a b lam (n + 2) (by omega)) (q - p) := by
  unfold theorem1AuxiliaryA auxiliaryG
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- The velocity of every IFB trajectory vanishes.  This is the common analytic
input for the shifted subsequence arguments in the three non-singleton cases. -/
private theorem theorem1_velocity_tendsto_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Theta : H → EReal) (psi : H → ℝ)
    (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Theta psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) :
    Filter.Tendsto (fun k : ℕ ↦ u (k + 1) - u k) Filter.atTop (nhds 0) := by
  rcases proposition2 phi Theta psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨_, hsum, _⟩
  have hsq : Filter.Tendsto (fun k : ℕ ↦ ‖u (k + 1) - u k‖ ^ 2)
      Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hnorm : Filter.Tendsto (fun k : ℕ ↦ ‖u (k + 1) - u k‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    convert hsqrt using 1
    · ext k
      change ‖u (k + 1) - u k‖ = √(‖u (k + 1) - u k‖ ^ 2)
      rw [Real.sqrt_sq (norm_nonneg _)]
    · simp
  exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm

/-- The square-velocity sum occurring in the Liapunov function is an ordinary
tail partial sum once the proof-carrying `velocity` arguments are unfolded. -/
private theorem theorem1_velocity_sq_sum_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u : ℕ → H)
    (hsum : Summable (fun k : ℕ ↦ ‖u (k + 1) - u k‖ ^ 2)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ ↦ ∑ i ∈ Finset.Icc 2 k, ‖u i - u (i - 1)‖ ^ 2)
      Filter.atTop (nhds L) := by
  let f : ℕ → ℝ := fun i ↦ ‖u i - u (i - 1)‖ ^ 2
  have htail : Summable (fun i : ℕ ↦ f (i + 2)) :=
    by
      have htail' := (summable_nat_add_iff 1).2 hsum
      simpa [f, Nat.add_assoc] using htail'
  refine ⟨∑' i : ℕ, f (i + 2), ?_⟩
  have hpartial := htail.hasSum.tendsto_sum_nat.comp (Filter.tendsto_sub_atTop_nat 1)
  apply hpartial.congr
  intro k
  change (∑ i ∈ Finset.range (k - 1), f (i + 2)) =
    ∑ i ∈ Finset.Icc 2 k, f i
  symm
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp
    · have hkone : 1 ≤ k := by omega
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      have hrange := (Finset.sum_range_succ (fun i ↦ f (i + 2)) (k - 1)).symm
      have hidx : k - 1 + 2 = k + 1 := by omega
      rw [hidx] at hrange
      simpa [Nat.sub_add_cancel hkone] using hrange

/-- Any fixed forward shift of a convergent Liapunov sequence has the same
limit.  Keeping the index proof explicit avoids dependent-proof rewriting in
the residual estimate used in alternative (iii). -/
private theorem theorem1_liapunov_shift_tendsto {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u y : ℕ → H)
    (a b lam : ℝ) (q : H) (l : ℝ)
    (hF : Filter.Tendsto
      (fun k : ℕ ↦ liapunovF u y a b lam q (k + 1) (by omega))
      Filter.atTop (nhds l))
    (r : ℕ) :
    Filter.Tendsto
      (fun k : ℕ ↦ liapunovF u y a b lam q (k + r + 1) (by omega))
      Filter.atTop (nhds l) := by
  simpa [Function.comp_def, Nat.add_assoc] using
    hF.comp ((Filter.tendsto_add_atTop_nat r))

/-- Passing two indices forward preserves a weak subsequential limit, since the
successive IFB velocities vanish. -/
private theorem theorem1_shift_two_weakly {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (u : ℕ → H) (t : ℕ → ℕ) (p : H)
    (hvel : Filter.Tendsto (fun k : ℕ ↦ u (k + 1) - u k) Filter.atTop (nhds 0))
    (htop : Filter.Tendsto t Filter.atTop Filter.atTop)
    (ht : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j))) Filter.atTop
      (nhds (toWeakSpace ℝ H p))) :
    Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j + 2))) Filter.atTop
      (nhds (toWeakSpace ℝ H p)) := by
  rw [weakConvergence_iff_forall_tendsto_inner_right] at ht ⊢
  intro v
  have htv := ht v
  have hstep₁ : Filter.Tendsto (fun j ↦ u (t j + 1) - u (t j)) Filter.atTop (nhds 0) :=
    by simpa using hvel.comp htop
  have htplus : Filter.Tendsto (fun j ↦ t j + 1) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp
      htop
  have hstep₂ : Filter.Tendsto (fun j ↦ u (t j + 2) - u (t j + 1)) Filter.atTop (nhds 0) :=
    by simpa [Nat.add_assoc] using hvel.comp htplus
  have hinner₁ : Filter.Tendsto (fun j ↦ inner ℝ (u (t j + 1) - u (t j)) v)
      Filter.atTop (nhds 0) := by
    let f : H → ℝ := fun x ↦ inner ℝ x v
    have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
    simpa [f] using (hf.tendsto 0).comp hstep₁
  have hinner₂ : Filter.Tendsto (fun j ↦ inner ℝ (u (t j + 2) - u (t j + 1)) v)
      Filter.atTop (nhds 0) := by
    let f : H → ℝ := fun x ↦ inner ℝ x v
    have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
    simpa [f] using (hf.tendsto 0).comp hstep₂
  have hsum := (htv.add hinner₁).add hinner₂
  convert hsum using 1 <;> simp [inner_add_left, sub_eq_add_neg]

/-- The first IFB update identifies the shifted `z` vector with the negative
subgradient used in all three remaining alternatives. -/
private theorem theorem1_neg_z_mem_subgradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam : ℝ) (u y : ℕ → H)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (k : ℕ) (hk : 1 ≤ k) :
    -zSequence u y a b lam k hk ∈ subdifferential phi (u k) := by
  obtain ⟨g, hg, hupdate⟩ := hIFB.first_update (k - 1)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk'] at hg hupdate
  have hupdate' :
      (1 / lam) • velocity u k hk + g + a • u (k - 1) - b • y (k - 1) = 0 := by
    simpa using hupdate
  have hg_eq : g = -zSequence u y a b lam k hk := by
    apply eq_neg_of_add_eq_zero_left
    change g + ((1 / lam) • velocity u k hk + a • u (k - 1) - b • y (k - 1)) = 0
    calc
      g + ((1 / lam) • velocity u k hk + a • u (k - 1) - b • y (k - 1)) =
          (1 / lam) • velocity u k hk + g + a • u (k - 1) - b • y (k - 1) := by abel
      _ = 0 := hupdate'
  simpa [hg_eq] using hg

/-- The second IFB update, normalized at the literal index used by Proposition 3. -/
private theorem theorem1_residual_vector_raw {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam : ℝ) (u y : ℕ → H)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (r : ℕ) :
    zSequence u y a b lam (r + 1 + 1) (by omega) - gradPsi (u (r + 1 + 1)) =
      (1 / lam - a) • velocity u (r + 1 + 1) (by omega) +
        (1 / lam + b) • zeta y (r + 1 + 1) (by omega) := by
  have hupdate := hIFB.second_update (r + 1)
  have hgrad : gradPsi (u (r + 1 + 1)) =
      - ((1 / lam) • (y (r + 1 + 1) - y (r + 1)) -
        a • u (r + 1 + 1) + b • y (r + 1 + 1)) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      gradPsi (u (r + 1 + 1)) +
          ((1 / lam) • (y (r + 1 + 1) - y (r + 1)) -
            a • u (r + 1 + 1) + b • y (r + 1 + 1)) =
          (1 / lam) • (y (r + 1 + 1) - y (r + 1)) +
            gradPsi (u (r + 1 + 1)) - a • u (r + 1 + 1) +
              b • y (r + 1 + 1) := by abel
      _ = 0 := by simpa [Nat.add_assoc] using hupdate
  rw [hgrad]
  unfold zSequence velocity zeta
  simp only [Nat.add_sub_cancel]
  module

/-- The residual-vector identity in the convenient `r + 2` spelling. -/
private theorem theorem1_residual_vector {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam : ℝ) (u y : ℕ → H)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (r : ℕ) :
    zSequence u y a b lam (r + 2) (by omega) - gradPsi (u (r + 2)) =
      (1 / lam - a) • velocity u (r + 2) (by omega) +
        (1 / lam + b) • zeta y (r + 2) (by omega) := by
  simpa [Nat.add_assoc] using theorem1_residual_vector_raw phi psi gradPsi a b lam u y hIFB r



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
  have hs := hg r
  change (⟪r - x, g⟫_ℝ : EReal) + (phi x : EReal) ≤ (phi r : EReal) at hs
  rw [hx_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hs
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
    have hs := hg (x + t • d)
    have hs' : (phi x : EReal) + (inner ℝ (x + t • d - x) g : EReal) ≤
        (phi (x + t • d) : EReal) := by
      simpa [add_comm] using hs
    have hsub : x + t • d - x = t • d := by abel
    have hsreal := EReal.toReal_le_toReal hs'
      (EReal.add_ne_bot_iff.mpr ⟨hpx.2, EReal.coe_ne_bot _⟩) hpz.1
    rw [EReal.toReal_add hpx.1 hpx.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsreal
    rw [hsub, inner_smul_left] at hsreal
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
    rw [real_inner_comm] at hsreal
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
private theorem theorem1_proposition3_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
private theorem minimizer_mem_phi_dom {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    {q : H} (hq : q ∈ Optimization.argminSet Θ) :
    q ∈ ERealFunction.dom phi := by
  rcases hH.phi_proper.2 with ⟨x, hx⟩
  have htheta_x : Θ x < ⊤ := by
    rw [hH.theta_eq]
    exact EReal.add_lt_top (lt_top_iff_ne_top.mp hx) (EReal.coe_ne_top _)
  have hq_le : Θ q ≤ Θ x := by
    rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
    rw [hq]
    exact sInf_le ⟨x, rfl⟩
  have htheta_q : Θ q < ⊤ := lt_of_le_of_lt hq_le htheta_x
  rw [ERealFunction.mem_dom_iff]
  by_contra hp
  have hp' : phi q = ⊤ := top_unique (not_lt.mp hp)
  rw [hH.theta_eq q, hp'] at htheta_q
  simp at htheta_q

/-- A bounded sequence of squared distances has bounded underlying iterates. -/
private theorem bounded_iterates_of_bounded_sq_distance {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u : ℕ → H) (q : H)
    (h : Bornology.IsBounded (Set.range (fun k => ‖u k - q‖ ^ 2))) :
    Bornology.IsBounded (Set.range u) := by
  rcases (Metric.isBounded_iff.1 h) with ⟨D, hD⟩
  let B : ℝ := D + ‖u 0 - q‖ ^ 2
  have hB : ∀ k, ‖u k - q‖ ^ 2 ≤ B := by
    intro k
    have hd := hD ⟨k, rfl⟩ ⟨0, rfl⟩
    rw [Real.dist_eq] at hd
    change |‖u k - q‖ ^ 2 - ‖u 0 - q‖ ^ 2| ≤ D at hd
    dsimp [B]
    linarith [le_abs_self (‖u k - q‖ ^ 2 - ‖u 0 - q‖ ^ 2)]
  have hBnonneg : 0 ≤ B := le_trans (sq_nonneg _) (hB 0)
  have hnorm : ∀ k, ‖u k - q‖ ≤ Real.sqrt B := by
    intro k
    nlinarith [sq_nonneg (‖u k - q‖ - Real.sqrt B),
      Real.sq_sqrt hBnonneg, norm_nonneg (u k - q), Real.sqrt_nonneg B, hB k]
  apply Metric.isBounded_iff.2
  refine ⟨2 * Real.sqrt B, ?_⟩
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  rw [dist_eq_norm]
  calc
    ‖u i - u j‖ = ‖(u i - q) - (u j - q)‖ := by congr 1; abel
    _ ≤ ‖u i - q‖ + ‖u j - q‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt B := by linarith [hnorm i, hnorm j]

/-- The velocity terms occurring in the Liapunov sum are controlled by the
global square-velocity series. -/
private theorem liapunov_velocity_sum_le_tsum {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (hsq : Summable (fun n : ℕ ↦ ‖u (n + 1) - u n‖ ^ 2))
    (k : ℕ) :
    ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2 := by
  let f : ℕ → ℝ := fun n ↦ ‖u (n + 1) - u n‖ ^ 2
  have hsum : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 = ∑ n ∈ Finset.Icc 1 (k - 1), f n := by
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
      rw [Nat.sub_add_cancel (by omega)]
  rw [hsum]
  exact hsq.sum_le_tsum _ (fun n _ ↦ sq_nonneg _)

private theorem bounded_nonnegative_real_range (p : ℕ → ℝ) (B : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hB : ∀ k, p k ≤ B) :
    Bornology.IsBounded (Set.range p) := by
  apply Metric.isBounded_iff.2
  refine ⟨B, ?_⟩
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hp i, hB j], by linarith [hp j, hB i]⟩

private theorem liapunov_cross_young {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A α : ℝ) (hA : 0 < A) (hα : 0 ≤ α) (v d : H) :
    -2 * α * inner ℝ v d ≤
      (A / 2) * ‖d‖ ^ 2 + (2 * α ^ 2 / A) * ‖v‖ ^ 2 := by
  have hinter : -‖v‖ * ‖d‖ ≤ inner ℝ v d := by
    simpa only [neg_mul] using (neg_le_of_abs_le (abs_real_inner_le_norm v d))
  have hmul := mul_le_mul_of_nonpos_left hinter (by linarith : -2 * α ≤ 0)
  have hscalar : 2 * α * ‖v‖ * ‖d‖ ≤
      (A / 2) * ‖d‖ ^ 2 + (2 * α ^ 2 / A) * ‖v‖ ^ 2 := by
    have hsq : 0 ≤ (A * ‖d‖ - 2 * α * ‖v‖) ^ 2 := sq_nonneg _
    have hden : 0 < 2 * A := by positivity
    have hnonneg : 0 ≤
        (A / 2) * ‖d‖ ^ 2 + (2 * α ^ 2 / A) * ‖v‖ ^ 2 -
          2 * α * ‖v‖ * ‖d‖ := by
      rw [show (A / 2) * ‖d‖ ^ 2 + (2 * α ^ 2 / A) * ‖v‖ ^ 2 -
          2 * α * ‖v‖ * ‖d‖ =
          (A * ‖d‖ - 2 * α * ‖v‖) ^ 2 / (2 * A) by
        field_simp [hA.ne']
        ring]
      exact div_nonneg hsq (le_of_lt hden)
    linarith
  nlinarith

private theorem liapunovF_proof_irrel {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ)
    (hk hk' : 1 ≤ k) :
    liapunovF u y a b lam q k hk = liapunovF u y a b lam q k hk' := by
  congr

/-- Transport a Liapunov inequality across its index-validity witnesses. -/
private theorem liapunovF_le_proof_irrel {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k l : ℕ)
    {hk hk' : 1 ≤ k} {hl hl' : 1 ≤ l}
    (h : liapunovF u y a b lam q k hk ≤ liapunovF u y a b lam q l hl) :
    liapunovF u y a b lam q k hk' ≤ liapunovF u y a b lam q l hl' := by
  calc
    liapunovF u y a b lam q k hk' = liapunovF u y a b lam q k hk :=
      liapunovF_proof_irrel u y a b lam q k _ _
    _ ≤ liapunovF u y a b lam q l hl := h
    _ = liapunovF u y a b lam q l hl' :=
      liapunovF_proof_irrel u y a b lam q l _ _

set_option maxHeartbeats 800000 in
-- The Liapunov energy estimate needs extra heartbeats.
/-- Proposition 8: a nonempty solution set yields bounded IFB iterates and convergent `F_k(q)`. -/
private theorem theorem1_proposition8_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (u y : ℕ → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y)
    (hS : (Optimization.argminSet Θ).Nonempty) :
    Bornology.IsBounded (Set.range u) ∧
    ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => liapunovF u y a b lam q (k + 1) (by omega))
        Filter.atTop (nhds l) := by
  obtain ⟨q₀, hq₀⟩ := hS
  obtain ⟨_, hsq, _⟩ := proposition2 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
  let S : ℝ := ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun n => sq_nonneg _
  have hpoint (n : ℕ) : ‖u (n + 1) - u n‖ ^ 2 ≤ S := by
    dsimp [S]
    simpa using hsq.sum_le_tsum ({n} : Finset ℕ) (fun _ _ => sq_nonneg _)
  let A : ℝ := (a + b) / (2 * lam)
  let c : ℝ := 1 / lam + b
  let α : ℝ := (1 + b * lam) / (2 * lam ^ 2)
  let δ : ℝ := (2 + (b - a) * lam) / (2 * lam ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    apply div_pos
    · nlinarith [hH.a_pos, hH.b_pos]
    · nlinarith [hH.step_pos]
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
  have hα : 0 < α := by
    dsimp [α]
    apply div_pos
    · nlinarith [mul_pos hH.b_pos hH.step_pos]
    · nlinarith [sq_pos_of_pos hH.step_pos]
  have hδ : 0 < δ := by
    have hlt : lam < 1 / a := lt_of_lt_of_le hH.step_lt (min_le_left _ _)
    have hla : lam * a < 1 := (lt_div_iff₀ hH.a_pos).mp hlt
    have hnum : 0 < 2 + (b - a) * lam := by
      nlinarith [mul_pos hH.b_pos hH.step_pos]
    dsimp [δ]
    exact div_pos hnum (by nlinarith [sq_pos_of_pos hH.step_pos])
  have hsqdist (q : H) (hq : q ∈ Optimization.argminSet Θ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ‖u k - q‖ ^ 2 ≤ B := by
    have hqdom := minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq
    let M : ℝ := Classical.choose (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom)
    have hG (j : ℕ) (hj : 2 ≤ j) : auxiliaryG u y a b lam q j hj ≤ M := by
      dsimp [M]
      exact Classical.choose_spec
        (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom) j hj
    let F : ℕ → ℝ := fun n => liapunovF u y a b lam q (n + 1) (by omega)
    have hF_succ (n : ℕ) : F (n + 1) ≤ F n := by
      dsimp [F]
      have hmono := (theorem1_proposition3_local phi Θ psi gradPsi u y a b lam Lpsi q (n + 1)
        hH hIFB (by omega) hH.theta_convex).2.2 hq
      exact liapunovF_le_proof_irrel u y a b lam q (n + 1 + 1) (n + 1) hmono
    have hFanti : Antitone F := antitone_nat_of_succ_le hF_succ
    have hupper (k : ℕ) : F k ≤ F 0 := hFanti (Nat.zero_le k)
    let C : ℝ := liapunovF u y a b lam q 1 (by omega) + c * M + δ * S +
      (2 * α ^ 2 / A) * S
    have htail (k : ℕ) : ‖u (k + 1) - q‖ ^ 2 ≤ max 0 (2 * C / A) := by
      have hsum := liapunov_velocity_sum_le_tsum u hsq (k + 1)
      have hGk : auxiliaryG u y a b lam q (k + 2) (by omega) ≤ M :=
        hG (k + 2) (by omega)
      have hvelsq : ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤ S := by
        rw [velocity_eq_sub_of_one_le]
        simpa using hpoint (k + 1)
      have hGM : -c * M ≤ -c * auxiliaryG u y a b lam q (k + 2) (by omega) := by
        nlinarith [mul_le_mul_of_nonneg_left hGk (le_of_lt hc)]
      have hTS : -δ * S ≤ -δ * (∑ i ∈ (Finset.Icc 2 (k + 1)).attach,
          ‖velocity u i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)‖ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hδ)]
      have hYoung := liapunov_cross_young A α hA (le_of_lt hα)
        (velocity u (k + 2) (by omega)) (u (k + 1) - q)
      have hcoef : 0 ≤ 2 * α ^ 2 / A := by positivity
      have hvelS : (2 * α ^ 2 / A) * ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤
          (2 * α ^ 2 / A) * S :=
        mul_le_mul_of_nonneg_left hvelsq hcoef
      have hcross : -(A / 2) * ‖u (k + 1) - q‖ ^ 2 -
          (2 * α ^ 2 / A) * ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤
          2 * α * inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) := by
        nlinarith [hYoung]
      have hF : (A / 2) * ‖u (k + 1) - q‖ ^ 2 - c * M - δ * S -
          (2 * α ^ 2 / A) * S ≤ liapunovF u y a b lam q (k + 1) (by omega) := by
        dsimp [liapunovF]
        nlinarith [hvelS, hcross]
      have hhalf : (A / 2) * ‖u (k + 1) - q‖ ^ 2 ≤ C := by
        dsimp [C]
        nlinarith [hF, hupper k]
      have hdiv : ‖u (k + 1) - q‖ ^ 2 ≤ 2 * C / A := by
        apply (le_div_iff₀ hA).mpr
        nlinarith
      exact hdiv.trans (le_max_right _ _)
    let B : ℝ := max (max 0 (2 * C / A)) (‖u 0 - q‖ ^ 2)
    refine ⟨B, ?_, ?_⟩
    · exact le_trans (sq_nonneg _) (le_max_right _ _)
    · intro k
      cases k with
      | zero => exact le_max_right _ _
      | succ k => exact (htail k).trans (le_max_left _ _)
  have hbd : Bornology.IsBounded (Set.range u) := by
    obtain ⟨B, hB0, hB⟩ := hsqdist q₀ hq₀
    apply bounded_iterates_of_bounded_sq_distance u q₀
    exact bounded_nonnegative_real_range (fun k => ‖u k - q₀‖ ^ 2) B
      (fun k => sq_nonneg _) hB
  refine ⟨hbd, ?_⟩
  intro q hq
  obtain ⟨B, hB0, hB⟩ := hsqdist q hq
  have hqdom := minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq
  let M : ℝ := Classical.choose (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom)
  have hG (j : ℕ) (hj : 2 ≤ j) : auxiliaryG u y a b lam q j hj ≤ M := by
    dsimp [M]
    exact Classical.choose_spec
      (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom) j hj
  let F : ℕ → ℝ := fun n => liapunovF u y a b lam q (n + 1) (by omega)
  have hF_succ (n : ℕ) : F (n + 1) ≤ F n := by
    dsimp [F]
    have hmono := (theorem1_proposition3_local phi Θ psi gradPsi u y a b lam Lpsi q (n + 1)
      hH hIFB (by omega) hH.theta_convex).2.2 hq
    exact liapunovF_le_proof_irrel u y a b lam q (n + 1 + 1) (n + 1) hmono
  have hFanti : Antitone F := antitone_nat_of_succ_le hF_succ
  let L : ℝ := -c * M - δ * S - 2 * α * Real.sqrt S * Real.sqrt B
  have hlower (k : ℕ) : L ≤ F k := by
    have hsum := liapunov_velocity_sum_le_tsum u hsq (k + 1)
    have hGk : auxiliaryG u y a b lam q (k + 2) (by omega) ≤ M := by
      exact hG (k + 2) (by omega)
    have hvelsq : ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤ S := by
      rw [velocity_eq_sub_of_one_le]
      simpa using hpoint (k + 1)
    have hvel : ‖velocity u (k + 2) (by omega)‖ ≤ Real.sqrt S := by
      nlinarith [norm_nonneg (velocity u (k + 2) (by omega)), Real.sqrt_nonneg S,
        Real.sq_sqrt hSnonneg]
    have hdist : ‖u (k + 1) - q‖ ≤ Real.sqrt B := by
      nlinarith [norm_nonneg (u (k + 1) - q), Real.sqrt_nonneg B,
        Real.sq_sqrt hB0, hB (k + 1)]
    have hinter : -‖velocity u (k + 2) (by omega)‖ * ‖u (k + 1) - q‖ ≤
        inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) := by
      simpa only [neg_mul] using
        (neg_le_of_abs_le (abs_real_inner_le_norm (velocity u (k + 2) (by omega))
          (u (k + 1) - q)))
    have hcross : -2 * α * Real.sqrt S * Real.sqrt B ≤
        2 * α * inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) := by
      have hmul := mul_le_mul_of_nonneg_left hinter (by positivity : 0 ≤ 2 * α)
      nlinarith [mul_nonneg (norm_nonneg (velocity u (k + 2) (by omega)))
          (norm_nonneg (u (k + 1) - q)),
        mul_le_mul hvel hdist (norm_nonneg _) (Real.sqrt_nonneg _)]
    have hGM : -c * M ≤ -c * auxiliaryG u y a b lam q (k + 2) (by omega) := by
      nlinarith [mul_le_mul_of_nonneg_left hGk (le_of_lt hc)]
    have hTS : -δ * S ≤ -δ * (∑ i ∈ (Finset.Icc 2 (k + 1)).attach,
        ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hδ)]
    dsimp [F, L, liapunovF]
    nlinarith [mul_nonneg (le_of_lt hA) (sq_nonneg (‖u (k + 1) - q‖))]
  have hbelow : BddBelow (Set.range F) :=
    ⟨L, by rintro _ ⟨k, rfl⟩; exact hlower k⟩
  refine ⟨⨅ k, F k, ?_⟩
  exact tendsto_atTop_ciInf hFanti hbelow

/-- The auxiliary quantity in (3.23) has a limit at every minimizer.  This is
the part of the final cluster-point argument which only uses Proposition 8 and
the square summability of the IFB velocities. -/
private theorem theorem1_auxiliaryA_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Theta : H → EReal) (psi : H → ℝ)
    (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Theta psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y)
    (hbounded : Bornology.IsBounded (Set.range u))
    (hFlim : ∀ q ∈ Optimization.argminSet Theta, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => liapunovF u y a b lam q (k + 1) (by omega))
        Filter.atTop (nhds l))
    {q : H} (hq : q ∈ Optimization.argminSet Theta) :
    ∃ l : ℝ, Filter.Tendsto (fun k : ℕ => theorem1AuxiliaryA u y a b lam q k)
      Filter.atTop (nhds l) := by
  rcases hFlim q hq with ⟨lF, hlF⟩
  rcases proposition2 phi Theta psi gradPsi a b lam Lpsi u y hH hIFB with ⟨_, hsq, _⟩
  rcases theorem1_velocity_sq_sum_tendsto u hsq with ⟨lS, hlS⟩
  have hsum : Filter.Tendsto (fun k : ℕ =>
      ∑ i ∈ (Finset.Icc 2 (k + 1)).attach,
        ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2) Filter.atTop (nhds lS) := by
    convert hlS.comp (Filter.tendsto_add_atTop_nat 1) using 1
    funext k
    simp only [Function.comp_apply]
    change Finset.sum (Finset.Icc 2 (k + 1)).attach (fun i =>
      ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2) = Finset.sum (Finset.Icc 2 (k + 1)) (fun i => ‖u i - u (i - 1)‖ ^ 2)
    classical
    apply Finset.sum_bij (fun i _ => i.1)
    · intro i hi
      exact i.2
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro j hj
      refine ⟨⟨j, hj⟩, Finset.mem_attach _ _, ?_⟩
      simp
    · intro i hi
      rw [velocity_eq_sub_of_one_le]
  have hvel := theorem1_velocity_tendsto_zero phi Theta psi gradPsi a b lam Lpsi u y hH hIFB
  have hstep : Filter.Tendsto (fun k : ℕ => u (k + 2) - u (k + 1))
      Filter.atTop (nhds 0) := by
    simpa [Nat.add_assoc] using hvel.comp (Filter.tendsto_add_atTop_nat 1)
  rcases (isBounded_iff_forall_norm_le.mp hbounded) with ⟨C, hC⟩
  let D : ℝ := C + ‖q‖
  have hD : ∀ k : ℕ, ‖u k - q‖ ≤ D := by
    intro k
    calc
      ‖u k - q‖ ≤ ‖u k‖ + ‖q‖ := norm_sub_le _ _
      _ ≤ D := by dsimp [D]; linarith [hC _ (Set.mem_range_self k)]
  have hcross : Filter.Tendsto (fun k : ℕ =>
      inner ℝ (u (k + 2) - u (k + 1)) (u (k + 1) - q))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : Filter.Tendsto (fun k : ℕ => ‖u (k + 2) - u (k + 1)‖)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hstep)
    have hprod : Filter.Tendsto (fun k : ℕ =>
        ‖u (k + 2) - u (k + 1)‖ * D) Filter.atTop (nhds 0) := by
      simpa using hnorm.mul_const D
    have habs : Filter.Tendsto (fun k : ℕ =>
        |inner ℝ (u (k + 2) - u (k + 1)) (u (k + 1) - q)|)
        Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod
        (fun k => abs_nonneg _) ?_
      intro k
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hD (k + 1)) (norm_nonneg _))
    simpa only [Real.norm_eq_abs] using habs
  have hF : Filter.Tendsto (fun k : ℕ =>
      liapunovF u y a b lam q (k + 1) (by omega)) Filter.atTop (nhds lF) := hlF
  let δ : ℝ := (2 + (b - a) * lam) / (2 * lam ^ 2)
  let α : ℝ := (1 + b * lam) / (2 * lam ^ 2)
  refine ⟨lF + δ * lS, ?_⟩
  have hmain := (hF.add (hsum.const_mul δ)).sub (hcross.const_mul (2 * α))
  convert hmain using 1 <;> ext k <;>
    simp [theorem1AuxiliaryA, liapunovF, velocity, δ, α]; ring


/-- Theorem 1: under any stated uniqueness/continuity/convexity alternative, IFB converges weakly
to a minimizer. -/
theorem theorem1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) :
    Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds (sInf (Set.range Θ))) ∧
    (((Optimization.argminSet Θ).Nonempty ∧
        ((∃ q, Optimization.argminSet Θ = {q}) ∨
          (∃ phiReal : H → ℝ, (∀ x, phi x = (phiReal x : EReal)) ∧ Differentiable ℝ phiReal ∧
            (∃ gradPhi : H → H, (∀ x h, fderiv ℝ phiReal x h = inner ℝ (gradPhi x) h) ∧
              IsWeakToWeakSequentiallyContinuous gradPhi)) ∨
          IsWeakToWeakSequentiallyContinuous gradPsi ∨
          Convex ℝ (ERealFunction.epigraph fun x ↦ (psi x : EReal)))) →
      (∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
        (nhds (toWeakSpace ℝ H q)))) ∧
    (Optimization.argminSet Θ = ∅ → Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop Filter.atTop) := by
  rcases proposition6 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨hobjective, hcluster, hempty⟩
  refine ⟨hobjective, ?_, hempty⟩
  rintro ⟨hS, hcase⟩
  -- The imported Proposition 8 has a malformed exported type: its final
  -- proof-index argument of `liapunovF` was erased.  A local reconstruction
  -- is therefore needed before this common boundedness package is available.
  have hbounded : Bornology.IsBounded (Set.range u) := by
    exact (theorem1_proposition8_local phi Θ psi gradPsi u y a b lam Lpsi hH hIFB hS).1
  have hFlim : ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => liapunovF u y a b lam q (k + 1) (by omega))
        Filter.atTop (nhds l) :=
    (theorem1_proposition8_local phi Θ psi gradPsi u y a b lam Lpsi hH hIFB hS).2
  have hAlim : ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => theorem1AuxiliaryA u y a b lam q k)
        Filter.atTop (nhds l) := by
    intro q hq
    exact theorem1_auxiliaryA_tendsto phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
      hbounded hFlim hq
  rcases hcase with hsingle | hphi | hgrad | hpsi
  · rcases hsingle with ⟨q0, hsingle⟩
    have hunique : ∀ p q : H,
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) → p = q := by
      intro p q hp hq
      have hpS : p ∈ ({q0} : Set H) := by simpa [hsingle] using hcluster p hp
      have hqS : q ∈ ({q0} : Set H) := by simpa [hsingle] using hcluster q hq
      exact (Set.mem_singleton_iff.mp hpS).trans (Set.mem_singleton_iff.mp hqS).symm
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with ⟨q, hq⟩
    have hqcluster : IsSequentialClusterPt
        (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) :=
      ⟨id, strictMono_id, by simpa using hq⟩
    exact ⟨q, hcluster q hqcluster, hq⟩
  · rcases hphi with ⟨phiReal, hphi, hdiff, gradPhi, hgradPhi, hgradWeak⟩
    have hsubgradient_eq (x g : H) (hg : g ∈ subdifferential phi x) :
        g = gradPhi x := by
      have hmin : IsMinOn (fun z : H => phiReal z - inner ℝ g z) Set.univ x := by
        intro z hz
        change phiReal x - inner ℝ g x ≤ phiReal z - inner ℝ g z
        have hs := hg z
        rw [hphi x, hphi z] at hs
        have hsreal : inner ℝ (z - x) g + phiReal x ≤ phiReal z := by
          apply EReal.coe_le_coe_iff.mp
          simpa using hs
        rw [inner_sub_left] at hsreal
        rw [real_inner_comm z g, real_inner_comm x g]
        linarith
      have hx : HasFDerivAt phiReal (fderiv ℝ phiReal x) x := (hdiff x).hasFDerivAt
      have hinner : HasFDerivAt (fun z : H => inner ℝ g z) (innerSL ℝ g) x :=
        (innerSL ℝ g).hasFDerivAt
      have hzero := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero (hx.sub hinner)
      have hmaps : fderiv ℝ phiReal x = innerSL ℝ g := sub_eq_zero.mp hzero
      have hd := congrArg (fun L : H →L[ℝ] ℝ => L (gradPhi x - g)) hmaps
      change (fderiv ℝ phiReal x) (gradPhi x - g) =
        inner ℝ g (gradPhi x - g) at hd
      rw [hgradPhi x (gradPhi x - g)] at hd
      have hnorm : ‖g - gradPhi x‖ ^ 2 = 0 := by
        rw [norm_sub_rev, ← real_inner_self_eq_norm_sq (gradPhi x - g), inner_sub_left]
        exact sub_eq_zero.mpr hd
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
    have hvel := theorem1_velocity_tendsto_zero phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
    have hunique : ∀ p q : H,
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) → p = q := by
      intro p q hp hq
      rcases hp with ⟨t, htmono, ht⟩
      rcases hq with ⟨s, hsmono, hs⟩
      have hpS : p ∈ Optimization.argminSet Θ := hcluster p ⟨t, htmono, ht⟩
      have hqS : q ∈ Optimization.argminSet Θ := hcluster q ⟨s, hsmono, hs⟩
      rcases hAlim p hpS with ⟨lp, hlp⟩
      rcases hAlim q hqS with ⟨lq, hlq⟩
      have htTop : Filter.Tendsto t Filter.atTop Filter.atTop := htmono.tendsto_atTop
      have hsTop : Filter.Tendsto s Filter.atTop Filter.atTop := hsmono.tendsto_atTop
      have ht2 := theorem1_shift_two_weakly u t p hvel htTop (by simpa [Function.comp_def] using ht)
      have hs2 := theorem1_shift_two_weakly u s q hvel hsTop (by simpa [Function.comp_def] using hs)
      have hAtp := hlp.comp htTop
      have hAsp := hlp.comp hsTop
      have hAtq := hlq.comp htTop
      have hAsq := hlq.comp hsTop
      have hleft := ((hAtp.sub hAsp).sub hAtq).add hAsq
      have hgradt := hgradWeak (fun j => u (t j + 2)) p ht2
      have hgrads := hgradWeak (fun j => u (s j + 2)) q hs2
      have hzinner : Filter.Tendsto (fun j => inner ℝ
          (zSequence u y a b lam (t j + 2) (by omega) -
            zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds (inner ℝ (gradPhi p - gradPhi q) (p - q))) := by
        have hgradt' := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 hgradt (q - p)
        have hgrads' := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 hgrads (q - p)
        have hinner := (hgradt'.sub hgrads').neg
        convert hinner using 1
        · ext j
          rw [← hsubgradient_eq (u (t j + 2))
              (-zSequence u y a b lam (t j + 2) (by omega))
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                (t j + 2) (by omega)),
            ← hsubgradient_eq (u (s j + 2))
              (-zSequence u y a b lam (s j + 2) (by omega))
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                (s j + 2) (by omega))]
          simp only [neg_sub_neg, inner_neg_left]
          simp only [inner_sub_left]
          ring
        · simp only [inner_sub_left, inner_sub_right]
          ring
      have hconv : ConvexOn ℝ Set.univ phiReal := by
        apply convexOn_of_convex_epigraph
        simpa [ERealFunction.epigraph, hphi] using hH.phi_convex
      have hsupport : ∀ x z : H,
          phiReal x - phiReal z ≤ inner ℝ (gradPhi x) (x - z) := by
        intro x z
        let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z x
        have hline : HasDerivAt line (x - z) 1 := by
          convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - z)).add_const z using 1 <;> simp
        have hc : ConvexOn ℝ Set.univ (phiReal ∘ line) := by
          simpa [line] using hconv.comp_affineMap line
        have hd : HasDerivAt (phiReal ∘ line) (inner ℝ (gradPhi x) (x - z)) 1 := by
          have hx : HasFDerivAt phiReal (fderiv ℝ phiReal x) (line 1) := by
            simpa [line] using (hdiff x).hasFDerivAt
          have hcomp := hx.comp_hasDerivAt 1 hline
          simpa [line, hgradPhi x, innerSL_apply_apply] using hcomp
        have hslope := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
          (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hd
        simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
          AffineMap.lineMap_apply_one] using hslope
      have hgrad_nonneg : 0 ≤ inner ℝ (gradPhi p - gradPhi q) (p - q) := by
        have hpq := hsupport p q
        have hqp := hsupport q p
        rw [show q - p = -(p - q) by abel, inner_neg_right] at hqp
        rw [inner_sub_left]
        linarith
      have hcoef : 0 < (a + b) / lam := div_pos (by linarith [hH.a_pos, hH.b_pos]) hH.step_pos
      have hzcoef : 0 < 1 / lam + b := by
        nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
      have hidentity : Filter.Tendsto (fun j =>
          ((a + b) / lam) * inner ℝ (u (t j + 1) - u (s j + 1)) (q - p) -
            (1 / lam + b) * inner ℝ
              (zSequence u y a b lam (t j + 2) (by omega) -
                zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds 0) := by
        convert hleft using 1
        · ext j
          exact (auxiliaryA_four_term u y a b lam p q (t j) (s j)).symm
        · simp
      have ht1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H p)) := by
        have ht' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j))) Filter.atTop
            (nhds (toWeakSpace ℝ H p)) := by simpa [Function.comp_def] using ht
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (t j + 1) - u (t j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp htTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (t j + 1) - u (t j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (ht' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have hs1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H q)) := by
        have hs' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j))) Filter.atTop
            (nhds (toWeakSpace ℝ H q)) := by simpa [Function.comp_def] using hs
        rw [weakConvergence_iff_forall_tendsto_inner_right] at hs' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (s j + 1) - u (s j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp hsTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (s j + 1) - u (s j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (hs' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have huinner : Filter.Tendsto (fun j =>
          inner ℝ (u (t j + 1) - u (s j + 1)) (q - p)) Filter.atTop
          (nhds (-‖p - q‖ ^ 2)) := by
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht1 hs1
        have hinner := ((ht1 (q - p)).sub (hs1 (q - p)))
        convert hinner using 1
        · ext j
          simp [inner_sub_left]
        · rw [← real_inner_self_eq_norm_sq (p - q)]
          simp only [inner_sub_left, inner_sub_right]
          ring_nf
      have hcombined :=
        (huinner.const_mul ((a + b) / lam)).sub
          (hzinner.const_mul (1 / lam + b))
      have heq : (0 : ℝ) = ((a + b) / lam) * (-‖p - q‖ ^ 2) -
          (1 / lam + b) * inner ℝ (gradPhi p - gradPhi q) (p - q) :=
        tendsto_nhds_unique hidentity hcombined
      have hnormzero : ‖p - q‖ = 0 := by
        have hfirst : 0 ≤ ((a + b) / lam) * ‖p - q‖ ^ 2 :=
          mul_nonneg hcoef.le (sq_nonneg _)
        have hsecond : 0 ≤ (1 / lam + b) * inner ℝ (gradPhi p - gradPhi q) (p - q) :=
          mul_nonneg hzcoef.le hgrad_nonneg
        have hz : ((a + b) / lam) * ‖p - q‖ ^ 2 = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left hcoef.ne' |> sq_eq_zero_iff.mp
      exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with ⟨q, hq⟩
    have hqcluster : IsSequentialClusterPt
        (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) :=
      ⟨id, strictMono_id, by simpa using hq⟩
    exact ⟨q, hcluster q hqcluster, hq⟩
  · have hvel := theorem1_velocity_tendsto_zero phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
    have hresidual_inner (q : H) (hq : q ∈ Optimization.argminSet Θ) :
        Filter.Tendsto (fun k : ℕ => inner ℝ
          (zSequence u y a b lam (k + 2) (by omega) - gradPsi (u (k + 2)))
          (u (k + 2) - q)) Filter.atTop (nhds 0) := by
      rcases hFlim q hq with ⟨l, hl⟩
      have hl' := theorem1_liapunov_shift_tendsto u y a b lam q l hl 1
      have hdiff := hl'.sub hl
      have hb : b ≠ 0 := ne_of_gt hH.b_pos
      have hscaled := hdiff.const_mul (1 / b)
      convert hscaled using 1
      · ext k
        have hinc := (theorem1_proposition3_local phi Θ psi gradPsi u y a b lam Lpsi q
          (k + 1) hH hIFB (by omega) hH.theta_convex).2.1
        calc
          inner ℝ
              (zSequence u y a b lam (k + 2) (by omega) - gradPsi (u (k + 2)))
              (u (k + 2) - q) =
              inner ℝ ((1 / lam - a) • velocity u (k + 2) (by omega) +
                (1 / lam + b) • zeta y (k + 2) (by omega)) (u (k + 2) - q) := by
                rw [theorem1_residual_vector phi psi gradPsi a b lam u y hIFB k]
          _ = (1 / b) * (liapunovF u y a b lam q (k + 1 + 1) (by omega) -
                liapunovF u y a b lam q (k + 1) (by omega)) := by
                rw [← hinc]
                field_simp [hb]
      · simp
    have hunique : ∀ p q : H,
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) → p = q := by
      intro p q hp hq
      rcases hp with ⟨t, htmono, ht⟩
      rcases hq with ⟨s, hsmono, hs⟩
      have hpS : p ∈ Optimization.argminSet Θ := hcluster p ⟨t, htmono, ht⟩
      have hqS : q ∈ Optimization.argminSet Θ := hcluster q ⟨s, hsmono, hs⟩
      rcases hAlim p hpS with ⟨lp, hlp⟩
      rcases hAlim q hqS with ⟨lq, hlq⟩
      have htTop : Filter.Tendsto t Filter.atTop Filter.atTop := htmono.tendsto_atTop
      have hsTop : Filter.Tendsto s Filter.atTop Filter.atTop := hsmono.tendsto_atTop
      have ht2 := theorem1_shift_two_weakly u t p hvel htTop
        (by simpa [Function.comp_def] using ht)
      have hs2 := theorem1_shift_two_weakly u s q hvel hsTop
        (by simpa [Function.comp_def] using hs)
      have hAtp := hlp.comp htTop
      have hAsp := hlp.comp hsTop
      have hAtq := hlq.comp htTop
      have hAsq := hlq.comp hsTop
      have hleft := ((hAtp.sub hAsp).sub hAtq).add hAsq
      have hidentity : Filter.Tendsto (fun j =>
          ((a + b) / lam) * inner ℝ (u (t j + 1) - u (s j + 1)) (q - p) -
            (1 / lam + b) * inner ℝ
              (zSequence u y a b lam (t j + 2) (by omega) -
                zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds 0) := by
        convert hleft using 1
        · ext j
          exact (auxiliaryA_four_term u y a b lam p q (t j) (s j)).symm
        · simp
      have ht1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H p)) := by
        have ht' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j))) Filter.atTop
            (nhds (toWeakSpace ℝ H p)) := by simpa [Function.comp_def] using ht
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (t j + 1) - u (t j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp htTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (t j + 1) - u (t j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (ht' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have hs1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H q)) := by
        have hs' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j))) Filter.atTop
            (nhds (toWeakSpace ℝ H q)) := by simpa [Function.comp_def] using hs
        rw [weakConvergence_iff_forall_tendsto_inner_right] at hs' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (s j + 1) - u (s j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp hsTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (s j + 1) - u (s j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (hs' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have huinner : Filter.Tendsto (fun j =>
          inner ℝ (u (t j + 1) - u (s j + 1)) (q - p)) Filter.atTop
          (nhds (-‖p - q‖ ^ 2)) := by
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht1 hs1
        have hinner := ((ht1 (q - p)).sub (hs1 (q - p)))
        convert hinner using 1
        · ext j
          simp [inner_sub_left]
        · rw [← real_inner_self_eq_norm_sq (p - q)]
          simp only [inner_sub_left, inner_sub_right]
          ring_nf
      have hrtp := (hresidual_inner p hpS).comp htTop
      have hrsp := (hresidual_inner p hpS).comp hsTop
      have hrtq := (hresidual_inner q hqS).comp htTop
      have hrsq := (hresidual_inner q hqS).comp hsTop
      have hresfour := ((hrtp.sub hrsp).sub hrtq).add hrsq
      have hgradt := hgrad (fun j => u (t j + 2)) p ht2
      have hgrads := hgrad (fun j => u (s j + 2)) q hs2
      have hgradinner : Filter.Tendsto (fun j => inner ℝ
          (gradPsi (u (t j + 2)) - gradPsi (u (s j + 2))) (q - p))
          Filter.atTop (nhds (inner ℝ (gradPsi p - gradPsi q) (q - p))) := by
        rw [weakConvergence_iff_forall_tendsto_inner_right] at hgradt hgrads
        convert (hgradt (q - p)).sub (hgrads (q - p)) using 1 <;>
          simp [inner_sub_left]
      have hzinner : Filter.Tendsto (fun j => inner ℝ
          (zSequence u y a b lam (t j + 2) (by omega) -
            zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds (inner ℝ (gradPsi p - gradPsi q) (q - p))) := by
        have hsum := hgradinner.add hresfour
        convert hsum using 1
        · ext j
          simp only [Function.comp_apply, inner_sub_left, inner_sub_right, Nat.add_comm]
          ring
        · simp
      have hcombined :=
        (huinner.const_mul ((a + b) / lam)).sub
          (hzinner.const_mul (1 / lam + b))
      have heq : (0 : ℝ) = ((a + b) / lam) * (-‖p - q‖ ^ 2) -
          (1 / lam + b) * inner ℝ (gradPsi p - gradPsi q) (q - p) :=
        tendsto_nhds_unique hidentity hcombined
      have hminimizer_subgradient (x : H) (hx : x ∈ Optimization.argminSet Θ) :
          -gradPsi x ∈ subdifferential phi x := by
        intro z
        by_cases hz_top : phi z = ⊤
        · rw [hz_top]
          exact le_top
        have hx_top : phi x ≠ ⊤ := by
          have hxdom := minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hx
          exact (ERealFunction.mem_dom_iff phi x).mp hxdom |>.ne
        have hx_bot : phi x ≠ ⊥ := hH.phi_proper.1 x
        have hz_bot : phi z ≠ ⊥ := hH.phi_proper.1 z
        let d : H := z - x
        let X : ℝ := (phi x).toReal
        let Z : ℝ := (phi z).toReal
        let P : ℝ → ℝ := fun t => psi (x + t • d)
        have hxE : phi x = (X : EReal) := by
          symm
          exact EReal.coe_toReal hx_top hx_bot
        have hzE : phi z = (Z : EReal) := by
          symm
          exact EReal.coe_toReal hz_top hz_bot
        have hchord : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            (phi (x + t • d)).toReal ≤ (1 - t) * X + t * Z := by
          intro t ht0 ht1
          have hxepi : (x, X) ∈ ERealFunction.epigraph phi := by
            rw [ERealFunction.mem_epigraph_iff, hxE]
          have hzepi : (z, Z) ∈ ERealFunction.epigraph phi := by
            rw [ERealFunction.mem_epigraph_iff, hzE]
          have hcomb := hH.phi_convex hxepi hzepi (by linarith) ht0 (by ring : (1 - t) + t = 1)
          change ((1 - t) • x + t • z, (1 - t) * X + t * Z) ∈
            ERealFunction.epigraph phi at hcomb
          rw [show (1 - t) • x + t • z = x + t • d by dsimp [d]; module,
            ERealFunction.mem_epigraph_iff] at hcomb
          have hpoint_top : phi (x + t • d) ≠ ⊤ := by
            intro htop
            rw [htop] at hcomb
            exact (EReal.coe_ne_top _ ) (top_unique hcomb)
          exact EReal.toReal_le_toReal hcomb (hH.phi_proper.1 _) (EReal.coe_ne_top _)
        have hquot : ∀ t : ℝ, 0 < t → t < 1 →
            -(P t - P 0) / t ≤ Z - X := by
          intro t ht ht1
          have hmin := (Optimization.mem_argminSet_iff Θ x).mp hx (x + t • d)
          have hpoint_top : phi (x + t • d) ≠ ⊤ := by
            have hxepi : (x, X) ∈ ERealFunction.epigraph phi := by
              rw [ERealFunction.mem_epigraph_iff, hxE]
            have hzepi : (z, Z) ∈ ERealFunction.epigraph phi := by
              rw [ERealFunction.mem_epigraph_iff, hzE]
            have hupper := hH.phi_convex hxepi hzepi (by linarith) ht.le
              (by ring : (1 - t) + t = 1)
            change ((1 - t) • x + t • z, (1 - t) * X + t * Z) ∈
              ERealFunction.epigraph phi at hupper
            rw [show (1 - t) • x + t • z = x + t • d by dsimp [d]; module,
              ERealFunction.mem_epigraph_iff] at hupper
            intro htop
            rw [htop] at hupper
            exact (EReal.coe_ne_top _) (top_unique hupper)
          have htheta_x : Θ x = ((X + P 0 : ℝ) : EReal) := by
            rw [hH.theta_eq, hxE]
            simp [P]
          have htheta_point : Θ (x + t • d) =
              (((phi (x + t • d)).toReal + P t : ℝ) : EReal) := by
            rw [hH.theta_eq]
            rw [← EReal.coe_toReal hpoint_top (hH.phi_proper.1 _)]
            simp [P]
          rw [htheta_x, htheta_point] at hmin
          have hreal := EReal.coe_le_coe_iff.mp hmin
          have hphi := hchord t ht.le ht1.le
          have htne : t ≠ 0 := ne_of_gt ht
          apply (div_le_iff₀ ht).2
          linarith [hphi]
        have hPderiv : HasDerivAt P (inner ℝ (gradPsi x) d) 0 := by
          exact hasDerivAt_line_restrict_local psi gradPsi x d hH.psi_differentiable
            hH.psi_gradient
        have hslope : Filter.Tendsto (fun t : ℝ => -(P t - P 0) / t)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (-inner ℝ (gradPsi x) d)) := by
          have ht := hPderiv.tendsto_slope_zero_right.neg
          convert ht using 1
          · ext t
            simp [slope, div_eq_mul_inv]
            ring
        have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            -(P t - P 0) / t ≤ Z - X := by
          have hlt : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
          filter_upwards [self_mem_nhdsWithin, hlt] with t htpos htone
          exact hquot t htpos htone
        have hlim := le_of_tendsto hslope hevent
        rw [hxE, hzE]
        norm_cast
        dsimp [d, X, Z] at hlim ⊢
        have hreal : inner ℝ (z - x) (-gradPsi x) + (phi x).toReal ≤
            (phi z).toReal := by
          rw [inner_neg_right, real_inner_comm]
          linarith [hlim]
        simpa using (EReal.coe_le_coe_iff.mpr hreal)
      have hp_sub := hminimizer_subgradient p hpS
      have hq_sub := hminimizer_subgradient q hqS
      have hmono := (isMonotone_subdifferential phi hH.phi_proper)
        (-gradPsi p) hp_sub (-gradPsi q) hq_sub
      have hgrad_nonpos : inner ℝ (gradPsi p - gradPsi q) (q - p) ≥ 0 := by
        calc
          0 ≤ inner ℝ ((-gradPsi p) - (-gradPsi q)) (p - q) := hmono
          _ = inner ℝ (gradPsi p - gradPsi q) (q - p) := by
            simp only [inner_sub_left, inner_sub_right, inner_neg_left]
            ring
      have hcoef : 0 < (a + b) / lam :=
        div_pos (by linarith [hH.a_pos, hH.b_pos]) hH.step_pos
      have hzcoef : 0 < 1 / lam + b := by
        nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
      have hnormzero : ‖p - q‖ = 0 := by
        have hfirst : 0 ≤ ((a + b) / lam) * ‖p - q‖ ^ 2 :=
          mul_nonneg hcoef.le (sq_nonneg _)
        have hsecond : 0 ≤ (1 / lam + b) * inner ℝ (gradPsi p - gradPsi q) (q - p) :=
          mul_nonneg hzcoef.le hgrad_nonpos
        have hz : ((a + b) / lam) * ‖p - q‖ ^ 2 = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left hcoef.ne' |> sq_eq_zero_iff.mp
      exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with ⟨q, hq⟩
    have hqcluster : IsSequentialClusterPt
        (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) :=
      ⟨id, strictMono_id, by simpa using hq⟩
    exact ⟨q, hcluster q hqcluster, hq⟩
  · have hpsiConv : ConvexOn ℝ Set.univ psi := by
      apply convexOn_of_convex_epigraph
      simpa [ERealFunction.epigraph] using hpsi
    have hpsiSupport : ∀ x z : H,
        psi x - psi z ≤ inner ℝ (gradPsi x) (x - z) := by
      intro x z
      let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z x
      have hline : HasDerivAt line (x - z) 1 := by
        convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - z)).add_const z using 1 <;> simp
      have hc : ConvexOn ℝ Set.univ (psi ∘ line) := by
        simpa [line] using hpsiConv.comp_affineMap line
      have hd : HasDerivAt (psi ∘ line) (inner ℝ (gradPsi x) (x - z)) 1 := by
        have hx : HasFDerivAt psi (fderiv ℝ psi x) (line 1) := by
          simpa [line] using hH.psi_differentiable x |>.hasFDerivAt
        have hcomp := hx.comp_hasDerivAt 1 hline
        simpa [line, hH.psi_gradient x, innerSL_apply_apply] using hcomp
      have hslope := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
        (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hd
      simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using hslope
    have hphiFinite (j : ℕ) (hj : 1 ≤ j) : phi (u j) ≠ ⊤ ∧ phi (u j) ≠ ⊥ := by
      have hz := theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB j hj
      constructor
      · exact subgradient_value_ne_top hH.phi_proper hz
      · exact hH.phi_proper.1 _
    have hGtel (q : H) (hq : q ∈ Optimization.argminSet Θ) :
        ∀ n m : ℕ, ∀ hn : 2 ≤ n, ∀ hnm : n ≤ m,
          auxiliaryG u y a b lam q n hn -
              auxiliaryG u y a b lam q m (le_trans hn hnm) -
              inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q) ≤
            (phi q).toReal - (phi (u m)).toReal := by
      intro n m hn hnm
      have hqtop : phi q ≠ ⊤ :=
        (ERealFunction.mem_dom_iff phi q).mp
          (minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq) |>.ne
      induction m, hnm using Nat.le_induction with
      | base =>
          have hs : phi (u n) +
              (inner ℝ (q - u n) (-zSequence u y a b lam n (by omega)) : EReal) ≤
                phi q := by
            simpa [add_comm] using
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                n (by omega)) q
          have hleftbot : phi (u n) +
              (inner ℝ (q - u n) (-zSequence u y a b lam n (by omega)) : EReal) ≠ ⊥ :=
            EReal.add_ne_bot_iff.mpr ⟨(hphiFinite n (by omega)).2, EReal.coe_ne_bot _⟩
          have hsreal := EReal.toReal_le_toReal hs hleftbot hqtop
          rw [EReal.toReal_add (hphiFinite n (by omega)).1 (hphiFinite n (by omega)).2
            (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsreal
          norm_num at hsreal
          rw [show q - u n = -(u n - q) by abel, inner_neg_left,
            real_inner_comm (zSequence u y a b lam n (by omega)) (u n - q)] at hsreal
          simp only [inner_neg_left]
          linarith
      | succ m hnm ih =>
          have hm : 2 ≤ m := le_trans hn hnm
          have hs : phi (u (m + 1)) +
              (inner ℝ (u m - u (m + 1))
                (-zSequence u y a b lam (m + 1) (by omega)) : EReal) ≤ phi (u m) := by
            simpa [add_comm] using
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                (m + 1) (by omega)) (u m)
          have hleftbot : phi (u (m + 1)) +
              (inner ℝ (u m - u (m + 1))
                (-zSequence u y a b lam (m + 1) (by omega)) : EReal) ≠ ⊥ :=
            EReal.add_ne_bot_iff.mpr
              ⟨(hphiFinite (m + 1) (by omega)).2, EReal.coe_ne_bot _⟩
          have hsreal := EReal.toReal_le_toReal
            hs hleftbot (hphiFinite m (by omega)).1
          rw [EReal.toReal_add (hphiFinite (m + 1) (by omega)).1
            (hphiFinite (m + 1) (by omega)).2
            (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsreal
          norm_num at hsreal
          have hinc := auxiliaryG_increment u y a b lam q (m - 1) (by omega)
          have hvel : velocity u (m + 1) (by omega) = u (m + 1) - u m := by
            rw [velocity_eq_sub_of_one_le]
            simp
          have hm1 : m - 1 + 1 = m := by omega
          have hm2 : m - 1 + 2 = m + 1 := by omega
          simp only [hm1, hm2] at hinc
          rw [hvel] at hinc
          calc
            auxiliaryG u y a b lam q n (by omega) -
                  auxiliaryG u y a b lam q (m + 1) (by omega) -
                  inner ℝ (-zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - q) =
                (auxiliaryG u y a b lam q n (by omega) -
                  auxiliaryG u y a b lam q m (by omega) -
                  inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q)) +
                  inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - u m) := by
                    simp only [inner_neg_left]
                    linear_combination -hinc
            _ ≤ ((phi q).toReal - (phi (u m)).toReal) +
                  inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - u m) := by
                      have ih' : auxiliaryG u y a b lam q n (by omega) -
                          auxiliaryG u y a b lam q m (by omega) -
                          inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q) ≤
                            (phi q).toReal - (phi (u m)).toReal := by
                        simpa only using ih
                      have hadd := add_le_add_right ih'
                        (inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                          (u (m + 1) - u m))
                      simpa only [add_comm] using hadd
            _ ≤ (phi q).toReal - (phi (u (m + 1))).toReal := by
              have hsreal' : inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                  (u (m + 1) - u m) ≤
                  (phi (u m)).toReal - (phi (u (m + 1))).toReal := by
                rw [show u m - u (m + 1) = -(u (m + 1) - u m) by abel,
                  inner_neg_left,
                  real_inner_comm (zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - u m)] at hsreal
                linarith
              linarith
    have hGgap (q : H) (hq : q ∈ Optimization.argminSet Θ) :
        ∀ n m : ℕ, ∀ hn : 2 ≤ n, ∀ hnm : n ≤ m,
          auxiliaryG u y a b lam q n hn -
              auxiliaryG u y a b lam q m (le_trans hn hnm) ≤
            (Θ q).toReal - (Θ (u m)).toReal +
              (1 / b) * (liapunovF u y a b lam q (m - 1) (by omega) -
                liapunovF u y a b lam q m (by omega)) := by
      intro n m hn hnm
      have hm : 2 ≤ m := le_trans hn hnm
      have hb : b ≠ 0 := ne_of_gt hH.b_pos
      have htel := hGtel q hq n m hn hnm
      have hinc := (theorem1_proposition3_local phi Θ psi gradPsi u y a b lam Lpsi q
        (m - 1) hH hIFB (by omega) hH.theta_convex).2.1
      have hres : inner ℝ
          (zSequence u y a b lam m (by omega) - gradPsi (u m)) (u m - q) =
          (1 / b) * (liapunovF u y a b lam q m (by omega) -
            liapunovF u y a b lam q (m - 1) (by omega)) := by
        have hvec := theorem1_residual_vector phi psi gradPsi a b lam u y hIFB (m - 2)
        have hmidx : m - 2 + 2 = m := by omega
        simp only [hmidx] at hvec
        rw [hvec]
        simp only [show m - 1 + 1 = m by omega] at hinc
        rw [← hinc]
        field_simp [hb]
      have hpsiB := hpsiSupport (u m) q
      have hendpoint : inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q) ≤
          (1 / b) * (liapunovF u y a b lam q (m - 1) (by omega) -
            liapunovF u y a b lam q m (by omega)) + psi q - psi (u m) := by
        rw [show -zSequence u y a b lam m (by omega) =
          -(zSequence u y a b lam m (by omega) - gradPsi (u m)) - gradPsi (u m) by abel,
          inner_sub_left, inner_neg_left, hres]
        linarith
      have hqtop : phi q ≠ ⊤ :=
        (ERealFunction.mem_dom_iff phi q).mp
          (minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq) |>.ne
      have hqbot : phi q ≠ ⊥ := hH.phi_proper.1 q
      have hthetaq : (Θ q).toReal = (phi q).toReal + psi q := by
        rw [hH.theta_eq, EReal.toReal_add hqtop hqbot
          (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
        simp
      have hthetam : (Θ (u m)).toReal = (phi (u m)).toReal + psi (u m) := by
        rw [hH.theta_eq, EReal.toReal_add (hphiFinite m (by omega)).1
          (hphiFinite m (by omega)).2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
        simp
      rw [hthetaq, hthetam]
      linarith
    have hdist : ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
        Filter.Tendsto (fun k ↦ ‖u k - q‖) Filter.atTop (nhds l) := by
      intro q hq
      rcases hAlim q hq with ⟨lA, hlA⟩
      rcases hFlim q hq with ⟨lF, hlF⟩
      have hqeq : Θ q = sInf (Set.range Θ) :=
        (Optimization.mem_argminSet_iff_eq_sInf Θ q).mp hq
      have hqtop : Θ q ≠ ⊤ := by
        rw [hH.theta_eq]
        exact EReal.add_ne_top
          ((ERealFunction.mem_dom_iff phi q).mp
            (minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq) |>.ne)
          (EReal.coe_ne_top _)
      have hqbot : Θ q ≠ ⊥ := by
        rw [hH.theta_eq]
        exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 q, EReal.coe_ne_bot _⟩
      have htheta : Filter.Tendsto (fun k : ℕ => (Θ (u k)).toReal)
          Filter.atTop (nhds ((Θ q).toReal)) := by
        have hobjectiveq : Filter.Tendsto (fun k : ℕ => Θ (u k))
            Filter.atTop (nhds (Θ q)) := by
          simpa only [hqeq] using hobjective
        exact (EReal.tendsto_toReal hqtop hqbot).comp hobjectiveq
      let c : ℝ := (a + b) / (2 * lam)
      let d : ℕ → ℝ := fun k => ‖u (k + 1) - q‖ ^ 2
      let e : ℕ → ℝ := fun m =>
        (1 / lam + b) * ((Θ q).toReal - (Θ (u (m + 2))).toReal +
          (1 / b) * (liapunovF u y a b lam q (m + 1) (by omega) -
            liapunovF u y a b lam q (m + 2) (by omega)))
      have hc : 0 < c := by
        dsimp [c]
        exact div_pos (by linarith [hH.a_pos, hH.b_pos])
          (mul_pos (by norm_num) hH.step_pos)
      have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
        have htheta2 := htheta.comp (Filter.tendsto_add_atTop_nat 2)
        have hF2 := hlF.comp (Filter.tendsto_add_atTop_nat 1)
        have hsubF := hlF.sub hF2
        have hzeroTheta : Filter.Tendsto
            (fun m : ℕ => (Θ q).toReal - (Θ (u (m + 2))).toReal)
            Filter.atTop (nhds 0) := by
          convert tendsto_const_nhds.sub htheta2 using 1 <;> simp
        dsimp [e]
        convert (hzeroTheta.add (hsubF.const_mul (1 / b))).const_mul (1 / lam + b)
          using 1 <;> simp
      have hineq (n m : ℕ) (hnm : n ≤ m) :
          c * d n ≤ c * d m +
            (theorem1AuxiliaryA u y a b lam q n -
              theorem1AuxiliaryA u y a b lam q m) + e m := by
        have hg := hGgap q hq (n + 2) (m + 2) (by omega) (by omega)
        dsimp [c, d, e, theorem1AuxiliaryA]
        have hn1 : n + 2 - 1 = n + 1 := by omega
        have hm1 : m + 2 - 1 = m + 1 := by omega
        simp only [hn1, hm1] at hg
        have hzcoef : 0 ≤ 1 / lam + b := by
          nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
        have hgmul := mul_le_mul_of_nonneg_left hg hzcoef
        linarith [hgmul]
      rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨R, hR⟩
      let B : ℝ := (R + ‖q‖) ^ 2
      have hdmem : ∀ k, d k ∈ Set.Icc 0 B := by
        intro k
        constructor
        · exact sq_nonneg _
        · have hk : ‖u (k + 1) - q‖ ≤ R + ‖q‖ := by
            calc
              ‖u (k + 1) - q‖ ≤ ‖u (k + 1)‖ + ‖q‖ := norm_sub_le _ _
              _ ≤ R + ‖q‖ := by
                linarith [hR _ (Set.mem_range_self (k + 1))]
          have hRnonneg : 0 ≤ R := by
            linarith [hR _ (Set.mem_range_self 0), norm_nonneg (u 0)]
          exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hk
      have hdcluster : ∀ r s : ℝ,
          IsSequentialClusterPt d r → IsSequentialClusterPt d s → r = s := by
        intro r s hr hs
        have hrs : r ≤ s := by
          rcases hr with ⟨t, htmono, ht⟩
          rcases hs with ⟨v, hvmono, hv⟩
          have htTop := htmono.tendsto_atTop
          have hvTop := hvmono.tendsto_atTop
          have hvcomp : Filter.Tendsto (d ∘ (v ∘ t)) Filter.atTop (nhds s) := by
            exact hv.comp htTop
          have hleft := (ht.const_mul c).sub (hvcomp.const_mul c)
          have heright := he.comp (hvTop.comp htTop)
          have hAdiff := (hlA.comp htTop).sub (hlA.comp (hvTop.comp htTop))
          have hright := hAdiff.add heright
          have hle : ∀ᶠ j : ℕ in Filter.atTop,
              c * d (t j) - c * d (v (t j)) ≤
                (theorem1AuxiliaryA u y a b lam q (t j) -
                  theorem1AuxiliaryA u y a b lam q (v (t j))) + e (v (t j)) := by
            filter_upwards [] with j
            linarith [hineq (t j) (v (t j))
              (StrictMono.id_le hvmono (t j))]
          have hlimle := le_of_tendsto_of_tendsto hleft hright hle
          have : c * r - c * s ≤ 0 := by simpa [Function.comp_def] using hlimle
          nlinarith
        have hsr : s ≤ r := by
          rcases hs with ⟨t, htmono, ht⟩
          rcases hr with ⟨v, hvmono, hv⟩
          have htTop := htmono.tendsto_atTop
          have hvTop := hvmono.tendsto_atTop
          have hvcomp : Filter.Tendsto (d ∘ (v ∘ t)) Filter.atTop (nhds r) := by
            exact hv.comp htTop
          have hleft := (ht.const_mul c).sub (hvcomp.const_mul c)
          have heright := he.comp (hvTop.comp htTop)
          have hAdiff := (hlA.comp htTop).sub (hlA.comp (hvTop.comp htTop))
          have hright := hAdiff.add heright
          have hle : ∀ᶠ j : ℕ in Filter.atTop,
              c * d (t j) - c * d (v (t j)) ≤
                (theorem1AuxiliaryA u y a b lam q (t j) -
                  theorem1AuxiliaryA u y a b lam q (v (t j))) + e (v (t j)) := by
            filter_upwards [] with j
            linarith [hineq (t j) (v (t j))
              (StrictMono.id_le hvmono (t j))]
          have hlimle := le_of_tendsto_of_tendsto hleft hright hle
          have : c * s - c * r ≤ 0 := by simpa [Function.comp_def] using hlimle
          nlinarith
        exact le_antisymm hrs hsr
      rcases isCompact_Icc.isSeqCompact hdmem with ⟨r, hrmem, t, htmono, ht⟩
      have hdlim : Filter.Tendsto d Filter.atTop (nhds r) :=
        tendsto_of_unique_sequential_cluster_point isCompact_Icc.isSeqCompact hdmem
          (fun s hs => hdcluster s r hs ⟨t, htmono, ht⟩)
      refine ⟨Real.sqrt r, ?_⟩
      have hsqrt := (Real.continuous_sqrt.tendsto r).comp hdlim
      have hshift : Filter.Tendsto (fun k : ℕ => ‖u (k + 1) - q‖)
          Filter.atTop (nhds (Real.sqrt r)) := by
        convert hsqrt using 1
        ext k
        dsimp [d]
        rw [Real.sqrt_sq (norm_nonneg _)]
      exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by
        simpa only [Nat.add_comm] using hshift)
    exact opial_lemma hS u hdist hcluster

end AttouchPeypouquetRedont2014
