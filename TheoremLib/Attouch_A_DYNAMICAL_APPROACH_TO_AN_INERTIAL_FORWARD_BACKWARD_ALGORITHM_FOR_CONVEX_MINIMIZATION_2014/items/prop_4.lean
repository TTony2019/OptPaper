import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_4
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_8
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.lem_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_1
import Foundation.Convex.WeakClosed

namespace AttouchPeypouquetRedont2014

open ERealFunction

/-- Removing a finite initial segment does not change the limit of a sequence. -/
private theorem tendsto_of_tendsto_nat_succ {X : Type*} [TopologicalSpace X]
    {f : ℕ → X} {x : X}
    (h : Filter.Tendsto (fun k : ℕ ↦ f (k + 1)) Filter.atTop (nhds x)) :
    Filter.Tendsto f Filter.atTop (nhds x) := by
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  rcases Filter.eventually_atTop.1 (h s hs) with ⟨N, hN⟩
  apply Filter.eventually_atTop.2
  refine ⟨N + 1, fun k hk ↦ ?_⟩
  have hk' : k - 1 ≥ N := by omega
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hN (k - 1) hk'

/-- Adding a continuous real-valued perturbation preserves lower semicontinuity in `EReal`. -/
private theorem lowerSemicontinuous_add_real_coe {X : Type*} [TopologicalSpace X]
    (f : X → EReal) (g : X → ℝ) (hf : LowerSemicontinuous f) (hg : Continuous g) :
    LowerSemicontinuous (fun x ↦ f x + (g x : EReal)) := by
  have hg' : LowerSemicontinuous (fun x ↦ (g x : EReal)) :=
    (continuous_coe_real_ereal.comp hg).lowerSemicontinuous
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    f x + (g x : EReal) ≤
        Filter.liminf f (nhds x) + Filter.liminf (fun y ↦ (g y : EReal)) (nhds x) :=
      add_le_add (hf.le_liminf x) (hg'.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ f y + (g y : EReal)) (nhds x) := by
      simpa using (EReal.le_liminf_add :
        Filter.liminf f (nhds x) + Filter.liminf (fun y ↦ (g y : EReal)) (nhds x) ≤
          Filter.liminf (f + fun y ↦ (g y : EReal)) (nhds x))

/-- The objective in Hypothesis H is lower semicontinuous. -/
private theorem theta_lowerSemicontinuous {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi) :
    LowerSemicontinuous Θ := by
  have hphi : LowerSemicontinuous phi :=
    (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph phi).mpr
      hH.phi_lower_semicontinuous
  have hpsi : Continuous psi := hH.psi_differentiable.continuous
  have htheta : Θ = fun x ↦ phi x + (psi x : EReal) := funext hH.theta_eq
  rw [htheta]
  exact lowerSemicontinuous_add_real_coe phi psi hphi hpsi

/-- Values of the objective along an IFB trajectory are finite. -/
private theorem theta_trajectory_finite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (n : ℕ) :
    Θ (u (n + 1)) ≠ ⊤ ∧ Θ (u (n + 1)) ≠ ⊥ := by
  obtain ⟨g, hg, -⟩ := hIFB.first_update n
  have hphitop : phi (u (n + 1)) ≠ ⊤ := by
    obtain ⟨w, hw⟩ := hH.phi_proper.2
    have hwtop : phi w < ⊤ := (ERealFunction.mem_dom_iff phi w).mp hw
    intro htop
    have hs : phi (u (n + 1)) + (inner ℝ g (w - u (n + 1)) : EReal) ≤ phi w := by
      simpa [real_inner_comm, add_comm] using hg w
    rw [htop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hs
    exact (not_le_of_gt hwtop) hs
  have hphibot : phi (u (n + 1)) ≠ ⊥ := hH.phi_proper.1 _
  constructor
  · rw [hH.theta_eq]
    exact EReal.add_ne_top hphitop (EReal.coe_ne_top _)
  · rw [hH.theta_eq]
    exact EReal.add_ne_bot_iff.mpr ⟨hphibot, EReal.coe_ne_bot _⟩

/-- Properness of `phi` prevents the objective from attaining `-∞`. -/
private theorem theta_ne_bot {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (x : H) : Θ x ≠ ⊥ := by
  rw [hH.theta_eq]
  exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 x, EReal.coe_ne_bot _⟩

/-- Real lower level sets of the convex objective are convex. -/
private theorem convex_lowerLevelSet_theta {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Θ : H → EReal) (r : ℝ)
    (hconvex : Convex ℝ (ERealFunction.epigraph Θ)) :
    Convex ℝ (ERealFunction.lowerLevelSet Θ r) := by
  intro x hx y hy s t hs ht hst
  have hep := hconvex (show (x, r) ∈ ERealFunction.epigraph Θ from hx)
    (show (y, r) ∈ ERealFunction.epigraph Θ from hy) hs ht hst
  change Θ (s • x + t • y) ≤ ((s • r + t • r : ℝ) : EReal) at hep
  change Θ (s • x + t • y) ≤ (r : EReal)
  convert hep using 1
  norm_cast
  have hr : s * r + t * r = r := by
    rw [← add_mul, hst]
    simp
  exact hr.symm

/-- If no weak sequential cluster point exists, the norms escape every bounded ball. -/
private theorem tendsto_norm_atTop_of_no_weak_cluster {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (u : ℕ → H)
    (hno : ∀ q : H, ¬ IsSequentialClusterPt
      (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q)) :
    Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop Filter.atTop := by
  by_contra hT
  rw [Filter.tendsto_atTop] at hT
  push Not at hT
  obtain ⟨R, hR⟩ := hT
  have hR' : ∀ N : ℕ, ∃ n ≥ N, ‖u n‖ < R := Filter.frequently_atTop.mp hR
  have hlarge : ∀ N : ℕ, ∃ n > N, ‖u n‖ < R := by
    intro N
    rcases hR' (N + 1) with ⟨n, hn, hnorm⟩
    exact ⟨n, lt_of_lt_of_le (by omega) hn, hnorm⟩
  obtain ⟨σ, hσ, hbound⟩ := Nat.exists_strictMono_subsequence hlarge
  have hbounded : Bornology.IsBounded (Set.range fun n ↦ u (σ n)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max R 0, ?_⟩
    rintro z ⟨n, rfl⟩
    exact le_trans (le_of_lt (hbound n)) (le_max_left _ _)
  obtain ⟨q, τ, hτ, hweak⟩ :=
    bounded_sequence_has_weakly_convergent_subsequence (fun n ↦ u (σ n)) hbounded
  apply hno q
  refine ⟨σ.comp τ, hσ.comp hτ, ?_⟩
  simpa [Function.comp_def] using hweak

/-- A finite interval of positive velocity squares is controlled by the square-summable
velocity series.  This is the indexing normalization needed in the Liapunov estimate. -/
private theorem velocity_Icc_sum_le_tsum_local {H : Type*} [NormedAddCommGroup H]
    (u : ℕ → H) (hsq : Summable (fun n : ℕ ↦ ‖u (n + 1) - u n‖ ^ 2))
    (k : ℕ) (_hk : 1 ≤ k) :
    ∑ i ∈ (Finset.Icc 2 k).attach,
      ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2 ≤ ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2 := by
  classical
  let f : ℕ → ℝ := fun n ↦ ‖u (n + 1) - u n‖ ^ 2
  let s : Finset ℕ := (Finset.Icc 2 k).image (fun i ↦ i - 1)
  have hsum :
      (∑ i ∈ (Finset.Icc 2 k).attach,
        ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2) = ∑ n ∈ s, f n := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 k).attach, f (i.1 - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi2 : 2 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
        have hpred : i.1 - 1 + 1 = i.1 := by omega
        simp [f, velocity, hpred]
      _ = ∑ i ∈ Finset.Icc 2 k, f (i - 1) := by
        simpa only using Finset.sum_attach (Finset.Icc 2 k) (fun i ↦ f (i - 1))
      _ = ∑ n ∈ s, f n := by
        symm
        apply (Finset.sum_image _)
        intro i hi j hj hij
        have hii : 2 ≤ i := (Finset.mem_Icc.mp hi).1
        have hjj : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        change i - 1 = j - 1 at hij
        omega
  rw [hsum]
  exact hsq.sum_le_tsum s (fun n _ ↦ sq_nonneg _)

/-- The bound supplied by Proposition 4, with its proof-index argument kept explicit. -/
private theorem auxiliaryG_le_of_proposition4_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (q : H)
    (hq : q ∈ ERealFunction.dom phi) :
    ∃ M : ℝ, ∀ j (hj : 2 ≤ j), auxiliaryG u y a b lam q j hj ≤ M :=
  proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hq

/-- The distance increment is bounded by the Liapunov quantity, up to a
constant depending on the comparison point.  This is (3.22) in the paper. -/
private theorem liapunov_distance_increment_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (q : H)
    (hq : q ∈ ERealFunction.dom phi) :
    ∃ C : ℝ, ∀ k : ℕ, ∀ hk : 1 ≤ k,
      ((1 + b * lam) / (2 * lam ^ 2)) * ‖u (k + 1) - q‖ ^ 2 -
          ((1 + b * lam) / (2 * lam ^ 2)) * ‖u k - q‖ ^ 2 ≤
        liapunovF u y a b lam q k hk - C := by
  classical
  obtain ⟨M, hG⟩ := auxiliaryG_le_of_proposition4_local phi Θ psi gradPsi a b lam Lpsi
    u y hH hIFB q hq
  obtain ⟨_, hsq, _⟩ := proposition2 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
  let S : ℝ := ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2
  let A : ℝ := (a + b) / (2 * lam)
  let c : ℝ := 1 / lam + b
  let α : ℝ := (1 + b * lam) / (2 * lam ^ 2)
  let δ : ℝ := (2 + (b - a) * lam) / (2 * lam ^ 2)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun n ↦ sq_nonneg _)
  have hA : 0 < A := by
    dsimp [A]
    apply div_pos <;> nlinarith [hH.a_pos, hH.b_pos, hH.step_pos]
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
  have hα : 0 < α := by
    dsimp [α]
    apply div_pos <;> nlinarith [hH.b_pos, hH.step_pos]
  refine ⟨-(c * M + α * S + |δ| * S), ?_⟩
  intro k hk
  have hvel : ‖velocity u (k + 1) (by omega)‖ ^ 2 ≤ S := by
    rw [velocity_eq_sub_of_one_le]
    dsimp [S]
    simpa using hsq.sum_le_tsum ({k} : Finset ℕ) (fun _ _ ↦ sq_nonneg _)
  have hsum : ∑ i ∈ (Finset.Icc 2 k).attach,
      ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2 ≤ S :=
    velocity_Icc_sum_le_tsum_local u hsq k hk
  have hsum0 : 0 ≤ ∑ i ∈ (Finset.Icc 2 k).attach,
      ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2 := by
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hGk := hG (k + 1) (by omega)
  have hpolar : 2 * inner ℝ (velocity u (k + 1) (by omega)) (u k - q) =
      ‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2 - ‖velocity u (k + 1) (by omega)‖ ^ 2 := by
    rw [velocity_eq_sub_of_one_le u (k + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    have hrewrite : u (k + 1) - q = (u (k + 1) - u k) + (u k - q) := by abel
    rw [hrewrite, norm_add_sq_real]
    ring
  have hGbound : -c * M ≤ -c * auxiliaryG u y a b lam q (k + 1) (by omega) := by
    nlinarith [mul_le_mul_of_nonneg_left hGk hc.le]
  have hvelbound : -α * S ≤ -α * ‖velocity u (k + 1) (by omega)‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hvel hα.le]
  have hsumbound : -|δ| * S ≤ -δ * ∑ i ∈ (Finset.Icc 2 k).attach,
      ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2 := by
    by_cases hδ : 0 ≤ δ
    · have h1 := mul_le_mul_of_nonneg_left hsum hδ
      have habs : |δ| = δ := abs_of_nonneg hδ
      rw [habs]
      linarith
    · have hδ' : δ ≤ 0 := le_of_not_ge hδ
      have h1 := mul_le_mul_of_nonpos_left hsum0 hδ'
      have habs : -δ ≤ |δ| := neg_le_abs δ
      nlinarith
  unfold liapunovF
  change α * ‖u (k + 1) - q‖ ^ 2 - α * ‖u k - q‖ ^ 2 ≤
    (A * ‖u k - q‖ ^ 2 - c * auxiliaryG u y a b lam q (k + 1) (by omega) -
      δ * ∑ i ∈ (Finset.Icc 2 k).attach,
        ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 +
      2 * α * inner ℝ (velocity u (k + 1) (by omega)) (u k - q)) -
      -(c * M + α * S + |δ| * S)
  rw [show 2 * α * inner ℝ (velocity u (k + 1) (by omega)) (u k - q) =
      α * (‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2 -
        ‖velocity u (k + 1) (by omega)‖ ^ 2) by rw [← hpolar]; ring]
  have hdist : 0 ≤ ‖u k - q‖ ^ 2 := sq_nonneg _
  nlinarith

/-- A limit of a nonincreasing sequence is below each of its terms. -/
private theorem energy_limit_le_local (E : ℕ → EReal) (e : EReal)
    (hmono : ∀ k, E (k + 1) ≤ E k)
    (hlim : Filter.Tendsto E Filter.atTop (nhds e)) : ∀ k, e ≤ E k := by
  intro k
  apply le_of_tendsto hlim
  apply Filter.eventually_atTop.2
  refine ⟨k, fun n hn ↦ ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans (hmono n) ih

/-- Reindexing a velocity-square series only changes its harmless zeroth term. -/
private theorem summable_predecessor_velocity_error_local {H : Type*}
    [NormedAddCommGroup H] (u : ℕ → H) (c : ℝ)
    (hs : Summable (fun n : ℕ ↦ c * ‖u (n + 1) - u n‖ ^ 2)) :
    Summable (fun k : ℕ ↦ if _ : 1 ≤ k then
      c * ‖u k - u (k - 1)‖ ^ 2 else 0) := by
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_sub_cancel] using hs

private theorem norm_difference_polarization_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x q d : H) :
    2 * inner ℝ d (x + d - q) = ‖x + d - q‖ ^ 2 - ‖x - q‖ ^ 2 + ‖d‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, real_inner_comm]
  ring

private theorem ifb_update_vector_identity_local {H : Type*} [NormedAddCommGroup H]
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

private theorem subgradient_value_ne_top_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {phi : H → EReal} (hproper : ERealFunction.IsProper phi)
    {x g : H} (hg : g ∈ subdifferential phi x) : phi x ≠ ⊤ := by
  obtain ⟨r, hr⟩ := hproper.2
  have hr_top : phi r < ⊤ := (ERealFunction.mem_dom_iff phi r).mp hr
  intro hx_top
  have hs : phi x + (inner ℝ g (r - x) : EReal) ≤ phi r := by
    simpa [real_inner_comm, add_comm] using hg r
  rw [hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hs
  exact (not_le_of_gt hr_top) hs

private theorem theta_value_finite_of_phi_subgradient_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Theta psi gradPsi a b lam Lpsi)
    {x g : H} (hg : g ∈ subdifferential phi x) :
    Theta x ≠ ⊤ ∧ Theta x ≠ ⊥ ∧ ((Theta x).toReal : EReal) = Theta x := by
  have hphi_top : phi x ≠ ⊤ := subgradient_value_ne_top_local hH.phi_proper hg
  have hphi_bot : phi x ≠ ⊥ := hH.phi_proper.1 x
  have htheta_top : Theta x ≠ ⊤ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_top hphi_top (EReal.coe_ne_top _)
  have htheta_bot : Theta x ≠ ⊥ := by
    rw [hH.theta_eq]
    exact EReal.add_ne_bot_iff.mpr ⟨hphi_bot, EReal.coe_ne_bot _⟩
  exact ⟨htheta_top, htheta_bot, EReal.coe_toReal htheta_top htheta_bot⟩

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

private theorem theta_support_of_phi_subgradient_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hΘconvex : Convex ℝ (ERealFunction.epigraph Θ))
    {x g q : H} (hg : g ∈ subdifferential phi x) :
    Θ q ≥ Θ x + (inner ℝ (g + gradPsi x) (q - x) : ℝ) := by
  obtain ⟨hx_top, hx_bot, hx_coe⟩ :=
    theta_value_finite_of_phi_subgradient_local phi Θ psi gradPsi a b lam Lpsi hH hg
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
    change ((1 - t) • x + t • q, (1 - t) * X + t * Q) ∈ ERealFunction.epigraph Θ at hcomb
    rw [hpoint, ERealFunction.mem_epigraph_iff] at hcomb
    have htop : Θ (x + t • d) ≠ ⊤ := by
      intro htop
      rw [htop] at hcomb
      apply EReal.coe_ne_top ((1 - t) * X + t * Q)
      simpa using hcomb
    have hbot : Θ (x + t • d) ≠ ⊥ := by
      rw [hH.theta_eq]
      exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 _, EReal.coe_ne_bot _⟩
    exact EReal.toReal_le_toReal hcomb hbot (EReal.coe_ne_top _)
  have hphi_finite : ∀ z : H, Θ z ≠ ⊤ → Θ z ≠ ⊥ → phi z ≠ ⊤ ∧ phi z ≠ ⊥ := by
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
      have hxepi : (x, X) ∈ ERealFunction.epigraph Θ := by rw [ERealFunction.mem_epigraph_iff, hxE]
      have hqepi : (q, Q) ∈ ERealFunction.epigraph Θ := by rw [ERealFunction.mem_epigraph_iff, hqE]
      have hs0 : 0 ≤ 1 - t := by linarith
      have hs1 : (1 - t) + t = 1 := by ring
      have hseg := hΘconvex hxepi hqepi hs0 ht.le hs1
      change ((1 - t) • x + t • q, (1 - t) * X + t * Q) ∈ ERealFunction.epigraph Θ at hseg
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
      rw [hH.theta_eq, EReal.toReal_add hpx.1 hpx.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    have hzreal : (Θ (x + t • d)).toReal = (phi (x + t • d)).toReal + psi (x + t • d) := by
      rw [hH.theta_eq, EReal.toReal_add hpz.1 hpz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    rw [hzreal]
    dsimp [P]
    simp only [zero_smul, add_zero] at *
    linarith
  have hquot : ∀ t : ℝ, 0 < t → t < 1 → inner ℝ g d + (P t - P 0) / t ≤ Q - X := by
    intro t ht ht1
    have h1 := hlower t ht ht1.le
    have h2 := hchord t ht.le ht1.le
    have htne : t ≠ 0 := ne_of_gt ht
    dsimp [X, Q] at h1 h2 ⊢
    calc
      inner ℝ g d + (P t - P 0) / t = (t * inner ℝ g d + (P t - P 0)) / t := by field_simp [htne]
      _ ≤ t * (Q - X) / t := (div_le_div_iff_of_pos_right ht).mpr (by linarith)
      _ = Q - X := by field_simp [htne]
  have hPderiv : HasDerivAt P (inner ℝ (gradPsi x) d) 0 :=
    hasDerivAt_line_restrict_local psi gradPsi x d hH.psi_differentiable hH.psi_gradient
  have hslope : Filter.Tendsto (fun t : ℝ => (P t - P 0) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (inner ℝ (gradPsi x) d)) := by
    have ht := hPderiv.tendsto_slope_zero_right
    simpa [one_div, div_eq_inv_mul] using ht
  have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), inner ℝ g d + (P t - P 0) / t ≤ Q - X := by
    have hlt : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with t htpos htone
    exact hquot t htpos htone
  have hlim := le_of_tendsto (hslope.const_add (inner ℝ g d)) hevent
  have hreal : inner ℝ (g + gradPsi x) d ≤ Q - X := by simpa [inner_add_left] using hlim
  rw [hxE, hqE]
  norm_cast
  dsimp [d, X, Q] at hreal
  linarith

private theorem sum_Icc_succ_local {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.Icc 2 (k + 1), f i) = (∑ i ∈ Finset.Icc 2 k, f i) + f (k + 1) :=
  Finset.sum_Icc_succ_top (a := 2) (b := k) (by omega) f

private theorem sum_inner_Icc_succ_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ (Finset.Icc 2 (n + 1)).attach, inner ℝ (zSequence u y a b lam i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega)) (velocity u i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega))) =
      (∑ i ∈ (Finset.Icc 2 n).attach, inner ℝ (zSequence u y a b lam i (by
        have hi := (Finset.mem_Icc.mp i.property).1; omega)) (velocity u i (by
        have hi := (Finset.mem_Icc.mp i.property).1; omega))) +
      inner ℝ (zSequence u y a b lam (n + 1) (by omega)) (velocity u (n + 1) (by omega)) := by
  let f : ℕ → ℝ := fun i => if hi : 1 ≤ i then
    inner ℝ (zSequence u y a b lam i hi) (velocity u i hi) else 0
  have hlarge : (∑ i ∈ (Finset.Icc 2 (n + 1)).attach, inner ℝ (zSequence u y a b lam i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega)) (velocity u i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega))) = ∑ i ∈ Finset.Icc 2 (n + 1), f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 (n + 1)).attach, f i := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_one : 1 ≤ (i : ℕ) := by
          have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
          omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  have hsmall : (∑ i ∈ (Finset.Icc 2 n).attach, inner ℝ (zSequence u y a b lam i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega)) (velocity u i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega))) = ∑ i ∈ Finset.Icc 2 n, f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 n).attach, f i := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_one : 1 ≤ (i : ℕ) := by
          have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
          omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  rw [hlarge, hsmall, sum_Icc_succ_local f n hn]
  simp [f]

private theorem sum_norm_sq_Icc_succ_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u : ℕ → H) (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ (Finset.Icc 2 (n + 1)).attach, ‖velocity u i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega)‖ ^ 2) =
      (∑ i ∈ (Finset.Icc 2 n).attach, ‖velocity u i (by
        have hi := (Finset.mem_Icc.mp i.property).1; omega)‖ ^ 2) +
          ‖velocity u (n + 1) (by omega)‖ ^ 2 := by
  let f : ℕ → ℝ := fun i => if hi : 1 ≤ i then ‖velocity u i hi‖ ^ 2 else 0
  have hlarge : (∑ i ∈ (Finset.Icc 2 (n + 1)).attach, ‖velocity u i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega)‖ ^ 2) =
        ∑ i ∈ Finset.Icc 2 (n + 1), f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 (n + 1)).attach, f i := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_one : 1 ≤ (i : ℕ) := by
          have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
          omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  have hsmall : (∑ i ∈ (Finset.Icc 2 n).attach, ‖velocity u i (by
      have hi := (Finset.mem_Icc.mp i.property).1; omega)‖ ^ 2) = ∑ i ∈ Finset.Icc 2 n, f i := by
    calc
      _ = ∑ i ∈ (Finset.Icc 2 n).attach, f i := by
        apply Finset.sum_congr rfl; intro i hi
        have hi_one : 1 ≤ (i : ℕ) := by
          have hi_two : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
          omega
        simp only [f, dif_pos hi_one]
      _ = _ := Finset.sum_attach _ _
  rw [hlarge, hsmall, sum_Icc_succ_local f n hn]
  simp [f]

private theorem auxiliaryG_increment_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) :
    auxiliaryG u y a b lam q (k + 2) (by omega) - auxiliaryG u y a b lam q (k + 1) (by omega) =
      inner ℝ (zSequence u y a b lam (k + 2) (by omega)) (u (k + 2) - q) -
        inner ℝ (zSequence u y a b lam (k + 1) (by omega)) (u (k + 1) - q) -
          inner ℝ (zSequence u y a b lam (k + 2) (by omega)) (velocity u (k + 2) (by omega)) := by
  unfold auxiliaryG
  rw [sum_inner_Icc_succ_local u y a b lam (k + 1) (by omega)]
  ring

private theorem liapunovF_increment_normal_form_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) :
    liapunovF u y a b lam q (k + 1) (by omega) - liapunovF u y a b lam q k hk =
      (a + b) / (2 * lam) * (‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2) +
      (1 / lam + b) * inner ℝ (zSequence u y a b lam (k + 2) (by omega))
        (velocity u (k + 2) (by omega)) -
      ((2 + (b - a) * lam) / (2 * lam ^ 2)) * ‖velocity u (k + 1) (by omega)‖ ^ 2 -
      (1 / lam + b) * (inner ℝ (zSequence u y a b lam (k + 2) (by omega)) (u (k + 2) - q) -
        inner ℝ (zSequence u y a b lam (k + 1) (by omega)) (u (k + 1) - q)) +
      2 * ((1 + b * lam) / (2 * lam ^ 2)) *
        (inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) -
          inner ℝ (velocity u (k + 1) (by omega)) (u k - q)) := by
  dsimp only [liapunovF]
  simp only [Nat.add_assoc]
  norm_num1
  have hG := auxiliaryG_increment_local u y a b lam q k hk
  have hnorm := sum_norm_sq_Icc_succ_local u k hk
  linear_combination -(1 / lam + b) * hG - ((2 + (b - a) * lam) / (2 * lam ^ 2)) * hnorm

private theorem scalar_product_normal_form_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) :
    b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
      (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) =
      (a + b) / (2 * lam) * (‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2) +
      (1 / lam + b) * inner ℝ (zSequence u y a b lam (k + 1) (by omega))
        (velocity u (k + 1) (by omega)) -
      ((2 + (b - a) * lam) / (2 * lam ^ 2)) * ‖velocity u (k + 1) (by omega)‖ ^ 2 -
      (1 / lam + b) * (inner ℝ (a • u (k + 1) - b • y (k + 1)) (u (k + 1) - q) -
        inner ℝ (a • u k - b • y k) (u k - q)) := by
  rw [velocity_eq_sub_of_one_le, zeta_eq_sub_of_one_le]
  simp only [Nat.add_sub_cancel]
  unfold zSequence
  rw [velocity_eq_sub_of_one_le]
  simp only [Nat.add_sub_cancel]
  have hpolar := norm_difference_polarization_local (u k) q (u (k + 1) - u k)
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

/-- Proposition 3 at its native successor index, converted to real values. -/
private theorem liapunov_succ_increment_le_gap_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H) (q : H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y)
    (hqtop : Θ q ≠ ⊤) (hqbot : Θ q ≠ ⊥) (j : ℕ) (hj : 1 ≤ j) :
    liapunovF u y a b lam q (j + 1) (by omega) -
        liapunovF u y a b lam q j hj ≤
      b * ((Θ q).toReal - (Θ (u (j + 1))).toReal) := by
  obtain ⟨hujtop, hujbot⟩ :=
    theta_trajectory_finite phi Θ psi gradPsi a b lam Lpsi u y hH hIFB j
  have hrhs :
      ((b * ((Θ q).toReal - (Θ (u (j + 1))).toReal) : ℝ) : EReal) =
        (b : EReal) * (Θ q - Θ (u (j + 1))) := by
    rw [← EReal.coe_toReal hqtop hqbot,
      ← EReal.coe_toReal hujtop hujbot]
    norm_num
  obtain ⟨g, hg, hvector⟩ := ifb_update_vector_identity_local phi psi gradPsi u y a b lam hIFB j
  have hsupp := theta_support_of_phi_subgradient_local phi Θ psi gradPsi a b lam Lpsi hH
    hH.theta_convex (q := q) hg
  rw [hvector] at hsupp
  have hsupp' : Θ q ≥ Θ (u (j + 1)) +
      (inner ℝ ((1 / lam - a) • velocity u (j + 1) (by omega) +
        (1 / lam + b) • zeta y (j + 1) (by omega)) (u (j + 1) - q) : ℝ) := by
    have hinner : inner ℝ (-((1 / lam - a) • velocity u (j + 1) (by omega) +
        (1 / lam + b) • zeta y (j + 1) (by omega))) (q - u (j + 1)) =
        inner ℝ ((1 / lam - a) • velocity u (j + 1) (by omega) +
          (1 / lam + b) • zeta y (j + 1) (by omega)) (u (j + 1) - q) := by
      rw [inner_neg_left]
      have hsub : q - u (j + 1) = -(u (j + 1) - q) := by abel
      rw [hsub, inner_neg_right]
      ring
    rw [hinner] at hsupp
    exact hsupp
  have hreal : inner ℝ ((1 / lam - a) • velocity u (j + 1) (by omega) +
      (1 / lam + b) • zeta y (j + 1) (by omega)) (u (j + 1) - q) ≤
      (Θ q).toReal - (Θ (u (j + 1))).toReal := by
    rw [← EReal.coe_toReal hujtop hujbot, ← EReal.coe_toReal hqtop hqbot] at hsupp'
    linarith [EReal.coe_le_coe_iff.mp hsupp']
  have hmul := mul_le_mul_of_nonneg_left hreal hIFB.b_pos.le
  have hpScalar :
      ((b * inner ℝ ((1 / lam - a) • velocity u (j + 1) (by omega) +
        (1 / lam + b) • zeta y (j + 1) (by omega)) (u (j + 1) - q) : ℝ) : EReal) ≤
        (b : EReal) * (Θ q - Θ (u (j + 1))) := by
    rw [← EReal.coe_toReal hujtop hujbot, ← EReal.coe_toReal hqtop hqbot]
    exact_mod_cast hmul
  have hscalar :
      b * inner ℝ ((1 / lam - a) • velocity u (j + 1) (by omega) +
        (1 / lam + b) • zeta y (j + 1) (by omega)) (u (j + 1) - q) ≤
        b * ((Θ q).toReal - (Θ (u (j + 1))).toReal) := by
    apply EReal.coe_le_coe_iff.mp
    rw [hrhs]
    exact hpScalar
  have hpId : b * inner ℝ ((1 / lam - a) • velocity u (j + 1) (by omega) +
      (1 / lam + b) • zeta y (j + 1) (by omega)) (u (j + 1) - q) =
      liapunovF u y a b lam q (j + 1) (by omega) - liapunovF u y a b lam q j hj := by
    have hscalar := scalar_product_normal_form_local u y a b lam q j hj
    have hF := liapunovF_increment_normal_form_local u y a b lam q j hj
    rw [hscalar, hF]
    have hv1 : velocity u (j + 1) (by omega) = u (j + 1) - u j := by
      rw [velocity_eq_sub_of_one_le]
      simp only [Nat.add_sub_cancel]
    have hnat : j + 2 - 1 = j + 1 := by omega
    have hv2 : velocity u (j + 2) (by omega) = u (j + 2) - u (j + 1) := by
      rw [velocity_eq_sub_of_one_le]
      rw [hnat]
    rw [hv1, hv2]
    unfold zSequence
    rw [hv1, hv2]
    rw [hnat]
    simp only [Nat.add_sub_cancel]
    rw [← real_inner_self_eq_norm_sq (u (j + 1) - u j)]
    simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [real_inner_comm (u (j + 1)) (u j)]
    by_cases hlam : lam = 0
    · subst lam
      norm_num
      ring
    · field_simp [hlam]
      ring
  have htotal : liapunovF u y a b lam q (j + 1) (by omega) - liapunovF u y a b lam q j hj ≤
      b * ((Θ q).toReal - (Θ (u (j + 1))).toReal) := hpId.symm.le.trans hscalar
  exact htotal

/-- Proposition 6: the objective approaches its infimum and weak cluster points are minimizers. -/
theorem proposition6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) :
    Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds (sInf (Set.range Θ))) ∧
    (∀ q, IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) →
      q ∈ Optimization.argminSet Θ) ∧
    (Optimization.argminSet Θ = ∅ → Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop Filter.atTop) := by
  rcases proposition2 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨henergy_mono, hsq, e, henergy_tail, hTheta_tail⟩
  have hTheta : Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds e) :=
    tendsto_of_tendsto_nat_succ hTheta_tail
  have hobjective : Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop
      (nhds (sInf (Set.range Θ))) := by
    let E : ℕ → EReal := fun k ↦
      mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega)
    have hE : Filter.Tendsto E Filter.atTop (nhds e) := by
      simpa [E] using henergy_tail
    have hE_mono : ∀ k, E (k + 1) ≤ E k := by
      intro k
      simpa [E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using henergy_mono k
    have hE_lower : ∀ k, e ≤ E k := energy_limit_le_local E e hE_mono hE
    have hvelocity_error : Summable (fun k : ℕ ↦
        (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2) := by
      simpa using Summable.mul_left (b * gamma a b lam) hsq
    obtain ⟨m, hm⟩ := hH.theta_bounded_below
    have hrange_bdd : BddBelow (Set.range Θ) := by
      refine ⟨(m : EReal), ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hm x
    have heq : e = sInf (Set.range Θ) := by
      apply le_antisymm
      · apply le_csInf
        · exact Set.range_nonempty Θ
        · intro z hz
          rcases hz with ⟨q, rfl⟩
          by_cases hqtop : Θ q = ⊤
          · rw [hqtop]
            exact le_top
          have hqbot : Θ q ≠ ⊥ := theta_ne_bot phi Θ psi gradPsi a b lam Lpsi hH q
          have hqphi : q ∈ ERealFunction.dom phi := by
            apply (ERealFunction.mem_dom_iff phi q).mpr
            apply (lt_top_iff_ne_top).2
            intro hphitop
            apply hqtop
            rw [hH.theta_eq, hphitop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
          obtain ⟨C, hC⟩ := liapunov_distance_increment_le phi Θ psi gradPsi a b lam Lpsi
            u y hH hIFB q hqphi
          have hm_e : (m : EReal) ≤ e := by
            apply ge_of_tendsto hTheta
            filter_upwards [] with k
            exact hm (u k)
          have hE0 : e ≤ E 0 := hE_lower 0
          have hE0top : E 0 ≠ ⊤ := by
            dsimp [E, mechanicalEnergy]
            exact EReal.add_ne_top (theta_trajectory_finite phi Θ psi gradPsi a b lam Lpsi
              u y hH hIFB 0).1 (EReal.coe_ne_top _)
          have hetop : e ≠ ⊤ := ne_top_of_le_ne_top hE0top hE0
          have hebot : e ≠ ⊥ := by
            intro he
            have : (m : EReal) = ⊥ := le_bot_iff.mp (he ▸ hm_e)
            exact EReal.coe_ne_bot m this
          have hecoe : ((e.toReal : ℝ) : EReal) = e := EReal.coe_toReal hetop hebot
          let α : ℝ := (1 + b * lam) / (2 * lam ^ 2)
          let aF : ℕ → ℝ := fun k ↦
            liapunovF u y a b lam q (k + 1) (by omega) - C
          let bDist : ℕ → ℝ := fun k ↦ α * ‖u (k + 1) - q‖ ^ 2
          let eps : ℕ → ℝ := fun k ↦
            (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2
          let theta : ℝ := b * ((Θ q).toReal - e.toReal)
          have heps : Summable eps := by
            simpa [eps] using hvelocity_error
          have hinc (k : ℕ) (hk : 1 ≤ k) :
              aF k - aF (k - 1) ≤ theta + eps k := by
            dsimp [aF, eps, theta]
            have hF := liapunov_succ_increment_le_gap_local phi Θ psi gradPsi a b lam Lpsi
              u y q hH hIFB hqtop hqbot k hk
            have hEk := hE_lower k
            dsimp [E, mechanicalEnergy] at hEk
            obtain ⟨hukt, hukb⟩ :=
              theta_trajectory_finite phi Θ psi gradPsi a b lam Lpsi u y hH hIFB k
            have hEkreal : e.toReal ≤ (Θ (u (k + 1))).toReal +
                gamma a b lam * ‖u (k + 1) - u k‖ ^ 2 := by
              rw [← EReal.coe_toReal hetop hebot,
                ← EReal.coe_toReal hukt hukb] at hEk
              norm_num at hEk
              rw [velocity_eq_sub_of_one_le] at hEk
              simpa only [Nat.add_sub_cancel] using (EReal.coe_le_coe_iff.mp hEk)
            have hgap : b * ((Θ q).toReal - (Θ (u (k + 1))).toReal) ≤
                b * ((Θ q).toReal - e.toReal) +
                  (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_left hEkreal hH.b_pos.le]
            have hFk : liapunovF u y a b lam q (k + 1) (by omega) -
                liapunovF u y a b lam q k (by omega) ≤
                b * ((Θ q).toReal - e.toReal) +
                  (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2 :=
              hF.trans hgap
            simpa [Nat.sub_add_cancel hk] using hFk
          have hdist (k : ℕ) (hk : 1 ≤ k) :
              bDist (k + 1) - bDist k ≤ aF k := by
            dsimp [bDist, aF, α]
            simpa [Nat.add_assoc] using hC (k + 1) (by omega)
          have hα : 0 < α := by
            dsimp [α]
            apply div_pos <;> nlinarith [hH.b_pos, hH.step_pos]
          have hnonneg (k : ℕ) (_ : 1 ≤ k) : 0 ≤ bDist k := by
            exact mul_nonneg hα.le (sq_nonneg _)
          have htheta : 0 ≤ theta :=
            lemma5 aF bDist eps theta 1 (by omega) heps.norm hinc hdist hnonneg
          have hreal : e.toReal ≤ (Θ q).toReal := by
            dsimp [theta] at htheta
            nlinarith [hH.b_pos]
          rw [← hecoe, ← EReal.coe_toReal hqtop hqbot]
          exact_mod_cast hreal
      · apply ge_of_tendsto hTheta
        filter_upwards [] with k
        exact csInf_le hrange_bdd ⟨u k, rfl⟩
    simpa [heq] using hTheta
  have hcluster : ∀ q, IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k))
      (toWeakSpace ℝ H q) → q ∈ Optimization.argminSet Θ := by
    intro q hq
    obtain ⟨σ, hσ, hσweak⟩ := hq.exists_subseq_tendsto
    have hsubTheta : Filter.Tendsto (fun n ↦ Θ (u (σ n))) Filter.atTop
        (nhds (sInf (Set.range Θ))) := by
      simpa [Function.comp_def] using hobjective.comp hσ.tendsto_atTop
    have hqle : Θ q ≤ sInf (Set.range Θ) := by
      by_contra hnot
      have hlt : sInf (Set.range Θ) < Θ q := lt_of_not_ge hnot
      obtain ⟨r, hrleft, hrright⟩ := EReal.exists_between_coe_real hlt
      have hevent : ∀ᶠ n in Filter.atTop, Θ (u (σ n)) < (r : EReal) :=
        hsubTheta.eventually (Iio_mem_nhds hrleft)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
      have hclosed : IsClosed (ERealFunction.lowerLevelSet Θ r) :=
        (ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet Θ).mp
          (theta_lowerSemicontinuous phi Θ psi gradPsi a b lam Lpsi hH) r
      have hconvex : Convex ℝ (ERealFunction.lowerLevelSet Θ r) :=
        convex_lowerLevelSet_theta Θ r hH.theta_convex
      have hmem : ∀ n, u (σ (n + N)) ∈ ERealFunction.lowerLevelSet Θ r := by
        intro n
        exact le_of_lt (hN _ (Nat.le_add_left N n))
      have hweakshift : Filter.Tendsto
          (fun n ↦ toWeakSpace ℝ H (u (σ (n + N)))) Filter.atTop
          (nhds (toWeakSpace ℝ H q)) := by
        simpa [Function.comp_def] using hσweak.comp (Filter.tendsto_add_atTop_nat N)
      have hqr : q ∈ ERealFunction.lowerLevelSet Θ r :=
        mem_of_tendsto_weakly_of_isClosed_convex hclosed hconvex hmem hweakshift
      exact (not_le_of_gt hrright) hqr
    rw [Optimization.mem_argminSet_iff_eq_sInf]
    exact le_antisymm hqle (csInf_le' ⟨q, rfl⟩)
  refine ⟨hobjective, hcluster, ?_⟩
  intro hempty
  apply tendsto_norm_atTop_of_no_weak_cluster u
  intro q hq
  have hqmin := hcluster q hq
  rw [hempty] at hqmin
  simp at hqmin

end AttouchPeypouquetRedont2014
