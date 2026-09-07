import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_10
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_4
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_1

namespace AttouchPeypouquetRedont2014

/-- Corollary 11: weak convergence plus bounded inf-compactness upgrades to strong convergence. -/
theorem corollary11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (u y : ℕ → H) (q : H) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hcompact : IsBoundedlyInfCompact Θ)
    (hweak : Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
      (nhds (toWeakSpace ℝ H q))) :
      Filter.Tendsto u Filter.atTop (nhds q) ∧ q ∈ Optimization.argminSet Θ := by
  rcases proposition6 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨hTheta, hclusterMin, _⟩
  have hqcluster : IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k))
      (toWeakSpace ℝ H q) :=
    ⟨id, strictMono_id, by simpa [Function.comp_def] using hweak⟩
  have hqmin : q ∈ Optimization.argminSet Θ := hclusterMin q hqcluster
  rcases (bounded_range_of_tendsto_weakly hweak).exists_pos_norm_le with ⟨R, hRpos, hR⟩
  have hLbot : sInf (Set.range Θ) ≠ (⊥ : EReal) := by
    rcases hH.theta_bounded_below with ⟨m, hm⟩
    have hml : (m : EReal) ≤ sInf (Set.range Θ) := by
      apply le_sInf
      rintro z ⟨x, rfl⟩
      exact hm x
    intro hbot
    rw [hbot] at hml
    exact (not_le_of_gt (EReal.bot_lt_coe m)) hml
  have hTheta_q_top : Θ q ≠ (⊤ : EReal) := by
    rcases hH.phi_proper.2 with ⟨x, hx⟩
    have hqx : Θ q ≤ Θ x := by
      rw [Optimization.mem_argminSet_iff_eq_sInf] at hqmin
      rw [hqmin]
      exact sInf_le (Set.mem_range_self x)
    have hxtop : Θ x < (⊤ : EReal) := by
      rw [hH.theta_eq]
      exact EReal.add_lt_top (lt_top_iff_ne_top.mp hx) (EReal.coe_ne_top _)
    exact ne_of_lt (lt_of_le_of_lt hqx hxtop)
  have hLtop : sInf (Set.range Θ) ≠ (⊤ : EReal) := by
    intro htop
    have hle : (⊤ : EReal) ≤ Θ q := by
      rw [← htop]
      exact sInf_le (Set.mem_range_self q)
    exact hTheta_q_top (top_unique hle)
  let r : ℝ := (sInf (Set.range Θ)).toReal + 1
  have hLr : sInf (Set.range Θ) < (r : EReal) := by
    rw [← EReal.coe_toReal hLtop hLbot]
    exact_mod_cast lt_add_one (sInf (Set.range Θ)).toReal
  have hevent : ∀ᶠ k in Filter.atTop, Θ (u k) < (r : EReal) :=
    hTheta.eventually_lt_const hLr
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  let A : Set H := {v | Θ v ≤ (r : EReal) ∧ ‖v‖ ≤ R}
  let K : Set H := closure A
  have hKcompact : IsCompact K := by
    dsimp [K, A]
    exact hcompact r R hRpos
  have hvK : ∀ n : ℕ, u (N + n) ∈ K := by
    intro n
    apply subset_closure
    constructor
    · exact le_of_lt (hN (N + n) (Nat.le_add_right N n))
    · exact hR (u (N + n)) (Set.mem_range_self _)
  have hunique : ∀ p : H, IsSequentialClusterPt (fun n ↦ u (N + n)) p → p = q := by
    intro p hp
    rcases hp.exists_subseq_tendsto with ⟨f, hf, hfp⟩
    have hindex : Filter.Tendsto (fun n ↦ N + f n) Filter.atTop Filter.atTop := by
      simpa [Nat.add_comm] using (Filter.tendsto_add_atTop_nat N).comp hf.tendsto_atTop
    have hweakq : Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (u (N + f n)))
        Filter.atTop (nhds (toWeakSpace ℝ H q)) := hweak.comp hindex
    have hweakp : Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (u (N + f n)))
        Filter.atTop (nhds (toWeakSpace ℝ H p)) := by
      simpa [Function.comp_def, toWeakSpaceCLM_eq_toWeakSpace] using
        (toWeakSpaceCLM ℝ H).continuous.tendsto p |>.comp hfp
    apply (toWeakSpace ℝ H).injective
    exact tendsto_nhds_unique hweakp hweakq
  have htail : Filter.Tendsto (fun n ↦ u (N + n)) Filter.atTop (nhds q) :=
    tendsto_of_unique_sequential_cluster_point hKcompact.isSeqCompact hvK hunique
  have hstrong : Filter.Tendsto u Filter.atTop (nhds q) := by
    apply (Filter.tendsto_add_atTop_iff_nat N).mp
    simpa [Nat.add_comm] using htail
  exact ⟨hstrong, hqmin⟩

end AttouchPeypouquetRedont2014
