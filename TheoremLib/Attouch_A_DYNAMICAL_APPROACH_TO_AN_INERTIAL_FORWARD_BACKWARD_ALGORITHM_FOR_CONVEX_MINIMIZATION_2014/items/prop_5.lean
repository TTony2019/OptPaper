import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_8
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.lem_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_1

namespace AttouchPeypouquetRedont2014

/-- A minimizer of `Θ = φ + ψ` lies in the effective domain of the proper part `φ`. -/
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
-- The Liapunov estimate needs extra heartbeats.
/-- Proposition 8: a nonempty solution set yields bounded IFB iterates and convergent `F_k(q)`. -/
theorem proposition8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (u y : ℕ → H) (a b lam Lpsi : ℝ)
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
      have hmono := (proposition3 phi Θ psi gradPsi u y a b lam Lpsi q (n + 1)
        hH hIFB (by omega) hH.theta_convex).2.2 hq
      exact liapunovF_le_proof_irrel u y a b lam q (n + 1 + 1) (n + 1)
        (hk := by omega) (hk' := by omega) (hl := by omega) (hl' := by omega) hmono
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
    have hmono := (proposition3 phi Θ psi gradPsi u y a b lam Lpsi q (n + 1)
      hH hIFB (by omega) hH.theta_convex).2.2 hq
    exact liapunovF_le_proof_irrel u y a b lam q (n + 1 + 1) (n + 1)
      (hk := by omega) (hk' := by omega) (hl := by omega) (hl' := by omega) hmono
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

end AttouchPeypouquetRedont2014
