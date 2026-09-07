import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_1
namespace Alvarez2002
open Filter
/-- Coercivity bounds every `(DIN)` trajectory, hence yields Theorem 2.1(iii). -/
theorem coercive_potential_bounds_din {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (gradΦ : H → H) (hessΦ : H → H →L[ℝ] H) (α β : ℝ)
    (x v acc : ℝ → H) (hΦ : AssumptionH H Φ)
    (hhessΦ : ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ p q,
      ‖p‖ ≤ R → ‖q‖ ≤ R → ‖hessΦ p - hessΦ q‖ ≤ L * ‖p - q‖)
    (hgrad : ∀ x u, HasDerivAt (fun s : ℝ => Φ (x + s • u))
      (inner ℝ (gradΦ x) u) 0)
    (hcoercive : ∀ r : ℝ, ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → r ≤ Φ z)
    (hsol : IsDINTrajectory H Φ α β x)
    (henergy : ∀ t,
      (α * β + 1) * Φ (x t) + (1 / 2) * ‖v t + β • gradΦ (x t)‖ ^ 2 ≤
        (α * β + 1) * Φ (x 0) + (1 / 2) * ‖v 0 + β • gradΦ (x 0)‖ ^ 2) :
    (∃ R : ℝ, ∀ t, ‖x t‖ ≤ R) ∧
      Bornology.IsBounded (Set.range v) ∧ Bornology.IsBounded (Set.range acc) ∧
      Bornology.IsBounded (Set.range (fun t => gradΦ (x t))) ∧
      Bornology.IsBounded (Set.range (fun t => hessΦ (x t))) ∧
      Tendsto v atTop (nhds 0) ∧ Tendsto acc atTop (nhds 0) ∧
      Tendsto (fun t => gradΦ (x t)) atTop (nhds 0) := by
  sorry
/-
  rcases hsol with ⟨hα, hβ, hxderiv, hvderiv, heq⟩
  have hab : 0 < α * β := mul_pos hα hβ
  have hs : 0 < α * β + 1 := by linarith
  let s : ℝ := α * β + 1
  let E0 : ℝ :=
    s * Φ (x 0) + (1 / 2) * ‖v 0 + β • gradΦ (x 0)‖ ^ 2
  have hs' : 0 < s := by simpa [s] using hs
  have hPhiSub : ∀ t, Φ (x t) ≤ E0 / s := by
    intro t
    have hsq : 0 ≤ (1 / 2 : ℝ) * ‖v t + β • gradΦ (x t)‖ ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hscaled : s * Φ (x t) ≤ E0 := by
      dsimp [s, E0]
      linarith [henergy t]
    exact (le_div_iff₀ hs').2 (by simpa [mul_comm] using hscaled)
  obtain ⟨R, hR⟩ := hcoercive (E0 / s + 1)
  have hRnorm : ∀ t, ‖x t‖ ≤ R := by
    intro t
    by_contra hnot
    have hRle : R ≤ ‖x t‖ := le_of_not_ge hnot
    have hlarge : E0 / s + 1 ≤ Φ (x t) := hR (x t) hRle
    linarith [hPhiSub t]
  have hxbdd : ∃ R : ℝ, ∀ t, ‖x t‖ ≤ R := ⟨R, hRnorm⟩
  have hxbddSet : Bornology.IsBounded (Set.range x) := by
    refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
    rintro z ⟨t, rfl⟩
    exact hRnorm t
  obtain ⟨y, w, a, hy0, hw0, htrajY, hunique, henergyY, hmemlpv, hmemlpgrad,
    hphiLim, hcomboLim, hpartIII⟩ :=
    din_forward_internal Φ hΦ α β hα hβ (x 0) (v 0)
  have hxConOn : ContinuousOn x (Set.Ici 0) :=
    (continuous_iff_continuousAt.mpr fun t => (hxderiv t).continuousAt).continuousOn
  have hvConOn : ContinuousOn v (Set.Ici 0) :=
    (continuous_iff_continuousAt.mpr fun t => (hvderiv t).continuousAt).continuousOn
  have hhessCont : Continuous hessΦ := by
    have hlocal : LocallyLipschitz hessΦ := by
      intro z
      let R : ℝ := ‖z‖ + 1
      have hR : 0 < R := by
        dsimp [R]
        linarith [norm_nonneg z]
      obtain ⟨L, hLpos, hL'⟩ := hhessΦ R hR
      let K : NNReal := ⟨L, hLpos.le⟩
      refine ⟨K, Metric.closedBall z 1, Metric.closedBall_mem_nhds z zero_lt_one,
        LipschitzOnWith.of_dist_le_mul ?_⟩
      intro p hp q hq
      have hpR : ‖p‖ ≤ R := by
        calc
          ‖p‖ ≤ ‖p - z‖ + ‖z‖ := by
            calc
              ‖p‖ = ‖(p - z) + z‖ := by congr 1; module
              _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 1 + ‖z‖ := by
            gcongr
            simpa [Metric.mem_closedBall, dist_eq_norm] using hp
          _ = R := by dsimp [R]; ring
      have hqR : ‖q‖ ≤ R := by
        calc
          ‖q‖ ≤ ‖q - z‖ + ‖z‖ := by
            calc
              ‖q‖ = ‖(q - z) + z‖ := by congr 1; module
              _ ≤ ‖q - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 1 + ‖z‖ := by
            gcongr
            simpa [Metric.mem_closedBall, dist_eq_norm] using hq
          _ = R := by dsimp [R]; ring
      simpa [K, dist_eq_norm] using hL' p q hpR hqR
    exact hlocal.continuous
  have haccCont : Continuous acc := by
    have heq' : acc = fun t => -(α • v t + β • hessΦ (x t) (v t) + gradΦ (x t)) := by
      funext t
      exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using heq t)
    rw [heq']
    have hxCont : Continuous x :=
      continuous_iff_continuousAt.mpr fun t => (hxderiv t).continuousAt
    have hvCont : Continuous v :=
      continuous_iff_continuousAt.mpr fun t => (hvderiv t).continuousAt
    have hgradCont : Continuous gradΦ :=
      continuous_iff_continuousAt.mpr fun z =>
        (hΦ.hessian_is_derivative z).continuousAt
    fun_prop
  have hxC2 : ContDiffOn ℝ 2 x (Set.Ioi 0) := by
    have hderivx : deriv x = v := by
      funext t
      exact (hxderiv t).deriv
    have hderivv : deriv v = acc := by
      funext t
      exact (hvderiv t).deriv
    change ContDiffOn ℝ (1 + 1) x (Set.Ioi 0)
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht => (hxderiv t).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h
      norm_num at h
    · rw [hderivx]
      change ContDiffOn ℝ (0 + 1) v (Set.Ioi 0)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun t ht => (hvderiv t).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro h
        norm_num at h
      · rw [hderivv]
        exact (contDiff_zero.mpr haccCont).contDiffOn
  have hgeq : ∀ t, 0 ≤ t → x t = y t ∧ v t = w t :=
    hunique x v acc rfl rfl ⟨hα, hβ, hxConOn, hvConOn, hxC2,
      fun t _ => hxderiv t, fun t _ => hvderiv t, fun t _ => heq t⟩
  have hacc_geq : ∀ t, 0 < t → acc t = a t := by
    intro t ht
    have hwa : HasDerivAt w (a t) t := htrajY.2.2.2.2.2.2.1 t ht
    have hvw_near : v =ᶠ[nhds t] w := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact (hgeq s hs.le).2
    have hva : HasDerivAt v (a t) t := hwa.congr_of_eventuallyEq hvw_near
    exact (hvderiv t).unique hva
  have hyIci : Bornology.IsBounded (y '' Set.Ici (0 : ℝ)) := by
    apply hxbddSet.subset
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, (hgeq t ht).1⟩
  rcases hpartIII hyIci with ⟨hwIci, haIci, hgIci, hhessIci, hwZero, haZero, hgZero⟩
  have hvZero : Tendsto v atTop (nhds 0) := by
    apply hwZero.congr'
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hgeq t ht).2.symm
  have haZero_x : Tendsto acc atTop (nhds 0) := by
    apply haZero.congr'
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (hacc_geq t (by linarith)).symm
  have hgZero_x : Tendsto (fun t => gradΦ (x t)) atTop (nhds 0) := by
    apply hgZero.congr'
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [(hgeq t ht).1]
  let R' : ℝ := max R 1 + 1
  have hR' : 0 < R' := by
    dsimp [R']
    linarith [le_max_right R 1]
  obtain ⟨L, hLpos, hL⟩ := hhessΦ R' hR'
  let M : ℝ := L * R' + ‖hessΦ 0‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (mul_nonneg hLpos.le hR'.le) (norm_nonneg _)
  have hxtR' : ∀ t, ‖x t‖ ≤ R' := by
    intro t
    calc
      ‖x t‖ ≤ R := hRnorm t
      _ ≤ R' := by
        dsimp [R']
        linarith [le_max_left R 1]
  have hhessbdd : Bornology.IsBounded (Set.range (fun t => hessΦ (x t))) := by
    refine isBounded_iff_forall_norm_le.2 ⟨M, ?_⟩
    rintro q ⟨t, rfl⟩
    have hzero : ‖(0 : H)‖ ≤ R' := by simpa using hR'.le
    have hd := hL (x t) 0 (hxtR' t) hzero
    calc
      ‖hessΦ (x t)‖ = ‖hessΦ (x t) - hessΦ 0 + hessΦ 0‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖hessΦ (x t) - hessΦ 0‖ + ‖hessΦ 0‖ := norm_add_le _ _
      _ ≤ L * ‖x t - 0‖ + ‖hessΦ 0‖ := by gcongr
      _ ≤ L * R' + ‖hessΦ 0‖ := by
        gcongr
        simpa using hxtR' t
      _ = M := rfl
  have hgradLip : ∀ p q, ‖p‖ ≤ R' → ‖q‖ ≤ R' →
      ‖gradΦ p - gradΦ q‖ ≤ M * ‖p - q‖ := by
    intro p q hp hq
    have hbound : ∀ z ∈ Metric.closedBall (0 : H) R', ‖hessΦ z‖ ≤ M := by
      intro z hz
      have hz' : ‖z‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have hzero : ‖(0 : H)‖ ≤ R' := by simpa using hR'.le
      have hd := hL z 0 hz' hzero
      calc
        ‖hessΦ z‖ = ‖hessΦ z - hessΦ 0 + hessΦ 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖hessΦ z - hessΦ 0‖ + ‖hessΦ 0‖ := norm_add_le _ _
        _ ≤ L * ‖z - 0‖ + ‖hessΦ 0‖ := by gcongr
        _ ≤ L * R' + ‖hessΦ 0‖ := by
          gcongr
          simpa using hz'
        _ = M := rfl
    have hderiv : ∀ z ∈ Metric.closedBall (0 : H) R', DifferentiableAt ℝ gradΦ z :=
      fun z _ => (hΦ.hessian_is_derivative z).differentiableAt
    have hfd : ∀ z ∈ Metric.closedBall (0 : H) R', ‖fderiv ℝ gradΦ z‖ ≤ M := by
      intro z hz
      simpa [(hΦ.hessian_is_derivative z).fderiv] using hbound z hz
    have hconv : Convex ℝ (Metric.closedBall (0 : H) R') := convex_closedBall _ _
    have hpball : p ∈ Metric.closedBall (0 : H) R' := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hp
    have hqball : q ∈ Metric.closedBall (0 : H) R' := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hq
    simpa [dist_eq_norm] using
      hconv.norm_image_sub_le_of_norm_fderiv_le hderiv hfd hqball hpball
  let G : ℝ := M * R' + ‖gradΦ 0‖
  have hgradbdd : Bornology.IsBounded (Set.range (fun t => gradΦ (x t))) := by
    refine isBounded_iff_forall_norm_le.2 ⟨G, ?_⟩
    rintro q ⟨t, rfl⟩
    have hzero : ‖(0 : H)‖ ≤ R' := by simpa using hR'.le
    have hd := hgradLip (x t) 0 (hxtR' t) hzero
    calc
      ‖gradΦ (x t)‖ = ‖gradΦ (x t) - gradΦ 0 + gradΦ 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖gradΦ (x t) - gradΦ 0‖ + ‖gradΦ 0‖ := norm_add_le _ _
      _ ≤ M * ‖x t - 0‖ + ‖gradΦ 0‖ := by gcongr
      _ ≤ M * R' + ‖gradΦ 0‖ := by
        gcongr
        simpa using hxtR' t
      _ = G := rfl
  obtain ⟨m, hm⟩ := hΦ.bounded_below
  let B : ℝ := E0 - s * m
  have hB : 0 ≤ B := by
    dsimp [B, E0]
    have hm0 := hm (x 0)
    nlinarith [hs'.le, sq_nonneg ‖v 0 + β • gradΦ (x 0)‖]
  have hcombo : ∀ t, ‖v t + β • gradΦ (x t)‖ ≤ B + 1 := by
    intro t
    have hsq : (1 / 2 : ℝ) * ‖v t + β • gradΦ (x t)‖ ^ 2 ≤ B := by
      have henergy' : s * Φ (x t) + (1 / 2) * ‖v t + β • gradΦ (x t)‖ ^ 2 ≤ E0 := by
        dsimp [s, E0]
        exact henergy t
      have hmt := hm (x t)
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_left hmt hs'.le]
    have hn := norm_nonneg (v t + β • gradΦ (x t))
    nlinarith
  have hvbdd : Bornology.IsBounded (Set.range v) := by
    rcases isBounded_iff_forall_norm_le.mp hgradbdd with ⟨G, hG⟩
    refine isBounded_iff_forall_norm_le.2 ⟨B + 1 + |β| * G, ?_⟩
    rintro q ⟨t, rfl⟩
    calc
      ‖v t‖ = ‖(v t + β • gradΦ (x t)) - β • gradΦ (x t)‖ := by
        rw [add_sub_cancel_right]
      _ ≤ ‖v t + β • gradΦ (x t)‖ + ‖β • gradΦ (x t)‖ := norm_sub_le _ _
      _ ≤ B + 1 + |β| * G := by
        rw [norm_smul]
        exact add_le_add (hcombo t)
          (mul_le_mul_of_nonneg_left (hG _ ⟨t, rfl⟩) (abs_nonneg β))
  have haccbdd : Bornology.IsBounded (Set.range acc) := by
    rcases isBounded_iff_forall_norm_le.mp hvbdd with ⟨V, hV⟩
    rcases isBounded_iff_forall_norm_le.mp hgradbdd with ⟨G, hG⟩
    rcases isBounded_iff_forall_norm_le.mp hhessbdd with ⟨Q, hQ⟩
    have hQnonneg : 0 ≤ Q := le_trans (norm_nonneg _) (hQ _ ⟨0, rfl⟩)
    refine isBounded_iff_forall_norm_le.2 ⟨|α| * V + |β| * Q * V + G, ?_⟩
    rintro q ⟨t, rfl⟩
    have hv := hV _ ⟨t, rfl⟩
    have hg := hG _ ⟨t, rfl⟩
    have hq := hQ _ ⟨t, rfl⟩
    have heqt := heq t
    have hacc : acc t = -(α • v t + β • hessΦ (x t) (v t) + gradΦ (x t)) := by
      exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using heqt)
    rw [hacc]
    calc
      ‖-(α • v t + β • hessΦ (x t) (v t) + gradΦ (x t))‖ ≤
          ‖α • v t‖ + ‖β • hessΦ (x t) (v t)‖ + ‖gradΦ (x t)‖ := by
        rw [norm_neg]
        calc
          _ ≤ ‖α • v t + β • hessΦ (x t) (v t)‖ + ‖gradΦ (x t)‖ := norm_add_le _ _
          _ ≤ ‖α • v t‖ + ‖β • hessΦ (x t) (v t)‖ + ‖gradΦ (x t)‖ := by
            gcongr
            exact norm_add_le _ _
      _ ≤ |α| * V + |β| * Q * V + G := by
        rw [norm_smul, norm_smul]
        calc
          |α| * ‖v t‖ + |β| * ‖hessΦ (x t) (v t)‖ + ‖gradΦ (x t)‖ ≤
              |α| * V + |β| * (Q * V) + G := by
            gcongr
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hq hv (norm_nonneg _) hQnonneg)
          _ = |α| * V + |β| * Q * V + G := by ring
  refine ⟨hxbdd, ?_, ?_, ?_, ?_, hvZero, haZero_x, hgZero_x⟩
  · exact hvbdd
  · exact haccbdd
  · exact hgradbdd
  · exact hhessbdd
 -/
end Alvarez2002
