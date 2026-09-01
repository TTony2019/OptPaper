import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_2

namespace AttouchAdlyDryFrictionDynamics2023

/-- Predicate expressing the first-order system (4.14) on the positive time half-line.
    The subgradient is recorded by its defining inequality, avoiding unnecessary
    global convexity/domain side conditions. -/
def IsDryStarFirstOrder {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r α s₀ : ℝ) (_hr : 0 < r) (fgrad : H → H) (x y dx dy : ℝ → H) : Prop :=
  ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s ∧ HasDerivAt y (dy s) s ∧
    ∃ u : H,
      (∀ q : H,
        (dryFrictionPotential (H := H) r (dy s) : EReal) +
            (inner ℝ u (q - dy s) : EReal) ≤
          (dryFrictionPotential (H := H) r q : EReal)) ∧
      dy s + (s / (α - 1)) • u + (s / (α - 1)) • fgrad (y s) = 0 ∧
        dx s + ((α - 1) / s) • (x s - y s) = 0

def IsDryStarTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r α s₀ : ℝ) (fgrad : H → H) (x dx ddx p : ℝ → H) : Prop :=
  ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s ∧ HasDerivAt dx (ddx s) s ∧
    p s ∈ frictionBallProjector r (fgrad (x s + (s / (α - 1)) • dx s)) ∧
      ddx s + (α / s) • dx s + fgrad (x s + (s / (α - 1)) • dx s) - p s = 0

private theorem dryFriction_subgradient_smul_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r c : ℝ} {v u : H} (hc : 0 < c)
    (hu : ∀ q : H, r * ‖v‖ + inner ℝ u (q - v) ≤ r * ‖q‖) :
    ∀ q : H, r * ‖c • v‖ + inner ℝ u (q - c • v) ≤ r * ‖q‖ := by
  intro q
  have hbase := hu (c⁻¹ • q)
  have hcne : c ≠ 0 := ne_of_gt hc
  have hnormq : ‖q‖ = c * ‖c⁻¹ • q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    field_simp [hcne]
  have hnormv : ‖c • v‖ = c * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hinner : inner ℝ u (q - c • v) = c * inner ℝ u (c⁻¹ • q - v) := by
    have hq : q - c • v = c • (c⁻¹ • q - v) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    rw [hq, real_inner_smul_right]
  rw [hnormv, hinner, hnormq]
  nlinarith

private theorem drygrad_subgradient_radial_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r : ℝ} (hr : 0 < r) {v u : H}
    (hu : ∀ q : H,
      (dryFrictionPotential (H := H) r v : EReal) +
          (inner ℝ u (q - v) : EReal) ≤ dryFrictionPotential (H := H) r q) :
    inner ℝ u v = r * ‖v‖ ∧ ‖u‖ ≤ r := by
  have hzero := hu 0
  norm_num [dryFrictionPotential] at hzero
  have hlower : r * ‖v‖ ≤ inner ℝ u v := by
    have : r * ‖v‖ - inner ℝ u v ≤ 0 := by exact_mod_cast hzero
    linarith
  have htwo := hu ((2 : ℝ) • v)
  norm_num [dryFrictionPotential] at htwo
  have hupper : inner ℝ u v ≤ r * ‖v‖ := by
    have htwo_real : r * ‖v‖ + inner ℝ u ((2 : ℝ) • v - v) ≤ r * ‖(2 : ℝ) • v‖ := by
      exact_mod_cast htwo
    rw [show (2 : ℝ) • v - v = v by module] at htwo_real
    have hnorm : ‖(2 : ℝ) • v‖ = 2 * ‖v‖ := by rw [norm_smul]; norm_num
    rw [hnorm] at htwo_real
    linarith
  have hwork : inner ℝ u v = r * ‖v‖ := le_antisymm hupper hlower
  refine ⟨hwork, ?_⟩
  have hforall : ∀ q : H, inner ℝ u q ≤ r * ‖q‖ := by
    intro q
    have hq := hu q
    have hqreal : r * ‖v‖ + inner ℝ u (q - v) ≤ r * ‖q‖ := by exact_mod_cast hq
    rw [inner_sub_right, hwork] at hqreal
    linarith
  have huu := hforall u
  rw [real_inner_self_eq_norm_sq] at huu
  by_cases hzero : ‖u‖ = 0
  · simp [hzero, le_of_lt hr]
  · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr (by simpa using hzero)
    nlinarith

private theorem neg_drygrad_subgradient_mem_projector {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r : ℝ} (hr : 0 < r) {v u g : H}
    (hsub : ∀ q : H,
      (dryFrictionPotential (H := H) r v : EReal) +
          (inner ℝ u (q - v) : EReal) ≤ dryFrictionPotential (H := H) r q)
    (hforce : v + u + g = 0) : -u ∈ frictionBallProjector r g := by
  rcases drygrad_subgradient_radial_local hr hsub with ⟨hwork, hunorm⟩
  have hpball : -u ∈ frictionBall r := by
    simpa [frictionBall, dist_eq_norm] using hunorm
  have hconvex : Convex ℝ (frictionBall (H := H) r) := by
    simpa [frictionBall] using (convex_closedBall (0 : H) r)
  have hnormal : ∀ q ∈ frictionBall (H := H) r, inner ℝ (g - (-u)) (q - (-u)) ≤ 0 := by
    intro q hq
    have hqnorm : ‖q‖ ≤ r := by simpa [frictionBall, dist_eq_norm] using hq
    have hcs : -‖v‖ * ‖q‖ ≤ inner ℝ v q := by
      convert neg_le_of_abs_le (abs_real_inner_le_norm v q) using 1
      all_goals ring
    have hmul : ‖v‖ * ‖q‖ ≤ ‖v‖ * r := mul_le_mul_of_nonneg_left hqnorm (norm_nonneg v)
    have hg : g = -v - u := by
      calc g = 0 - (v + u) := by rw [← hforce]; abel
           _ = -v - u := by abel
    have hgminus : g - (-u) = -v := by rw [hg]; abel
    have hwork' : inner ℝ v u = r * ‖v‖ := by rw [real_inner_comm]; exact hwork
    rw [hgminus, show q - (-u) = q + u by abel,
      inner_neg_left, inner_add_right, hwork']
    nlinarith
  unfold frictionBallProjector IsFrictionBallBestApproximation
  refine ⟨hpball, ?_⟩
  rw [Metric.infDist_eq_iInf]
  simpa [dist_eq_norm] using
    (norm_eq_iInf_iff_real_inner_le_zero hconvex hpball).mpr hnormal

/-- Theorem 4.1: time scaling yields the first-order and inertial DRYSTAR systems. -/
theorem theorem_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {r α s₀ : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (f : H → ℝ) (fgrad : H → H)
    (z dz x y dx dy ddx : ℝ → H)
    (_hgradient : ∀ u v, fderiv ℝ f u v = inner ℝ (fgrad u) v)
    (hsol : IsDrygradTrajectory r hr fgrad z dz (s₀ ^ 2 / (2 * (α - 1))))
    (hy : y = timeScaledTrajectory z (fun s => s ^ 2 / (2 * (α - 1))))
    (haverage : x s₀ = y s₀ ∧ ∀ s ∈ Set.Ici s₀,
      HasDerivAt x (dx s) s ∧
        dx s + ((s / (α - 1))⁻¹) • (x s - y s) = 0)
    (hdy : ∀ s, HasDerivAt y (dy s) s)
    (hddx : ∀ s, HasDerivAt dx (ddx s) s) :
    IsDryStarFirstOrder r α s₀ hr fgrad x y dx dy ∧
      ∃ p : ℝ → H, IsDryStarTrajectory r α s₀ fgrad x dx ddx p := by
  have ha1 : 0 < α - 1 := sub_pos.mpr hα
  have hτ_domain : ∀ s ∈ Set.Ici s₀,
      s ^ 2 / (2 * (α - 1)) ∈ Set.Ici (s₀ ^ 2 / (2 * (α - 1))) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hdenom : 0 < 2 * (α - 1) := mul_pos (by norm_num) ha1
    apply (div_le_div_iff_of_pos_right hdenom).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (add_nonneg (le_of_lt hs₀) (le_of_lt hspos))]
  have hτ_deriv : ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => t ^ 2 / (2 * (α - 1))) (s / (α - 1)) s := by
    intro s
    convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1
    all_goals
      field_simp [ne_of_gt ha1]
      ring
  have hfirst : IsDryStarFirstOrder r α s₀ hr fgrad x y dx dy := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hdτpos : 0 < s / (α - 1) := div_pos hspos ha1
    have hsol_s := hsol (s ^ 2 / (2 * (α - 1))) (hτ_domain s hs)
    rcases hsol_s.2 with ⟨u, husub, huseq⟩
    have hy_point : y s = z (s ^ 2 / (2 * (α - 1))) := by
      simp [hy, timeScaledTrajectory]
    have hchain : HasDerivAt y ((s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1)))) s := by
      simpa only [hy, timeScaledTrajectory] using
        (hsol_s.1.scomp s (hτ_deriv s))
    have hdy_eq : dy s = (s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1))) :=
      (hdy s).unique hchain
    refine ⟨(haverage.2 s hs).1, hdy s, u, ?_, ?_, ?_⟩
    · -- Positive one-homogeneity transports the norm subgradient along the time scale.
      intro q
      have husub_real : ∀ q : H,
          r * ‖dz (s ^ 2 / (2 * (α - 1)))‖ +
              inner ℝ u (q - dz (s ^ 2 / (2 * (α - 1)))) ≤ r * ‖q‖ := by
        intro q
        exact_mod_cast husub q
      have hscaled_sub := dryFriction_subgradient_smul_pos hdτpos husub_real q
      rw [← hdy_eq] at hscaled_sub
      exact_mod_cast hscaled_sub
    · have hscaled := congrArg (fun w : H => (s / (α - 1)) • w) huseq
      simp only [smul_add, smul_zero] at hscaled
      rw [hdy_eq, hy_point]
      exact hscaled
    · have havg := (haverage.2 s hs).2
      have hcoef : (α - 1) / s = (s / (α - 1))⁻¹ := by
        field_simp [ne_of_gt ha1, ne_of_gt hspos]
      rw [hcoef]
      exact havg
  refine ⟨hfirst, ?_⟩
  have hyx : ∀ s ∈ Set.Ici s₀, y s = x s + (s / (α - 1)) • dx s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hcne : s / (α - 1) ≠ 0 := ne_of_gt (div_pos hspos ha1)
    have havg := congrArg (fun w : H => (s / (α - 1)) • w) (haverage.2 s hs).2
    simp only [smul_add, smul_zero, smul_smul] at havg
    rw [mul_inv_cancel₀ hcne, one_smul] at havg
    calc y s = y s + ((s / (α - 1)) • dx s + (x s - y s)) := by rw [havg, add_zero]
         _ = x s + (s / (α - 1)) • dx s := by abel
  have hdy_avg : ∀ s ∈ Set.Ici s₀,
      dy s = (s / (α - 1)) • ddx s + (1 + 1 / (α - 1)) • dx s := by
    intro s hs
    let R : ℝ → H := fun t => x t + (t / (α - 1)) • dx t
    have hR : HasDerivAt R
        (dx s + (1 / (α - 1)) • dx s + (s / (α - 1)) • ddx s) s := by
      convert (haverage.2 s hs).1.add
        ((hasDerivAt_id s).div_const (α - 1) |>.smul (hddx s)) using 1
      all_goals
        simp
        module
    have hdiff : HasDerivAt (fun t => y t - R t)
        (dy s - (dx s + (1 / (α - 1)) • dx s + (s / (α - 1)) • ddx s)) s :=
      (hdy s).sub hR
    have hzero : dy s - (dx s + (1 / (α - 1)) • dx s +
        (s / (α - 1)) • ddx s) = 0 := by
      change s₀ ≤ s at hs
      rcases lt_or_eq_of_le hs with hslt | rfl
      · have heq : (fun t => y t - R t) =ᶠ[nhds s] fun _ => 0 := by
          filter_upwards [eventually_gt_nhds hslt] with t ht
          simp [R, hyx t (le_of_lt ht)]
        exact (hdiff.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s 0)
      · have heq : (fun t => y t - R t) =ᶠ[nhdsWithin s₀ (Set.Ioi s₀)] fun _ => 0 := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          change s₀ < t at ht
          simp [R, hyx t (le_of_lt ht)]
        calc
          dy s₀ - (dx s₀ + (1 / (α - 1)) • dx s₀ + (s₀ / (α - 1)) • ddx s₀) =
              derivWithin (fun t => y t - R t) (Set.Ioi s₀) s₀ :=
            (hdiff.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi s₀)).symm
          _ = 0 :=
            by
              have hend : y s₀ - R s₀ = 0 := by
                simp [R, hyx s₀ (Set.mem_Ici.mpr le_rfl)]
              have hzeroDeriv : HasDerivWithinAt (fun t => y t - R t) 0 (Set.Ioi s₀) s₀ :=
                (hasDerivAt_const s₀ (0 : H)).hasDerivWithinAt.congr_of_eventuallyEq
                  heq hend
              exact hzeroDeriv.derivWithin (uniqueDiffWithinAt_Ioi s₀)
    rw [sub_eq_zero] at hzero
    rw [hzero]
    module
  classical
  let uOf : ℝ → H := fun s => if hs : s ∈ Set.Ici s₀ then
    Classical.choose ((hsol (s ^ 2 / (2 * (α - 1))) (hτ_domain s hs)).2) else 0
  have huOf_spec : ∀ s (hs : s ∈ Set.Ici s₀),
      (∀ q : H,
        (dryFrictionPotential (H := H) r (dz (s ^ 2 / (2 * (α - 1)))) : EReal) +
          (inner ℝ (uOf s) (q - dz (s ^ 2 / (2 * (α - 1)))) : EReal) ≤
            dryFrictionPotential (H := H) r q) ∧
        dz (s ^ 2 / (2 * (α - 1))) + uOf s + fgrad (z (s ^ 2 / (2 * (α - 1)))) = 0 := by
    intro s hs
    dsimp [uOf]
    rw [dif_pos hs]
    exact Classical.choose_spec ((hsol _ (hτ_domain s hs)).2)
  let p : ℝ → H := fun s => -uOf s
  refine ⟨p, ?_⟩
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hcne : s / (α - 1) ≠ 0 := ne_of_gt (div_pos hspos ha1)
  have hy_point : y s = z (s ^ 2 / (2 * (α - 1))) := by simp [hy, timeScaledTrajectory]
  have hsol_s := hsol (s ^ 2 / (2 * (α - 1))) (hτ_domain s hs)
  have hchain : HasDerivAt y ((s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1)))) s := by
    simpa only [hy, timeScaledTrajectory] using hsol_s.1.scomp s (hτ_deriv s)
  have hdy_eq : dy s = (s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1))) :=
    (hdy s).unique hchain
  rcases huOf_spec s hs with ⟨hsub, hforce⟩
  refine ⟨(haverage.2 s hs).1, hddx s, ?_, ?_⟩
  · have hproj := neg_drygrad_subgradient_mem_projector hr hsub hforce
    rw [← hy_point, hyx s hs] at hproj
    simpa [p] using hproj
  · have hscaled := congrArg (fun w : H => (s / (α - 1)) • w) hforce
    simp only [smul_add, smul_zero] at hscaled
    rw [← hdy_eq, ← hy_point] at hscaled
    have hdiv := congrArg (fun w : H => (s / (α - 1))⁻¹ • w) hscaled
    simp only [smul_add, smul_zero, smul_smul] at hdiv
    have hone : (s / (α - 1))⁻¹ * (s / (α - 1)) = 1 := inv_mul_cancel₀ hcne
    rw [hone, one_smul] at hdiv
    have hcoef : (s / (α - 1))⁻¹ * (1 + 1 / (α - 1)) = α / s := by
      field_simp [ne_of_gt hspos, ne_of_gt ha1]
      ring
    rw [hdy_avg s hs, smul_add, smul_smul, smul_smul, hcoef] at hdiv
    rw [hone, one_smul] at hdiv
    simp only [one_smul] at hdiv
    rw [← hyx s hs]
    simp only [p]
    calc
      ddx s + (α / s) • dx s + fgrad (y s) - -uOf s =
          ddx s + (α / s) • dx s + uOf s + fgrad (y s) := by abel
      _ = 0 := hdiv

end AttouchAdlyDryFrictionDynamics2023
