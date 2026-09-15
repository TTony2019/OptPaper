import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.prop_3
import Mathlib
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open Filter MeasureTheory

private theorem cor218_eventually_norm_le_of_tendsto_weakly
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {x : ℝ → H} {z : H}
    (hxweak : Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
      (nhds (toWeakSpace ℝ H z))) : ∃ C : ℝ, ∀ᶠ t in atTop, ‖x t‖ ≤ C := by
  by_contra hbounded
  push Not at hbounded
  have hbad (n : ℕ) : ∃ t : ℝ, (n : ℝ) ≤ t ∧ (n : ℝ) < ‖x t‖ :=
    Filter.frequently_atTop.mp (hbounded n) (n : ℝ)
  choose t ht_ge ht_large using hbad
  have htend : Tendsto t atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro a
    obtain ⟨n, hn⟩ := exists_nat_ge a
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact le_trans (hn.trans (Nat.cast_le.mpr hm)) (ht_ge m)
  have hseqweak : Tendsto (fun n ↦ toWeakSpace ℝ H (x (t n))) atTop
      (nhds (toWeakSpace ℝ H z)) := hxweak.comp htend
  obtain ⟨C, _, hC⟩ := (bounded_range_of_tendsto_weakly hseqweak).exists_pos_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  linarith [ht_large n, hC (x (t n)) (Set.mem_range_self n)]

private theorem cor218_strong_tendsto_of_eventually_compact_and_weak_scalar_convergence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ℝ → H) (xStar : H) (K : Set H) (hK : IsCompact K)
    (hxK : ∀ᶠ t in atTop, x t ∈ K)
    (hweak : ∀ ell : H →L[ℝ] ℝ,
      Tendsto (fun t => ell (x t)) atTop (nhds (ell xStar))) :
    Tendsto x atTop (nhds xStar) := by
  apply hK.tendsto_nhds_of_unique_mapClusterPt hxK
  intro z _ hz
  have hscalar : ∀ ell : H →L[ℝ] ℝ, ell z = ell xStar := by
    intro ell
    by_contra hne
    let eps : ℝ := dist (ell z) (ell xStar) / 3
    have hdist : 0 < dist (ell z) (ell xStar) := dist_pos.mpr hne
    have heps : 0 < eps := by
      dsimp [eps]
      positivity
    have hEvent : ∀ᶠ t in atTop, ell (x t) ∈ Metric.ball (ell xStar) eps :=
      (hweak ell).eventually (Metric.ball_mem_nhds _ heps)
    have hCluster : MapClusterPt (ell z) atTop (fun t => ell (x t)) := by
      simpa [Function.comp_def] using hz.tendsto_comp (ell.continuous.tendsto z)
    rcases ((hCluster.frequently (Metric.ball_mem_nhds _ heps)).and_eventually hEvent).exists with
      ⟨t, htZ, htStar⟩
    have hltZ : dist (ell z) (ell (x t)) < eps := by
      simpa [dist_comm] using htZ
    have hcontra : dist (ell z) (ell xStar) < dist (ell z) (ell xStar) := by
      calc
        dist (ell z) (ell xStar) ≤ dist (ell z) (ell (x t)) + dist (ell (x t)) (ell xStar) :=
          dist_triangle _ _ _
        _ < eps + eps := add_lt_add hltZ (Metric.mem_ball.mp htStar)
        _ < dist (ell z) (ell xStar) := by
          dsimp [eps]
          linarith
    exact lt_irrefl _ hcontra
  have hinner := hscalar (innerSL ℝ (z - xStar))
  have hzero : ‖z - xStar‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    calc
      inner ℝ (z - xStar) (z - xStar) =
          inner ℝ (z - xStar) z - inner ℝ (z - xStar) xStar := by
            rw [inner_sub_right]
      _ = 0 := sub_eq_zero.mpr (by
        simpa only [innerSL_apply_apply, inner_sub_left, real_inner_self_eq_norm_sq] using hinner)
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [sq_nonneg ‖z - xStar‖]))

/-- Corollary 2.18: bounded inf-compactness gives strong convergence of every orbit. -/
theorem bounded_inf_compact_strong_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x v : ℝ → H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hlam : 0 < lam) (hmu : 0 < mu)
    (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)))
    (hinfcompact : ∀ r a : ℝ,
      IsCompact (Metric.closedBall (Classical.choose hS) r ∩
        {y | (Phi y : EReal) ≤ (a : EReal)})) :
    ∃ z ∈ S, Tendsto x atTop (nhds z) := by
  let z0 : H := Classical.choose hS
  have hz0 : z0 ∈ S := Classical.choose_spec hS
  obtain ⟨_, _, xinf, hxinfS, hxweak, hvalue⟩ :=
    proposition_2_16 S Phi hPhi B x v z0 lam mu beta hS hz0 hlam hmu hmu_lam hbeta
      hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2 horbit hsolution hdom hweak
  obtain ⟨C, hC⟩ := cor218_eventually_norm_le_of_tendsto_weakly hxweak
  let a : ℝ := (Phi xinf : EReal).toReal + 1
  let R : ℝ := C + ‖z0‖
  let K : Set H := Metric.closedBall z0 R ∩ {y | (Phi y : EReal) ≤ (a : EReal)}
  have hK : IsCompact K := by
    dsimp [K, R, a, z0]
    exact hinfcompact (C + ‖Classical.choose hS‖) ((Phi xinf : EReal).toReal + 1)
  have hEventuallyK : ∀ᶠ t in atTop, x t ∈ K := by
    have hlt : ∀ᶠ t in atTop, (Phi (x t) : EReal).toReal < a := by
      dsimp [a]
      exact hvalue.eventually_lt_const (lt_add_one _)
    filter_upwards [hC, hlt, eventually_ge_atTop (0 : ℝ)] with t ht htv ht0
    constructor
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hsum : ‖x t‖ + ‖z0‖ ≤ C + ‖z0‖ := by linarith
      exact le_trans (norm_sub_le _ _) (by simpa [R] using hsum)
    · have hcoer : ((Phi (x t) : EReal).toReal : EReal) ≤ (a : EReal) := by
        exact_mod_cast le_of_lt htv
      exact (EReal.le_coe_toReal (ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp
        (hdom.1 t ht0)))).trans hcoer
  have hscalar : ∀ ell : H →L[ℝ] ℝ,
      Tendsto (fun t ↦ ell (x t)) atTop (nhds (ell xinf)) := by
    intro ell
    let u : H := (InnerProductSpace.toDual ℝ H).symm ell
    have hu := (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H xinf) |>.comp hxweak
    have hrepr (y : H) : ell y = inner ℝ y u := by
      calc
        ell y = inner ℝ u y := (InnerProductSpace.toDual_symm_apply).symm
        _ = inner ℝ y u := real_inner_comm _ _
    simpa only [hrepr] using hu
  exact ⟨xinf, hxinfS,
    cor218_strong_tendsto_of_eventually_compact_and_weak_scalar_convergence x xinf K hK
      hEventuallyK hscalar⟩

end AbbasDynamical2015
