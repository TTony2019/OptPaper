import Mathlib
import Foundation.Differentiation.Gateaux
import Foundation.Optimization.Argmin
import Foundation.Projection.BestApproximation
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.prop_3

namespace Alvarez2002

open Filter
open scoped InnerProductSpace

private theorem quadratic_form_zero_iff_mem_ker {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →L[ℝ] H)
    (hselfadjoint : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ)
    (hpositive : ∀ u, 0 ≤ ⟪A u, u⟫_ℝ) (u : H) :
    ⟪A u, u⟫_ℝ = 0 ↔ u ∈ A.ker := by
  constructor
  · intro hu
    have hzero : ∀ v : H, ⟪A u, v⟫_ℝ = 0 := by
      intro v
      by_contra hne
      let q : ℝ := ⟪A v, v⟫_ℝ
      let b : ℝ := ⟪A u, v⟫_ℝ
      have hq : 0 ≤ q := by exact hpositive v
      have hne' : b ≠ 0 := by simpa [b] using hne
      have hbpos : 0 < b ∨ b < 0 := lt_or_gt_of_ne hne'.symm
      rcases hbpos with hbpos | hbneg
      · let t : ℝ := b / (q + 1)
        have ht : 0 < t := by
          dsimp [t]
          positivity
        have hqt : 0 ≤ ⟪A (u - t • v), u - t • v⟫_ℝ := hpositive _
        have hqexpand :
            ⟪A (u - t • v), u - t • v⟫_ℝ = t ^ 2 * q - 2 * t * b := by
          dsimp [q, b]
          simp [map_sub, map_smul, inner_sub_left, inner_sub_right,
            inner_smul_left, inner_smul_right, hselfadjoint u v, real_inner_comm, hu]
          ring
        rw [hqexpand] at hqt
        have htq : t * (q + 1) = b := by
          dsimp [t]
          field_simp
        nlinarith [sq_nonneg t]
      · let t : ℝ := (-b) / (q + 1)
        have ht : 0 < t := by
          dsimp [t]
          exact div_pos (neg_pos.mpr hbneg) (by linarith)
        have hqt : 0 ≤ ⟪A (u + t • v), u + t • v⟫_ℝ := hpositive _
        have hqexpand :
            ⟪A (u + t • v), u + t • v⟫_ℝ = t ^ 2 * q + 2 * t * b := by
          dsimp [q, b]
          simp [map_add, map_smul, inner_add_left, inner_add_right,
            inner_smul_left, inner_smul_right, hselfadjoint u v, real_inner_comm, hu]
          ring
        rw [hqexpand] at hqt
        have htq : t * (q + 1) = -b := by
          dsimp [t]
          field_simp
        nlinarith [sq_nonneg t]
    apply (innerSL_inj (𝕜 := ℝ) (E := H)).mp
    ext v
    simpa only [innerSL_apply_apply, inner_zero_left] using hzero v
  · intro hu
    change A u = 0 at hu
    simp [hu]

private theorem quadratic_potential_convex {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (A : H →L[ℝ] H)
    (hΦ : ∀ u, Φ u = (1 / 2 : ℝ) * ⟪A u, u⟫_ℝ)
    (hselfadjoint : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ)
    (hpositive : ∀ u, 0 ≤ ⟪A u, u⟫_ℝ) :
    ConvexOn ℝ Set.univ Φ := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [hΦ, hΦ, hΦ]
  have hquad :
      0 ≤ ⟪A (x - y), x - y⟫_ℝ := hpositive (x - y)
  have hexpand :
      ⟪A (x - y), x - y⟫_ℝ = ⟪A x, x⟫_ℝ + ⟪A y, y⟫_ℝ -
        2 * ⟪A x, y⟫_ℝ := by
    simp [map_sub, inner_sub_left, inner_sub_right, hselfadjoint x y,
      real_inner_comm]
    ring
  rw [hexpand] at hquad
  have hquad' :
      0 ≤ ⟪x, A x⟫_ℝ + ⟪y, A y⟫_ℝ - 2 * ⟪x, A y⟫_ℝ := by
    have hquad'' := hquad
    rw [hselfadjoint x y] at hquad''
    simpa [real_inner_comm] using hquad''
  simp [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hselfadjoint x y, real_inner_comm,
    smul_eq_mul]
  have habnonneg : 0 ≤ a * b := mul_nonneg ha hb
  have hxpos : 0 ≤ ⟪x, A x⟫_ℝ := by simpa [real_inner_comm] using hpositive x
  have hypos : 0 ≤ ⟪y, A y⟫_ℝ := by simpa [real_inner_comm] using hpositive y
  have hident :
      a * (1 / 2 * ⟪x, A x⟫_ℝ) + b * (1 / 2 * ⟪y, A y⟫_ℝ) -
          (1 / 2 : ℝ) *
            (a * (a * ⟪x, A x⟫_ℝ + b * ⟪x, A y⟫_ℝ) +
              b * (a * ⟪x, A y⟫_ℝ + b * ⟪y, A y⟫_ℝ)) =
        (1 / 2 : ℝ) * (a * b) *
          (⟪x, A x⟫_ℝ + ⟪y, A y⟫_ℝ - 2 * ⟪x, A y⟫_ℝ) := by
    linear_combination
      -(1 / 2 : ℝ) *
        (a * ⟪x, A x⟫_ℝ + b * ⟪y, A y⟫_ℝ) * hab
  have hnonneg : 0 ≤
      (1 / 2 : ℝ) * (a * b) *
        (⟪x, A x⟫_ℝ + ⟪y, A y⟫_ℝ - 2 * ⟪x, A y⟫_ℝ) := by
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact mul_nonneg (mul_nonneg hhalf habnonneg) hquad'
  nlinarith [hident, hnonneg]

private theorem quadratic_gradient_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (A : H →L[ℝ] H)
    (hΦ : AssumptionH H Φ) (hquadratic : ∀ u, Φ u = (1 / 2 : ℝ) * ⟪A u, u⟫_ℝ)
    (hselfadjoint : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) :
    gradient Φ = A := by
  have hΦC1 : ContDiff ℝ 1 Φ :=
    hΦ.twice_continuously_differentiable.of_le (by norm_num)
  have hAdj : A.adjoint = A := by
    apply ContinuousLinearMap.ext
    intro u
    apply (innerSL_inj (𝕜 := ℝ) (E := H)).mp
    ext v
    calc
      ⟪A.adjoint u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
        ContinuousLinearMap.adjoint_inner_left A v u
      _ = ⟪A u, v⟫_ℝ := (hselfadjoint u v).symm
  funext u
  have hleft : HasGradientAt Φ (gradient Φ u) u :=
    (hΦC1.differentiable (by norm_num) u).hasGradientAt
  have hright0 := quadratic_affine_functional_hasGradientAt A 0 u
  have hright : HasGradientAt
      (fun y : H => (1 / 2 : ℝ) * quadratic_affine_functional A 0 y)
      ((1 / 2 : ℝ) • ((A + A.adjoint) u - 0)) u := by
    change HasGradientAt ((1 / 2 : ℝ) • quadratic_affine_functional A 0)
      ((1 / 2 : ℝ) • ((A + A.adjoint) u - 0)) u
    have hsmul (v : H) :
        (InnerProductSpace.toDual ℝ H).symm
            ((1 / 2 : ℝ) • (InnerProductSpace.toDual ℝ H) v) =
          (1 / 2 : ℝ) • v := by
      rw [(InnerProductSpace.toDual ℝ H).symm.map_smulₛₗ,
        (InnerProductSpace.toDual ℝ H).symm_apply_apply]
      simp
    convert (hright0.hasFDerivAt.const_smul (1 / 2 : ℝ)).hasGradientAt using 1
    exact (hsmul _).symm
  have hfun : (fun y : H => (1 / 2 : ℝ) * quadratic_affine_functional A 0 y) = Φ := by
    funext y
    simp [quadratic_affine_functional, hquadratic y]
  have hright' : HasGradientAt Φ
      ((1 / 2 : ℝ) • ((A + A.adjoint) u - 0)) u := by
    rw [← hfun]
    exact hright
  have heq := hleft.unique hright'
  calc
    gradient Φ u = (1 / 2 : ℝ) • ((A + A.adjoint) u - 0) := heq
    _ = (1 / 2 : ℝ) • (A u + A u) := by rw [hAdj]; simp
    _ = A u := by module

/-- The quadratic-potential remark following Theorem 5.1: the minimizers are
`Ker A`, and the trajectory converges strongly to the projection of its
initial affine momentum onto that kernel. -/
theorem quadratic_potential_limit_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (A : H →L[ℝ] H)
    (α β : ℝ) (x : ℝ → H) (hΦ : AssumptionH H Φ)
    (hquadratic : ∀ u, Φ u = (1 / 2 : ℝ) * ⟪A u, u⟫_ℝ)
    (hselfadjoint : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ)
    (hpositive : ∀ u, 0 ≤ ⟪A u, u⟫_ℝ)
    (hsol : IsDINTrajectory H Φ α β x) (hx : ContDiff ℝ 2 x)
    (hαβ : α * β ≤ 1) :
    Optimization.argminSet Φ = (A.ker : Set H) ∧
      ∃ p, p ∈ A.ker ∧
        ‖x 0 + (α⁻¹ : ℝ) • deriv x 0 - p‖ =
          Metric.infDist (x 0 + (α⁻¹ : ℝ) • deriv x 0) (A.ker : Set H) ∧
        Tendsto x atTop (nhds p) := by
  have hargmin : Optimization.argminSet Φ = (A.ker : Set H) := by
    ext u
    constructor
    · intro hu
      have hΦu : Φ u ≤ Φ 0 := hu 0
      have hΦ0 : Φ 0 = 0 := by simp [hquadratic]
      have hqu : ⟪A u, u⟫_ℝ = 0 := by
        have hnonneg : 0 ≤ ⟪A u, u⟫_ℝ := hpositive u
        rw [hquadratic, hΦ0] at hΦu
        nlinarith
      exact (quadratic_form_zero_iff_mem_ker A hselfadjoint hpositive u).mp hqu
    · intro hu v
      rw [hquadratic, hquadratic]
      have hzero : A u = 0 := by exact hu
      simpa [hzero] using mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (hpositive v)
  have hconvex : ConvexOn ℝ Set.univ Φ :=
    quadratic_potential_convex Φ A hquadratic hselfadjoint hpositive
  have hmin : (Optimization.argminSet Φ).Nonempty := by
    rw [hargmin]
    exact ⟨0, by simp⟩
  obtain ⟨p, hpmin, hxp⟩ :=
    din_strong_convergence_of_even_potential Φ α β x hΦ hconvex hmin hsol hx hαβ
      (by intro u; rw [hquadratic, hquadratic]; simp)
  have hpker : p ∈ A.ker := by
    have hpmin' : p ∈ (A.ker : Set H) := by simpa [hargmin] using hpmin
    exact hpmin'
  let q : H := x 0 + (α⁻¹ : ℝ) • deriv x 0
  let K : Set H := (A.ker : Set H)
  have hKnonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K]
  have hKclosed : IsClosed K := by
    simpa [K] using (A.isClosed_ker : IsClosed (A.ker : Set H))
  have hKconvex : Convex ℝ K := by
    simpa [K] using (A.ker.convex : Convex ℝ (A.ker : Set H))
  let hCheb := isChebyshev_of_nonempty_isClosed_convex hKnonempty hKclosed hKconvex
  refine ⟨hargmin, p, hpker, ?_, hxp⟩
  have horth : ∀ z ∈ K, ⟪q - p, z⟫_ℝ = 0 := by
    intro z hz
    have hgrad_eq : gradient Φ = A :=
      quadratic_gradient_eq Φ A hΦ hquadratic hselfadjoint
    have hhess_eq : ∀ u, fderiv ℝ (gradient Φ) u = A := by
      intro u
      rw [hgrad_eq]
      exact A.hasFDerivAt.fderiv
    have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
      obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hxp) 1 zero_lt_one
      let T₀ : ℝ := max T 0
      have htail : ∀ t, T₀ ≤ t → ‖x t‖ ≤ ‖p‖ + 1 := by
        intro t ht
        have hdist' : dist (x t) p < 1 :=
          hT t (le_trans (le_max_left T 0) ht)
        have hsub : ‖x t - p‖ < 1 := by
          simpa [dist_eq_norm] using hdist'
        calc
          ‖x t‖ = ‖(x t - p) + p‖ := by congr 1; module
          _ ≤ ‖x t - p‖ + ‖p‖ := norm_add_le _ _
          _ ≤ 1 + ‖p‖ := by linarith
          _ = ‖p‖ + 1 := by ring
      have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
        exact isCompact_Icc.image_of_continuousOn
          (hx.continuous.continuousOn.mono Set.Icc_subset_Ici_self)
      rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
      refine isBounded_iff_forall_norm_le.mpr ⟨max R₀ (‖p‖ + 1), ?_⟩
      rintro y ⟨t, ht, rfl⟩
      by_cases hle : t ≤ T₀
      · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
      · exact (htail t (le_of_not_ge hle)).trans (le_max_right _ _)
    have hpartiii := din_global_properties_part_iii Φ hΦ α β hsol.1 hsol.2.1
      (x 0) (deriv x 0) x rfl rfl hsol hx hx_bounded
    obtain ⟨_, _, _, _, hvlim, _, _⟩ := hpartiii
    let f : ℝ → ℝ := fun t => ⟪deriv x t + α • x t, z⟫_ℝ
    have hx_at (t : ℝ) : HasDerivAt x (deriv x t) t :=
      (hx.differentiable (by norm_num) t).hasDerivAt
    have hv_at (t : ℝ) : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
      (hx.differentiable_deriv_two t).hasDerivAt
    have hu_at (t : ℝ) : HasDerivAt (fun s => deriv x s + α • x s)
        (deriv (deriv x) t + α • deriv x t) t := by
      exact (hv_at t).add ((hx_at t).const_smul α)
    have hzero_deriv (t : ℝ) (ht : 0 ≤ t) :
        deriv (fun s => ⟪deriv x s + α • x s, z⟫_ℝ) t = 0 := by
      have heq := hsol.2.2 t ht
      rw [hhess_eq (x t), hgrad_eq] at heq
      have hz' : A z = 0 := by
        change A z = 0 at hz
        exact hz
      have hAv : ⟪A (deriv x t), z⟫_ℝ = 0 := by
        rw [hselfadjoint]
        simp [hz']
      have hAx : ⟪A (x t), z⟫_ℝ = 0 := by
        rw [hselfadjoint]
        simp [hz']
      have hode_inner :
          ⟪deriv (deriv x) t + α • deriv x t, z⟫_ℝ = 0 := by
        have heq' := congrArg (fun v : H => ⟪v, z⟫_ℝ) heq
        simpa [inner_add_left, inner_smul_left, hAv, hAx] using heq'
      have hf' := (hu_at t).inner ℝ (hasDerivAt_const t z)
      rw [hf'.deriv]
      simp only [inner_zero_right, hode_inner, add_zero]
    have hf_diff : DifferentiableOn ℝ f (Set.Ici (0 : ℝ)) := by
      intro t ht
      have hf_at := (hu_at t).inner ℝ (hasDerivAt_const t z)
      simpa [f] using hf_at.differentiableAt.differentiableWithinAt
    have hf_fderiv : ∀ t ∈ Set.Ici (0 : ℝ),
        fderivWithin ℝ f (Set.Ici (0 : ℝ)) t = 0 := by
      intro t ht
      have hf_at : HasDerivAt f 0 t := by
        have hf_raw := (hu_at t).inner ℝ (hasDerivAt_const t z)
        have hder0 := hzero_deriv t ht
        rw [hf_raw.deriv] at hder0
        have hinner :
            ⟪deriv (deriv x) t + α • deriv x t, z⟫_ℝ = 0 := by
          simpa [inner_zero_right] using hder0
        convert hf_raw using 1;
          simp [inner_zero_right, hinner]
      have hfw :=
        ((hf_at.hasDerivWithinAt (s := Set.Ici (0 : ℝ))).hasFDerivWithinAt).fderivWithin
          (uniqueDiffOn_Ici 0 t ht)
      simpa using hfw
    have hf_const : ∀ t ∈ Set.Ici (0 : ℝ), f t = f 0 := by
      intro t ht
      exact (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero hf_diff hf_fderiv
        ht (Set.mem_Ici.mpr (le_refl 0))
    have hflim : Tendsto f atTop (nhds (⟪(0 : H) + α • p, z⟫_ℝ)) := by
      have hsum : Tendsto (fun t => deriv x t + α • x t) atTop
          (nhds ((0 : H) + α • p)) := hvlim.add (hxp.const_smul α)
      simpa [f] using hsum.inner (tendsto_const_nhds : Tendsto (fun _ : ℝ => z) atTop (nhds z))
    have hflim0 : Tendsto f atTop (nhds (f 0)) := by
      apply (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hf_const t (Set.mem_Ici.mpr ht)
    have hfeq : f 0 = ⟪(0 : H) + α • p, z⟫_ℝ :=
      tendsto_nhds_unique hflim0 hflim
    have hfeq' : ⟪deriv x 0, z⟫_ℝ + α * ⟪x 0, z⟫_ℝ =
        α * ⟪p, z⟫_ℝ := by
      simpa [f, inner_add_left, real_inner_smul_left] using hfeq
    have hzorth : α * ⟪q - p, z⟫_ℝ = 0 := by
      dsimp [q]
      rw [inner_sub_left, inner_add_left, real_inner_smul_left]
      field_simp [ne_of_gt hsol.1]
      nlinarith [hfeq']
    exact (mul_eq_zero.mp hzorth).resolve_left (ne_of_gt hsol.1)
  have hp_proj : p = projectionPoint K hCheb q := by
    refine (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hCheb hKconvex).mpr ?_
    refine ⟨by simpa [K] using hpker, ?_⟩
    intro z hz
    have hzorth := horth z hz
    have hporth : ⟪q - p, p⟫_ℝ = 0 := by
      have := horth p (by simpa [K] using hpker)
      exact this
    have hpterm : ⟪p, q - p⟫_ℝ = 0 := by
      simpa [real_inner_comm] using hporth
    have hzorth' : ⟪z, q - p⟫_ℝ = 0 := by
      simpa [real_inner_comm] using hzorth
    have : ⟪z - p, q - p⟫_ℝ = 0 := by
      rw [inner_sub_left]
      rw [hzorth', hpterm]
      ring
    exact le_of_eq this
  calc
    ‖q - p‖ = dist q p := by simp [dist_eq_norm]
    _ = dist q (projectionPoint K hCheb q) := by rw [← hp_proj]
    _ = Metric.infDist q K := (projectionPoint_isBestApproximation K hCheb q).2
    _ = Metric.infDist (x 0 + (α⁻¹ : ℝ) • deriv x 0) (A.ker : Set H) := by simp [q, K]

end Alvarez2002
