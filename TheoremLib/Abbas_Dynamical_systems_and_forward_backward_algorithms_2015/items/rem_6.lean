import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.thm_4
import Mathlib
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open Filter MeasureTheory
open scoped Pointwise

private theorem antitone_norm_sq_integrableOn_Ici_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] (r : ℝ → E)
    (hanti : AntitoneOn (fun t => ‖r t‖) (Set.Ici 0))
    (hint : IntegrableOn (fun t : ℝ => ‖r t‖ ^ 2) (Set.Ici 0)) :
    Tendsto r atTop (nhds 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  rcases h with ⟨ε, hε, hbad⟩
  have htail : Tendsto (fun n : ℕ => ∫ x in Set.Ici (n : ℝ), ‖r x‖ ^ 2)
      atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone
      (f := fun x : ℝ => ‖r x‖ ^ 2) (fun n : ℕ => measurableSet_Ici)
      (fun m n hmn => Set.Ici_subset_Ici.mpr (Nat.cast_le.mpr hmn))
      ⟨0, hint.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))⟩
    have hempty : (⋂ n : ℕ, Set.Ici (n : ℝ)) = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact False.elim ((not_le_of_gt hn) (Set.mem_iInter.mp hx n))
      · simp
    simpa [hempty] using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail) _ (sq_pos_of_pos hε)
  obtain ⟨u, huN, hubad⟩ := hbad ((N : ℝ) + 1)
  have hu0 : 0 ≤ u := by linarith
  have hlow : ∀ x ∈ Set.Ioc (u - 1) u, ε ^ 2 ≤ ‖r x‖ ^ 2 := by
    intro x hx
    have hub : ε ≤ ‖r u‖ := by simpa using hubad
    have hxnorm : ‖r u‖ ≤ ‖r x‖ :=
      hanti (Set.mem_Ici.mpr (by linarith [hx.1])) (Set.mem_Ici.mpr hu0) hx.2
    nlinarith [norm_nonneg (r x)]
  have hint_lower : ε ^ 2 ≤ ∫ x in Set.Ioc (u - 1) u, ‖r x‖ ^ 2 := by
    calc
      ε ^ 2 = ∫ x in Set.Ioc (u - 1) u, ε ^ 2 := by
        simp [MeasureTheory.integral_const]
      _ ≤ ∫ x in Set.Ioc (u - 1) u, ‖r x‖ ^ 2 := by
        apply MeasureTheory.integral_mono_ae
        · exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
        · exact hint.mono_set (fun x hx => Set.mem_Ici.mpr (by linarith [hx.1]))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          exact hlow x hx
  have hinter : Set.Ioc (u - 1) u ⊆ Set.Ici (N : ℝ) :=
    fun x hx => Set.mem_Ici.mpr (by linarith [hx.1, huN])
  have hint_upper : ∫ x in Set.Ioc (u - 1) u, ‖r x‖ ^ 2 ≤
      ∫ x in Set.Ici (N : ℝ), ‖r x‖ ^ 2 := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hint.mono_set (Set.Ici_subset_Ici.mpr (Nat.cast_nonneg N))
    · filter_upwards with x
      exact sq_nonneg _
    · exact hinter.eventuallyLE
  have hN' := hN N le_rfl
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), ‖r x‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  change |(∫ x in Set.Ici (N : ℝ), ‖r x‖ ^ 2) - 0| < _ at hN'
  simp only [sub_zero, abs_of_nonneg htail_nonneg] at hN'
  linarith

private theorem eventually_norm_le_of_tendsto_weakly_trajectory
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
  obtain ⟨C, hCpos, hC⟩ := (bounded_range_of_tendsto_weakly hseqweak).exists_pos_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hle : ‖x (t n)‖ ≤ C := hC _ (Set.mem_range_self n)
  linarith [ht_large n]

private theorem strong_tendsto_of_eventually_compact_and_weak_scalar_convergence
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
      linarith
    have hEvent : ∀ᶠ t in atTop, ell (x t) ∈ Metric.ball (ell xStar) eps :=
      (hweak ell).eventually (Metric.ball_mem_nhds _ heps)
    have hCluster : MapClusterPt (ell z) atTop (fun t => ell (x t)) := by
      simpa [Function.comp_def] using hz.tendsto_comp (ell.continuous.tendsto z)
    rcases ((hCluster.frequently (Metric.ball_mem_nhds _ heps)).and_eventually hEvent).exists with
      ⟨t, htZ, htStar⟩
    have hltZ : dist (ell z) (ell (x t)) < eps := by
      simpa [dist_comm] using htZ
    have hltStar : dist (ell (x t)) (ell xStar) < eps := Metric.mem_ball.mp htStar
    have hcontra : dist (ell z) (ell xStar) < dist (ell z) (ell xStar) := by
      calc
        dist (ell z) (ell xStar) ≤ dist (ell z) (ell (x t)) + dist (ell (x t)) (ell xStar) :=
          dist_triangle _ _ _
        _ < eps + eps := add_lt_add hltZ hltStar
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

/-- Remark 4.2: strong monotonicity or bounded inf-compactness yields strong convergence. -/
theorem semigroup_strong_convergence_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (S : Set H) (x : ℝ → H)
    (beta : ℝ) (hS : S.Nonempty) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (horbit : ForwardBackwardSemigroupOrbit Phi B x)
    (hA : ∀ y, A y = ERealFunction.subdifferential Phi y + ({B y} : Set H))
    (hstrongly_monotone :
      (∃ rho : ℝ, 0 < rho ∧ ∀ ⦃a b u w⦄, u ∈ A a → w ∈ A b → rho * ‖a - b‖ ^ 2 ≤
          inner ℝ (a - b) (u - w)) ∨
      ((∀ r a : ℝ, IsCompact {y | ‖y‖ ≤ r ∧ (Phi y : EReal) ≤ (a : EReal)}) ∧
        ∃ a : ℝ, ∀ᶠ t in atTop, (Phi (x t) : EReal) ≤ (a : EReal))) :
    ∃ z ∈ S, Tendsto x atTop (nhds z) := by
  obtain ⟨hdxint, ⟨z, hz, hxweak⟩, _⟩ :=
    semigroup_convergence Phi hPhi S B x beta hS hbeta hB hsolution horbit
  have hressqint : IntegrableOn (fun t ↦ ‖horbit.residual t‖ ^ 2) (Set.Ici 0) := by
    refine Integrable.congr hdxint ?_
    filter_upwards [horbit.residual_eq_neg_deriv] with t ht
    rw [ht, norm_neg]
  have hreszero := antitone_norm_sq_integrableOn_Ici_tendsto_zero horbit.residual
    horbit.residual_norm_antitone hressqint
  rcases hstrongly_monotone with hsm | ⟨hinfcompact, a, hPhiTail⟩
  · rcases hsm with ⟨rho, hrho, hsm⟩
    have hzeroA : 0 ∈ A z := by
      rw [hA z]
      refine Set.mem_add.mpr ⟨-B z, (hsolution z).mp hz, B z, by simp, by abel⟩
    have hresA (t : ℝ) (ht : 0 ≤ t) : horbit.residual t ∈ A (x t) := by
      rw [hA (x t)]
      exact horbit.residual_mem t ht
    have hupper : Tendsto (fun t ↦ rho⁻¹ * ‖horbit.residual t‖) atTop (nhds 0) := by
      simpa using hreszero.norm.const_mul rho⁻¹
    have hnorm : Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hupper_event : ∀ᶠ t in atTop, rho⁻¹ * ‖horbit.residual t‖ ∈
          Metric.ball 0 ε := hupper.eventually (Metric.ball_mem_nhds _ hε)
      apply Filter.eventually_atTop.mp
      filter_upwards [Filter.eventually_ge_atTop 0, hupper_event] with t ht hupper_t
      have hmono := hsm (hresA t ht) hzeroA
      have hinner : inner ℝ (x t - z) (horbit.residual t) ≤
          ‖x t - z‖ * ‖horbit.residual t‖ := real_inner_le_norm _ _
      have hmono' : rho * ‖x t - z‖ ^ 2 ≤ inner ℝ (x t - z) (horbit.residual t) := by
        simpa using hmono
      have hsquare : rho * ‖x t - z‖ ^ 2 ≤ ‖x t - z‖ * ‖horbit.residual t‖ :=
        le_trans hmono' hinner
      have hdistance : rho * ‖x t - z‖ ≤ ‖horbit.residual t‖ := by
        by_cases hzero : ‖x t - z‖ = 0
        · simp [hzero, norm_nonneg]
        · have hpos : 0 < ‖x t - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
          nlinarith
      have hbound : ‖x t - z‖ ≤ rho⁻¹ * ‖horbit.residual t‖ := by
        calc
          ‖x t - z‖ = rho⁻¹ * (rho * ‖x t - z‖) := by
            field_simp [hrho.ne']
          _ ≤ rho⁻¹ * ‖horbit.residual t‖ :=
            mul_le_mul_of_nonneg_left hdistance (by positivity)
      have hupper_lt : rho⁻¹ * ‖horbit.residual t‖ < ε := by
        have hnonneg : 0 ≤ rho⁻¹ * ‖horbit.residual t‖ :=
          mul_nonneg (le_of_lt (inv_pos.mpr hrho)) (norm_nonneg _)
        simpa [Real.dist_eq, abs_of_nonneg hnonneg, abs_of_pos hrho] using hupper_t
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using lt_of_le_of_lt hbound hupper_lt
    exact ⟨z, hz, tendsto_iff_norm_sub_tendsto_zero.mpr hnorm⟩
  · obtain ⟨C, hC⟩ := eventually_norm_le_of_tendsto_weakly_trajectory hxweak
    let R : ℝ := max 1 C
    let K : Set H := {y | ‖y‖ ≤ R ∧ (Phi y : EReal) ≤ (a : EReal)}
    have hK : IsCompact K := hinfcompact R a
    have hEventuallyK : ∀ᶠ t in atTop, x t ∈ K := by
      filter_upwards [hC, hPhiTail] with t htC htPhi
      exact ⟨le_trans htC (le_max_right _ _), htPhi⟩
    have hweakScalar : ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun t => ell (x t)) atTop (nhds (ell z)) := by
      intro ell
      let u : H := (InnerProductSpace.toDual ℝ H).symm ell
      have hu := (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H z) |>.comp hxweak
      have hrepr (y : H) : ell y = inner ℝ y u := by
        calc
          ell y = inner ℝ u y := (InnerProductSpace.toDual_symm_apply).symm
          _ = inner ℝ y u := real_inner_comm _ _
      simpa only [hrepr] using hu
    exact ⟨z, hz,
      strong_tendsto_of_eventually_compact_and_weak_scalar_convergence x z K hK hEventuallyK
        hweakScalar⟩

end AbbasDynamical2015
