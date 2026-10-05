import TheoremLib.Dual_guided_2026.SDOTPopulationRemainder
import TheoremLib.Dual_guided_2026.SDOTLocalization

/-!
# Population semidual contrast and curvature

Subtracting the integrand at a fixed reference potential changes the
population semidual only by a constant. The contrast is bounded uniformly
in the source point, so its differentiation does not require an additional
cost-integrability assumption.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators Topology

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def semiDualContrastIntegrand (data : HELLOSDOTData X Ω)
    (gRef g : Fin data.n → ℝ) (x : X) : ℝ :=
  sInf (Set.range fun j => sdCost data x j - g j) -
    sInf (Set.range fun j => sdCost data x j - gRef j)

noncomputable def potentialFunctional (data : HELLOSDOTData X Ω)
    (v : Fin data.n → ℝ) : (Fin data.n → ℝ) →L[ℝ] ℝ :=
  ∑ j, v j • ContinuousLinearMap.proj j

theorem potentialFunctional_apply (data : HELLOSDOTData X Ω)
    (v g : Fin data.n → ℝ) : potentialFunctional data v g = ∑ j, v j * g j := by
  simp [potentialFunctional]

noncomputable def populationSemiDualContrast (data : HELLOSDOTData X Ω)
    (gRef g : Fin data.n → ℝ) : ℝ :=
  potentialFunctional data data.b (g - gRef) +
    ∫ x, semiDualContrastIntegrand data gRef g x ∂data.sourceMeasure

theorem measurable_semiDualContrastIntegrand (data : HELLOSDOTData X Ω)
    (gRef g : Fin data.n → ℝ) : Measurable (semiDualContrastIntegrand data gRef g) := by
  unfold semiDualContrastIntegrand
  apply Measurable.sub <;> apply Measurable.iInf <;> intro j <;> unfold sdCost <;> fun_prop

theorem semiDualContrastIntegrand_abs_le_norm (data : HELLOSDOTData X Ω)
    (gRef g : Fin data.n → ℝ) (x : X) :
    |semiDualContrastIntegrand data gRef g x| ≤ ‖g - gRef‖ :=
  semiDualMinimum_sub_abs_le_norm data x g gRef

theorem integrable_semiDualContrastIntegrand (data : HELLOSDOTData X Ω)
    (gRef g : Fin data.n → ℝ) :
    Integrable (semiDualContrastIntegrand data gRef g) data.sourceMeasure := by
  apply (integrable_const ‖g - gRef‖).mono'
    (measurable_semiDualContrastIntegrand data gRef g).aestronglyMeasurable
  filter_upwards [] with x
  exact semiDualContrastIntegrand_abs_le_norm data gRef g x

theorem populationSemiDualContrast_self (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : populationSemiDualContrast data g g = 0 := by
  simp [populationSemiDualContrast, semiDualContrastIntegrand]

theorem ae_strict_laguerreAssignment (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (g : Fin data.n → ℝ) :
    ∀ᵐ x ∂data.sourceMeasure, ∀ j, j ≠ laguerreAssignment data g x →
      sdCost data x (laguerreAssignment data g x) - g (laguerreAssignment data g x) <
        sdCost data x j - g j := by
  have hpairs : ∀ i j : Fin data.n, i ≠ j →
      ∀ᵐ x ∂data.sourceMeasure, sdCost data x i - g i ≠ sdCost data x j - g j := by
    intro i j hij
    apply ae_iff.mpr
    simpa only [not_not] using pairwise_boundary_null data hregular g hij
  have hfull : ∀ᵐ x ∂data.sourceMeasure, ∀ i j : Fin data.n, i ≠ j →
      sdCost data x i - g i ≠ sdCost data x j - g j := by
    simp only [ae_all_iff]
    exact hpairs
  filter_upwards [hfull] with x hx
  intro j hj
  exact lt_of_le_of_ne ((laguerreAssignment_mem data g x).1 j)
    (hx _ _ hj.symm)

noncomputable def semiDualSampleDerivative (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) : (Fin data.n → ℝ) →L[ℝ] ℝ :=
  ∑ j, cellIndicator data g j x • (-ContinuousLinearMap.proj j)

theorem semiDualSampleDerivative_eq_proj (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) :
    semiDualSampleDerivative data g x =
      -ContinuousLinearMap.proj (laguerreAssignment data g x) := by
  classical
  simp [semiDualSampleDerivative, cellIndicator_eq_assignment]

theorem measurable_semiDualSampleDerivative (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : Measurable (semiDualSampleDerivative data g) := by
  unfold semiDualSampleDerivative
  apply Finset.measurable_sum _
  intro j _
  unfold cellIndicator
  exact (measurable_const.indicator (measurableSet_laguerreCell data g j)).smul measurable_const

theorem hasFDerivAt_semiDualContrastIntegrand_of_strict (data : HELLOSDOTData X Ω)
    (gRef g : Fin data.n → ℝ) (x : X)
    (hstrict : ∀ j, j ≠ laguerreAssignment data g x →
      sdCost data x (laguerreAssignment data g x) - g (laguerreAssignment data g x) <
        sdCost data x j - g j) :
    HasFDerivAt (fun g' => semiDualContrastIntegrand data gRef g' x)
      (semiDualSampleDerivative data g x) g := by
  let a := laguerreAssignment data g x
  have hevent : ∀ᶠ g' in 𝓝 g, ∀ j, j ≠ a →
      sdCost data x a - g' a < sdCost data x j - g' j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = a
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · apply Filter.Eventually.mono ((isOpen_lt
        (show Continuous (fun g' : Fin data.n → ℝ => sdCost data x a - g' a) by fun_prop)
        (show Continuous (fun g' : Fin data.n → ℝ => sdCost data x j - g' j) by fun_prop)).mem_nhds
        (hstrict j hj))
      intro g' hg' _
      exact hg'
  have hEq : (fun g' => semiDualContrastIntegrand data gRef g' x) =ᶠ[𝓝 g]
      (fun g' => sdCost data x a - g' a -
        sInf (Set.range fun j => sdCost data x j - gRef j)) := by
    filter_upwards [hevent] with g' hg'
    unfold semiDualContrastIntegrand
    rw [semiDualMinimum_eq_active data g' x]
    intro j
    by_cases hj : j = a
    · rw [hj]
    · exact (hg' j hj).le
  rw [semiDualSampleDerivative_eq_proj]
  have hproj : HasFDerivAt (fun g' : Fin data.n → ℝ => g' a)
      (ContinuousLinearMap.proj a) g :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin data.n => ℝ) a).hasFDerivAt
  exact ((hproj.const_sub (sdCost data x a)).sub_const
    (sInf (Set.range fun j => sdCost data x j - gRef j))).congr_of_eventuallyEq hEq

theorem integral_semiDualSampleDerivative (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) :
    (∫ x, semiDualSampleDerivative data g x ∂data.sourceMeasure) =
      -potentialFunctional data (data.populationMarginal g) := by
  unfold semiDualSampleDerivative
  rw [integral_finset_sum Finset.univ (fun j _ =>
    ((memLp_cellIndicator data g j).integrable (by norm_num)).smul_const _)]
  simp_rw [integral_smul_const, integral_cellIndicator]
  simp only [smul_neg, potentialFunctional, Finset.sum_neg_distrib]

/-- Boundary anti-concentration makes the active score unique almost surely.
The uniform unit Lipschitz envelope permits differentiation under the integral. -/
theorem hasFDerivAt_populationSemiDualContrast (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (gRef g : Fin data.n → ℝ) :
    HasFDerivAt (populationSemiDualContrast data gRef)
      (potentialFunctional data (data.b - data.populationMarginal g)) g := by
  have hdiff : ∀ᵐ x ∂data.sourceMeasure,
      HasFDerivAt (fun g' => semiDualContrastIntegrand data gRef g' x)
        (semiDualSampleDerivative data g x) g := by
    filter_upwards [ae_strict_laguerreAssignment data hregular g] with x hx
    exact hasFDerivAt_semiDualContrastIntegrand_of_strict data gRef g x hx
  have hLip : ∀ᵐ x ∂data.sourceMeasure, ∀ g' ∈ (Set.univ : Set (Fin data.n → ℝ)),
      ‖semiDualContrastIntegrand data gRef g' x - semiDualContrastIntegrand data gRef g x‖ ≤
        (1 : ℝ) * ‖g' - g‖ := by
    filter_upwards [] with x
    intro g' _
    rw [Real.norm_eq_abs, one_mul]
    have hcancel : semiDualContrastIntegrand data gRef g' x -
        semiDualContrastIntegrand data gRef g x =
        sInf (Set.range fun j => sdCost data x j - g' j) -
          sInf (Set.range fun j => sdCost data x j - g j) := by
      unfold semiDualContrastIntegrand
      ring
    rw [hcancel]
    exact semiDualMinimum_sub_abs_le_norm data x g' g
  have hIntegral := (hasFDerivAt_integral_of_dominated_loc_of_lip'
    (𝕜 := ℝ) (s := Set.univ) (bound := fun _ : X => (1 : ℝ)) Filter.univ_mem
    (fun g' _ => (measurable_semiDualContrastIntegrand data gRef g').aestronglyMeasurable)
    (integrable_semiDualContrastIntegrand data gRef g)
    (measurable_semiDualSampleDerivative data g).aestronglyMeasurable hLip
    (integrable_const 1) hdiff).2
  rw [integral_semiDualSampleDerivative] at hIntegral
  have hlinear : HasFDerivAt (fun g' => potentialFunctional data data.b (g' - gRef))
      (potentialFunctional data data.b) g := by
    simpa only [map_sub] using
      ((potentialFunctional data data.b).hasFDerivAt (x := g)).sub_const
        (potentialFunctional data data.b gRef)
  have htotal := hlinear.add hIntegral
  change HasFDerivAt (populationSemiDualContrast data gRef)
    (potentialFunctional data data.b + -potentialFunctional data (data.populationMarginal g)) g
    at htotal
  convert htotal using 1
  ext u
  simp only [potentialFunctional_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem pi_norm_sq_le_sum_sq (data : HELLOSDOTData X Ω) (u : Fin data.n → ℝ) :
    ‖u‖ ^ 2 ≤ ∑ j, (u j) ^ 2 := by
  have hs : 0 ≤ ∑ j, (u j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnorm : ‖u‖ ≤ Real.sqrt (∑ j, (u j) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
    rw [sq_abs, Real.sq_sqrt hs]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (u k)) (Finset.mem_univ j)
  simpa only [Real.sq_sqrt hs] using
    (sq_le_sq₀ (norm_nonneg u) (Real.sqrt_nonneg _)).2 hnorm

theorem potential_pairing_le_norm (data : HELLOSDOTData X Ω)
    (u v : Fin data.n → ℝ) : ∑ j, u j * v j ≤ (data.n : ℝ) * ‖u‖ * ‖v‖ := by
  calc
    ∑ j, u j * v j ≤ ∑ j, |u j| * |v j| :=
      Finset.sum_le_sum fun j _ => by simpa only [abs_mul] using le_abs_self (u j * v j)
    _ ≤ ∑ _j : Fin data.n, ‖u‖ * ‖v‖ :=
      Finset.sum_le_sum fun j _ => mul_le_mul
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u j)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- Positive curvature at the balanced potential and its first-order Taylor
expansion give a positive radial pairing throughout a fixed neighborhood. -/
theorem populationMarginal_local_pairing_lower_bound (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    (hJ : HasFDerivAt data.populationMarginal J gStar) {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    ∃ r : ℝ, 0 < r ∧ ∀ u, IsBGaugeDirection data u → ‖u‖ ≤ r →
      (lambda / 2) * (∑ j, (u j) ^ 2) ≤
        ∑ j, u j * (data.populationMarginal (gStar + u) j - data.b j) := by
  let η := lambda / (2 * ((data.n : ℝ) + 1))
  have hn : (0 : ℝ) ≤ data.n := Nat.cast_nonneg _
  have hη : 0 < η := div_pos hlambda (by positivity)
  have hηeq : η * (2 * ((data.n : ℝ) + 1)) = lambda :=
    div_mul_cancel₀ _ (by positivity)
  have hcoeff : (data.n : ℝ) * η ≤ lambda / 2 := by nlinarith
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.1 (hJ.isLittleO.bound hη)
  refine ⟨s / 2, half_pos hs, ?_⟩
  intro u hu hnorm
  let v := populationLinearizationRemainder data gStar J (gStar + u)
  have hv : ‖v‖ ≤ η * ‖u‖ := by
    have hnear : dist (gStar + u) gStar < s := by
      simp only [dist_eq_norm, add_sub_cancel_left]
      linarith
    simpa only [v, populationLinearizationRemainder, add_sub_cancel_left] using hball hnear
  have hnegative := potential_pairing_le_norm data u (-v)
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, norm_neg] at hnegative
  have hnegative' : -(∑ j, u j * v j) ≤
      ((data.n : ℝ) * η) * ‖u‖ ^ 2 := by
    calc
      -(∑ j, u j * v j) ≤ (data.n : ℝ) * ‖u‖ * ‖v‖ := hnegative
      _ ≤ (data.n : ℝ) * ‖u‖ * (η * ‖u‖) :=
        mul_le_mul_of_nonneg_left hv (mul_nonneg hn (norm_nonneg _))
      _ = _ := by ring
  have herror : -(∑ j, u j * v j) ≤ (lambda / 2) * ∑ j, (u j) ^ 2 := by
    calc
      -(∑ j, u j * v j) ≤ ((data.n : ℝ) * η) * ‖u‖ ^ 2 := hnegative'
      _ ≤ (lambda / 2) * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ ≤ (lambda / 2) * ∑ j, (u j) ^ 2 :=
        mul_le_mul_of_nonneg_left (pi_norm_sq_le_sum_sq data u) (by positivity)
  have hsum : (∑ j, u j * (data.populationMarginal (gStar + u) j - data.b j)) =
      (∑ j, u j * (J u) j) + ∑ j, u j * v j := by
    simp only [v, populationLinearizationRemainder, Pi.sub_apply, hbalanced,
      add_sub_cancel_left]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  nlinarith [hcurvature u hu]

/-- Lemma F.8: along each gauge direction, the population objective loses at
least one quarter of the curvature times the squared Euclidean displacement. -/
theorem populationSemiDualContrast_local_margin (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    (hJ : HasFDerivAt data.populationMarginal J gStar) {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    ∃ r : ℝ, 0 < r ∧ ∀ u, IsBGaugeDirection data u → ‖u‖ ≤ r →
      populationSemiDualContrast data gStar (gStar + u) ≤
        -(lambda / 4) * (∑ j, (u j) ^ 2) := by
  obtain ⟨r, hr, hpair⟩ :=
    populationMarginal_local_pairing_lower_bound data gStar J hbalanced hJ hlambda hcurvature
  refine ⟨r, hr, ?_⟩
  intro u hu hnorm
  let F : ℝ → ℝ := fun t => populationSemiDualContrast data gStar (gStar + t • u)
  let D : ℝ → ℝ := fun t => potentialFunctional data
    (data.b - data.populationMarginal (gStar + t • u)) u
  let S := ∑ j, (u j) ^ 2
  let B : ℝ → ℝ := fun t => -(lambda / 4) * S * t ^ 2
  let B' : ℝ → ℝ := fun t => -(lambda / 2) * S * t
  have hF (t : ℝ) : HasDerivAt F (D t) t := by
    have hpath : HasDerivAt (fun s : ℝ => gStar + s • u) u t := by
      simpa only [one_smul] using ((hasDerivAt_id t).smul_const u).const_add gStar
    exact (hasFDerivAt_populationSemiDualContrast data hregular gStar
      (gStar + t • u)).comp_hasDerivAt t hpath
  have hB (t : ℝ) : HasDerivAt B (B' t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (-(lambda / 4) * S) using 1
    simp only [B', id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring
  have hderbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, D t ≤ B' t := by
    intro t ht
    have htgauge : IsBGaugeDirection data (t • u) := by
      unfold IsBGaugeDirection at hu ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm (data.b _) t, ← Finset.mul_sum, hu, mul_zero]
    have htnear : ‖t • u‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc
        t * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
        _ ≤ r := by simpa only [one_mul] using hnorm
    have hlocal := hpair (t • u) htgauge htnear
    have hsquare : (∑ j, ((t • u) j) ^ 2) = t ^ 2 * S := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, S, Finset.mul_sum]
    have hpairing : (∑ j, (t • u) j *
        (data.populationMarginal (gStar + t • u) j - data.b j)) = -(t * D t) := by
      simp only [Pi.smul_apply, smul_eq_mul, D, potentialFunctional_apply, Pi.sub_apply,
        Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsquare, hpairing] at hlocal
    by_cases htzero : t = 0
    · simp only [D, B', htzero, zero_smul, add_zero, hbalanced, sub_self]
      simp [potentialFunctional]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      dsimp only [B']
      nlinarith
  have hcompare := image_le_of_deriv_right_le_deriv_boundary
    (show ContinuousOn F (Set.Icc 0 1) from
      (continuous_iff_continuousAt.2 fun t => (hF t).continuousAt).continuousOn)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B, populationSemiDualContrast_self])
    (show ContinuousOn B (Set.Icc 0 1) from
      (continuous_iff_continuousAt.2 fun t => (hB t).continuousAt).continuousOn)
    (fun t _ => (hB t).hasDerivWithinAt) hderbound
  simpa only [F, B, S, one_smul, one_pow, mul_one] using
    hcompare (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)

theorem populationSemiDualContrast_local_norm_margin (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    (hJ : HasFDerivAt data.populationMarginal J gStar) {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    ∃ r : ℝ, 0 < r ∧ ∀ u, IsBGaugeDirection data u → ‖u‖ ≤ r →
      populationSemiDualContrast data gStar (gStar + u) ≤ -(lambda / 4) * ‖u‖ ^ 2 := by
  obtain ⟨r, hr, hmargin⟩ :=
    populationSemiDualContrast_local_margin data hregular gStar J hbalanced hJ hlambda hcurvature
  refine ⟨r, hr, fun u hu hnorm => ?_⟩
  exact (hmargin u hu hnorm).trans (mul_le_mul_of_nonpos_left
    (pi_norm_sq_le_sum_sq data u) (by linarith))

end DualGuided2026
