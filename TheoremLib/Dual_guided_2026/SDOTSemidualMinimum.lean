import TheoremLib.Dual_guided_2026.SDOTLocalization

/-!
# Continuity of the single-source semidual minimum

The target index set is finite, so the minimum of the continuously varying
scores is jointly continuous in the potential and source point.
-/

namespace DualGuided2026

open MeasureTheory
open scoped ENNReal

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem continuous_jointSemiDualMinimum (data : HELLOSDOTData X Ω) :
    Continuous (fun z : (Fin data.n → ℝ) × X =>
      sInf (Set.range fun j => sdCost data z.2 j - z.1 j)) := by
  let f : ((Fin data.n → ℝ) × X) → Fin data.n → ℝ :=
    fun z j => sdCost data z.2 j - z.1 j
  have hf : Continuous ↿f := by
    apply continuous_prod_of_discrete_right.mpr
    intro j
    change Continuous (fun z : (Fin data.n → ℝ) × X =>
      ‖z.2 - data.targetSites j‖ ^ 2 - z.1 j)
    fun_prop
  have h := (isCompact_univ : IsCompact (Set.univ : Set (Fin data.n))).continuous_sInf hf
  simpa only [f, Set.image_univ] using h

theorem measurable_jointSemiDualMinimum (data : HELLOSDOTData X Ω) :
    Measurable (fun z : (Fin data.n → ℝ) × X =>
      sInf (Set.range fun j => sdCost data z.2 j - z.1 j)) :=
  (continuous_jointSemiDualMinimum data).measurable

theorem measurable_semiDualMinimum (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) :
    Measurable (fun x : X => sInf (Set.range fun j => sdCost data x j - g j)) := by
  have hc : Continuous (fun x : X => (g, x)) := continuous_const.prodMk continuous_id
  have h := Continuous.comp (continuous_jointSemiDualMinimum data) hc
  exact h.measurable

theorem memLp_semiDualContrast (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (q : ℝ≥0∞) :
    MemLp (fun x : X => sInf (Set.range fun j => sdCost data x j - g j) -
      sInf (Set.range fun j => sdCost data x j - h j)) q data.sourceMeasure := by
  apply (memLp_const ‖g - h‖).of_le
  · exact ((measurable_semiDualMinimum data g).sub
      (measurable_semiDualMinimum data h)).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      semiDualMinimum_sub_abs_le_norm data x g h

end DualGuided2026
