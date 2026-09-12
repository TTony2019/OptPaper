import Mathlib
import Foundation.Analysis.Semicontinuity
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_3

namespace BotCsetnek2015

/-- Proper lower semicontinuous coercive functions attain a finite infimum. -/
theorem exists_minimizer_of_proper_lsc_coercive {m : Nat}
    (g : EuclideanSpace m -> EReal)
    (hproper : ERealFunction.IsProper g)
    (hlsc : LowerSemicontinuous g)
    (hcoercive : CoerciveEReal g) :
    (∃ r : Real, sInf (Set.range g) = (r : EReal)) ∧
      ∃ x : EuclideanSpace m, IsMinOn g Set.univ x ∧ g x = sInf (Set.range g) := by
  rcases hproper with ⟨hg_ne_bot, x0, hx0_dom⟩
  have hx0_lt_top : g x0 < ⊤ := hx0_dom
  have hx0_ne_top : g x0 ≠ ⊤ := ne_of_lt hx0_lt_top
  have hx0_eff : x0 ∈ ERealFunction.effectiveDom g := by
    rw [ERealFunction.mem_effectiveDom_iff]
    exact ⟨hx0_ne_top, hg_ne_bot x0⟩
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real g x0).mp hx0_eff with ⟨c0, hc0⟩
  let C : Set (EuclideanSpace m) := ERealFunction.lowerLevelSet g c0
  have hx0C : x0 ∈ C := by
    simp [C, ERealFunction.lowerLevelSet, hc0]
  have hC_bounded : Bornology.IsBounded C := hcoercive c0
  have hC_closed : IsClosed C := by
    have hclosed :=
      (ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet g).mp hlsc c0
    simpa [C, ERealFunction.lowerLevelSet] using hclosed
  have hC_compact : IsCompact C := by
    exact (Metric.isCompact_iff_isClosed_bounded).2 ⟨hC_closed, hC_bounded⟩
  have hC_dom : (C ∩ {x | g x < ⊤}).Nonempty := by
    exact ⟨x0, hx0C, hx0_lt_top⟩
  rcases ERealFunction.lowerSemicontinuous_exists_isMinOn_of_isCompact hlsc hC_compact hC_dom with
    ⟨xmin, hxminC, hxmin_minC⟩
  have hxmin_le_c0 : g xmin ≤ (c0 : EReal) := hxminC
  have hxmin_min_univ : IsMinOn g Set.univ xmin := by
    intro y hy
    by_cases hyC : y ∈ C
    · exact hxmin_minC hyC
    · have hnot_le : ¬ g y ≤ (c0 : EReal) := by
        simpa [C, ERealFunction.lowerLevelSet] using hyC
      exact le_trans hxmin_le_c0 (le_of_lt (lt_of_not_ge hnot_le))
  have hxmin_ne_top : g xmin ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hxmin_le_c0
  have hxmin_eff : xmin ∈ ERealFunction.effectiveDom g := by
    rw [ERealFunction.mem_effectiveDom_iff]
    exact ⟨hxmin_ne_top, hg_ne_bot xmin⟩
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real g xmin).mp hxmin_eff with
    ⟨cmin, hcmin⟩
  have hxmin_eq_inf : g xmin = sInf (Set.range g) := by
    simpa using
      (ERealFunction.eq_sInf_image_of_isMinOn (f := g) (C := Set.univ)
        (x := xmin) trivial hxmin_min_univ)
  constructor
  · exact ⟨cmin, by rw [← hxmin_eq_inf, hcmin]⟩
  · exact ⟨xmin, hxmin_min_univ, hxmin_eq_inf⟩

end BotCsetnek2015
