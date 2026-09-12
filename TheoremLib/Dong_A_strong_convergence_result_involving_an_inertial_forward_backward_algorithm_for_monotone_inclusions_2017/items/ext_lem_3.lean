import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_1
import Foundation.FixedPoint.Algorithms

/-! Browder's demiclosedness lemma. -/

open Filter Function Set
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Browder's demiclosedness lemma for a nonempty closed convex subset of a Hilbert space. -/
theorem browder_demiclosedness_lemma
    {C : Set H} (_hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : H → H} (_hT_maps : MapsTo T C C)
    (hT : ∀ a ∈ C, ∀ b ∈ C, ‖T a - T b‖ ≤ ‖a - b‖)
    (_hfixed : (fixedPointSetOn C T).Nonempty) {xSeq : ℕ → H} (hxSeq : ∀ n, xSeq n ∈ C)
    {x y : H}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (nhds (toWeakSpace ℝ H x)))
    (hy : Tendsto (fun n ↦ xSeq n - T (xSeq n)) atTop (nhds y)) :
    x - T x = y ∧ (y = 0 → x ∈ fixedPointSetOn C T) := by
  have hweak_closed : IsSeqClosed ((toWeakSpace ℝ H) '' C) :=
    ((isClosed_iff_weak_image_isClosed_of_convex hC_convex).mp hC_closed).isSeqClosed
  have hT_lipschitz : LipschitzOnWith 1 T C :=
    isNonexpansiveOn_restrict_iff_lipschitzOnWith_one.mp hT
  have hresidual : x - T x = y :=
    browder_demiclosedness_principle hweak_closed hT_lipschitz hxSeq hx hy
  constructor
  · exact hresidual
  · intro hy_zero
    rw [mem_fixedPointSetOn_iff]
    refine ⟨mem_of_tendsto_weakly_of_isClosed_convex hC_closed hC_convex hxSeq hx, ?_⟩
    exact (sub_eq_zero.mp (hresidual.trans hy_zero)).symm
