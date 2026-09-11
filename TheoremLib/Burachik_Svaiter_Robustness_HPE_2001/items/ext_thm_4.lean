import Foundation.SetValued.Minty
import Foundation.Hilbert.WeakConvergence

namespace BurachikSvaiterRobustnessHPE2001

open Filter SetValuedOperator
open scoped InnerProductSpace Topology Pointwise

/-! The current Foundation branch keeps the resolvent wrapper in a module whose
    compatibility `.olean` is not available.  This local form is the only
    resolvent fact needed below, and follows directly from maximal monotonicity. -/
private theorem positive_scaled_maximal_monotone_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (hT : T.IsMaximalMonotone) {rho : ℝ} (hrho : 0 < rho) :
    SetValuedOperator.IsMaximalMonotone (fun x : H => rho • T x) := by
  let S : SetValuedOperator H H := fun x : H => rho • T x
  have hSmono : S.IsMonotone := by
    intro x y u hu v hv
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨b, hb, rfl⟩
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg hrho.le (hT.1 a ha b hb)
  refine ⟨hSmono, ?_⟩
  intro B hB hSB p hp
  rcases p with ⟨x, u⟩
  change u ∈ B x at hp
  let C : SetValuedOperator H H := fun z => rho⁻¹ • B z
  have hC : C.IsMonotone := by
    intro x y a ha b hb
    rcases ha with ⟨u, hu, rfl⟩
    rcases hb with ⟨v, hv, rfl⟩
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg (inv_pos.mpr hrho).le (hB u hu v hv)
  have hTC : T.graph ⊆ C.graph := by
    intro q hq
    rcases q with ⟨z, a⟩
    change a ∈ T z at hq
    change a ∈ C z
    refine ⟨rho • a, ?_, ?_⟩
    · exact (SetValuedOperator.mem_graph_iff B z (rho • a)).mp
        (hSB ((SetValuedOperator.mem_graph_iff S z (rho • a)).mpr ⟨a, hq, rfl⟩))
    · simp [smul_smul, inv_mul_cancel₀ hrho.ne']
  change u ∈ S x
  refine ⟨rho⁻¹ • u, ?_, ?_⟩
  · exact (SetValuedOperator.mem_graph_iff T x (rho⁻¹ • u)).mp
      (hT.2 C hC hTC ((SetValuedOperator.mem_graph_iff C x (rho⁻¹ • u)).mpr ⟨u, hp, rfl⟩))
  · simp [smul_smul, mul_inv_cancel₀ hrho.ne']

private theorem inner_tendsto_zero_of_tendsto_zero_of_bounded {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {a b : ℕ → H}
    (ha : Tendsto a atTop (nhds 0)) (hb : Bornology.IsBounded (Set.range b)) :
    Tendsto (fun n => inner ℝ (a n) (b n)) atTop (nhds 0) := by
  rcases isBounded_iff_forall_norm_le.mp hb with ⟨M, hM⟩
  have ha_norm : Tendsto (fun n => ‖a n‖) atTop (nhds 0) := by simpa using ha.norm
  have hprod : Tendsto (fun n => ‖a n‖ * M) atTop (nhds 0) := by
    simpa using ha_norm.mul_const M
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod
    (fun n => abs_nonneg _) ?_
  intro n
  calc
    |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left
      (hM _ (Set.mem_range_self n)) (norm_nonneg _)

/-- A maximal monotone operator with bounded domain is surjective. -/
theorem maximal_monotone_surjective_of_bounded_domain {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {U : SetValuedOperator H H}
    (hU : U.IsMaximalMonotone) (hdom : Bornology.IsBounded U.dom) :
    U.range = Set.univ ∧ U.zeros.Nonempty := by
  classical
  let c : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hc : ∀ n, 0 < c n := by
    intro n
    dsimp [c]
    positivity
  have hres : ∀ n : ℕ, ∀ p : H, ∃ x u : H, u ∈ U x ∧ x + c n • u = c n • p := by
    intro n p
    rcases minty_surjective_of_maximal_monotone
        (T := fun x : H => c n • U x) (positive_scaled_maximal_monotone_local hU (hc n)) (c n • p) with
      ⟨x, q, hq, heq⟩
    rcases hq with ⟨u, hu, rfl⟩
    exact ⟨x, u, hu, heq.symm⟩
  have hsurj : ∀ p : H, p ∈ U.range := by
    intro p
    choose x u hu hEq using fun n => hres n p
    have hxbounded : Bornology.IsBounded (Set.range x) := by
      apply Bornology.IsBounded.subset hdom
      rintro _ ⟨n, rfl⟩
      exact SetValuedOperator.mem_dom_iff U (x n) |>.2 ⟨u n, hu n⟩
    have hinv : Tendsto (fun n : ℕ => (c n)⁻¹) atTop (nhds 0) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have hadd : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 hnat
      exact tendsto_inv_atTop_zero.comp (by simpa [c] using hadd)
    have hcorr : Tendsto (fun n => (c n)⁻¹ • x n) atTop (nhds 0) := by
      rcases isBounded_iff_forall_norm_le.mp hxbounded with ⟨M, hM⟩
      have hbound (n : ℕ) : ‖(c n)⁻¹ • x n‖ ≤ (c n)⁻¹ * M := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hc n).le)]
        exact mul_le_mul_of_nonneg_left (hM _ (Set.mem_range_self n)) (inv_nonneg.mpr (hc n).le)
      have hright : Tendsto (fun n : ℕ => (c n)⁻¹ * M) atTop (nhds 0) := by
        simpa using hinv.mul_const M
      exact squeeze_zero_norm hbound hright
    have hu_formula (n : ℕ) : u n = p - (c n)⁻¹ • x n := by
      have hc0 : c n ≠ 0 := (hc n).ne'
      calc
        u n = (c n)⁻¹ • (c n • u n) := by simp [smul_smul, hc0]
        _ = (c n)⁻¹ • (c n • p - x n) := by rw [← hEq n]; abel
        _ = p - (c n)⁻¹ • x n := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hc0]
          simp
    have hu0 : Tendsto (fun n => u n - p) atTop (nhds 0) := by
      have : (fun n => u n - p) = fun n => -((c n)⁻¹ • x n) := by
        funext n
        rw [hu_formula]
        abel
      rw [this]
      simpa using hcorr.neg
    rcases bounded_sequence_has_weakly_convergent_subsequence x hxbounded with
      ⟨xbar, phi, hphi, hxweak⟩
    let xs : ℕ → H := fun k => x (phi k)
    let us : ℕ → H := fun k => u (phi k)
    have hus0 : Tendsto (fun k => us k - p) atTop (nhds 0) := by
      simpa [us] using hu0.comp hphi.tendsto_atTop
    have hxsbounded : Bornology.IsBounded (Set.range xs) := by
      apply Bornology.IsBounded.subset hxbounded
      rintro _ ⟨k, rfl⟩
      exact ⟨phi k, rfl⟩
    have hrel : ∀ z w, w ∈ U z → 0 ≤ inner ℝ (p - w) (xbar - z) := by
      intro z w hw
      have h1 : Tendsto (fun k => inner ℝ (us k - p) (xs k)) atTop (nhds 0) :=
        inner_tendsto_zero_of_tendsto_zero_of_bounded hus0 hxsbounded
      have h2 : Tendsto (fun k => inner ℝ (us k - p) z) atTop (nhds 0) := by
        simpa using hus0.inner tendsto_const_nhds
      have h3 : Tendsto (fun k => inner ℝ w (xs k)) atTop (nhds (inner ℝ w xbar)) := by
        have hcont := (weakSpace_continuous_inner_right w).tendsto (toWeakSpace ℝ H xbar)
        simpa [xs, real_inner_comm] using hcont.comp hxweak
      have hp : Tendsto (fun k => inner ℝ p (xs k)) atTop (nhds (inner ℝ p xbar)) := by
        have hcont := (weakSpace_continuous_inner_right p).tendsto (toWeakSpace ℝ H xbar)
        simpa [xs, real_inner_comm] using hcont.comp hxweak
      have hlim : Tendsto (fun k => inner ℝ (us k - w) (xs k - z)) atTop
          (nhds (inner ℝ (p - w) (xbar - z))) := by
        have hpz : Tendsto (fun _ : ℕ => inner ℝ p z) atTop (nhds (inner ℝ p z)) :=
          tendsto_const_nhds
        have hwz : Tendsto (fun _ : ℕ => inner ℝ w z) atTop (nhds (inner ℝ w z)) :=
          tendsto_const_nhds
        have hsum := ((((h1.add hp).sub h2).sub hpz).sub h3).add hwz
        have hexpand : (fun k => inner ℝ (us k - w) (xs k - z)) =
            (fun k => inner ℝ (us k - p) (xs k) + inner ℝ p (xs k) -
              inner ℝ (us k - p) z - inner ℝ p z - inner ℝ w (xs k) + inner ℝ w z) := by
          funext k
          simp [inner_sub_left, inner_sub_right]
          ring
        rw [hexpand]
        convert hsum using 1 <;> simp [inner_sub_left, inner_sub_right] <;> ring
      have hnonneg : ∀ k, 0 ≤ inner ℝ (us k - w) (xs k - z) := by
        intro k
        exact hU.1 (us k) (by simpa [us] using hu (phi k)) w hw
      exact isClosed_Ici.mem_of_tendsto hlim (Filter.Eventually.of_forall hnonneg)
    have hpU : p ∈ U xbar := mem_of_monotonically_related_to_graph (T := U) hU hrel
    exact SetValuedOperator.mem_range_iff U p |>.2 ⟨xbar, hpU⟩
  constructor
  · exact Set.eq_univ_of_forall hsurj
  · rcases SetValuedOperator.mem_range_iff U (0 : H) |>.1 (hsurj 0) with ⟨x, hx⟩
    exact ⟨x, SetValuedOperator.mem_zeros_iff U x |>.2 hx⟩

end BurachikSvaiterRobustnessHPE2001
