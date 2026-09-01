import Mathlib

/-!
# Real sequences

Discrete analysis for real-indexed sequences: asymptotic `O`/`o` notation at
infinity, the discrete Gronwall inequality, and summability criteria.  All
declarations here are promoted from paper-local items (see the `/-! Source
item: ... -/` notes below).
-/

/-! Source item:
`TheoremLib/Attouch_Chbani_Riahi_Fast_proximal_methods_via_time_scaling_of_damped_inertial_dynamics_2019_correction/items/ext_def_4` -/

/-- Big-O at infinity for real sequences: `a` is eventually bounded by a constant
multiple of the positive comparison sequence `r`. -/
def IsBigOAtTop (a r : ℕ → ℝ) : Prop :=
  (∀ k, 0 < r k) ∧ ∃ C > 0, ∃ K, ∀ k ≥ K, |a k| ≤ C * r k

/-- Little-o at infinity for real sequences with a positive comparison sequence:
`a / r` tends to zero at infinity. -/
def IsLittleOAtTop (a r : ℕ → ℝ) : Prop :=
  (∀ k, 0 < r k) ∧ ∀ ε > 0, ∃ K, ∀ k ≥ K, |a k| ≤ ε * r k

/-! Source item:
`TheoremLib/Attouch_Chbani_Riahi_Fast_proximal_methods_via_time_scaling_of_damped_inertial_dynamics_2019_correction/items/ext_lem_1`
(Lemma A.4; externally cited from Attouch--Chbani--Peypouquet--Redont 2018). -/

/-- Discrete Gronwall inequality (Lemma A.4): if a nonnegative sequence `a` satisfies
`a k ^ 2 ≤ c ^ 2 + ∑ j ≤ k, b j * a j` for a summable nonnegative sequence `b`, then
`a k ≤ c + ∑' j, b j` for all `k`. -/
theorem discrete_gronwall_A4 (a b : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hs : Summable b)
    (hrec : ∀ k, a k ^ 2 ≤ c ^ 2 + ∑ j ∈ Finset.Icc 1 k, b j * a j) :
    ∀ k, a k ≤ c + ∑' j, b j := by
  set B : ℝ := ∑' j, b j
  set A : ℝ := c + B
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using (tsum_nonneg hb)
  have hA_nonneg : 0 ≤ A := add_nonneg hc hB_nonneg
  have hc_le_A : c ≤ A := by
    dsimp [A]
    linarith
  have hfin_le_B (s : Finset ℕ) : (∑ j ∈ s, b j) ≤ B := by
    simpa [B] using hs.sum_le_tsum s (fun j _ => hb j)
  have hbound : ∀ k, a k ≤ A := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih
    by_contra hnot
    have hA_lt_ak : A < a k := lt_of_not_ge hnot
    have hc_le_ak : c ≤ a k := le_trans hc_le_A hA_lt_ak.le
    have hak_nonneg : 0 ≤ a k := ha k
    have hsum_le : (∑ j ∈ Finset.Icc 1 k, b j * a j) ≤ B * a k := by
      calc
        ∑ j ∈ Finset.Icc 1 k, b j * a j ≤
            ∑ j ∈ Finset.Icc 1 k, b j * a k := by
              refine Finset.sum_le_sum fun j hj => ?_
              rcases Finset.mem_Icc.mp hj with ⟨_, hjk⟩
              rcases Nat.lt_or_eq_of_le hjk with hjk | rfl
              · exact mul_le_mul_of_nonneg_left
                  (le_of_lt ((ih j hjk).trans_lt hA_lt_ak)) (hb j)
              · exact le_rfl
        _ = (∑ j ∈ Finset.Icc 1 k, b j) * a k := by
              rw [Finset.sum_mul]
        _ ≤ B * a k := mul_le_mul_of_nonneg_right
              (hfin_le_B (Finset.Icc 1 k)) hak_nonneg
    have hsq_le : a k ^ 2 ≤ A * a k := by
      calc
        a k ^ 2 ≤ c ^ 2 + ∑ j ∈ Finset.Icc 1 k, b j * a j := hrec k
        _ ≤ c ^ 2 + B * a k := add_le_add_right hsum_le _
        _ ≤ c * a k + B * a k := by
              rw [pow_two]
              exact add_le_add_left (mul_le_mul_of_nonneg_left hc_le_ak hc) _
        _ = A * a k := by
              dsimp [A]
              ring
    have hak_pos : 0 < a k := lt_of_le_of_lt hA_nonneg hA_lt_ak
    have hstrict : A * a k < a k ^ 2 := by
      rw [pow_two]
      exact mul_lt_mul_of_pos_right hA_lt_ak hak_pos
    exact (not_lt_of_ge hsq_le) hstrict
  simpa [A, B] using hbound

/-! Source item:
`TheoremLib/Attouch_Adly_Le_Threshold_dry_friction_2023/items/rem_1`
(Remark 4.1: weighted summability of the perturbations). -/

/-- Weighted summability `∑ k‖e_k‖ < ∞` of the perturbation sequence forces it to
vanish: `‖e_k‖ → 0`.  Standard tool for perturbed-algorithm analyses. -/
theorem summable_weighted_norm_tendsto_zero {H : Type*} [NormedAddCommGroup H]
    (e : ℕ → H) :
    Summable (fun k : ℕ => (k : ℝ) * ‖e k‖) →
      Filter.Tendsto (fun k => ‖e k‖) Filter.atTop (nhds 0) := by
  intro hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hs.tendsto_atTop_zero ?_ ?_
  · filter_upwards with k
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hk
    simpa using mul_le_mul_of_nonneg_right hk' (norm_nonneg (e k))

/-! Source item:
`TheoremLib/Attouch_Balhag_Chbani_Riahi_Tikhonov_Inertial_Dynamics_2022/items/lem_1`
(Lemma 1, Attouch--Balhag--Chbani--Riahi 2022). -/

/-- If the squared norm of `u` tends to zero along a filter `l`, then `u` itself
tends to zero along `l`.  Generic analysis fact used in the proof of Lemma 1 of
Attouch--Balhag--Chbani--Riahi 2022. -/
theorem tendsto_norm_of_sq_tendsto_zero {α H : Type*} [NormedAddCommGroup H]
    {l : Filter α} {u : α → H}
    (h : Filter.Tendsto (fun a => ‖u a‖ ^ 2) l (nhds 0)) :
    Filter.Tendsto u l (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.tendsto 0 |>.comp h
  have hsqrt' : Filter.Tendsto (fun a => √(‖u a‖ ^ 2)) l (nhds 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero] using hsqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt'
