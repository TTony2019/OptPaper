import Mathlib

namespace AttouchPeypouquetRedont2014

theorem eventually_lt_of_contract_recurrence
    (p : ℕ → ℝ) (η q : ℝ) (N : ℕ)
    (hη_nonneg : 0 ≤ η) (hη_lt_one : η < 1) (hq_pos : 0 < q)
    (hrecq : ∀ k ≥ N, p (k + 1) ≤ η * p k + q) :
    ∀ r : ℝ, q / (1 - η) < r → ∀ᶠ n in Filter.atTop, p n < r := by
  intro r hr
  have hgap_pos : 0 < 1 - η := sub_pos.mpr hη_lt_one
  have hgap_ne : 1 - η ≠ 0 := ne_of_gt hgap_pos
  let B : ℝ := max (p N) 0
  have hpN_le_B : p N ≤ B := le_max_left _ _
  have hB_nonneg : 0 ≤ B := le_max_right _ _
  have hquot_pos : 0 < q / (1 - η) := div_pos hq_pos hgap_pos
  have hgeom : η * (q / (1 - η)) + q = q / (1 - η) := by
    field_simp [hgap_ne]
    ring
  have hbound : ∀ t : ℕ, p (N + t) ≤ B * η ^ t + q / (1 - η) := by
    intro t
    induction t with
    | zero =>
        simp only [add_zero, pow_zero, mul_one]
        linarith
    | succ t iht =>
        have hrec := hrecq (N + t) (Nat.le_add_right N t)
        rw [show N + Nat.succ t = (N + t) + 1 by omega]
        calc
          p ((N + t) + 1) ≤ η * p (N + t) + q := hrec
          _ ≤ η * (B * η ^ t + q / (1 - η)) + q :=
            by linarith [mul_le_mul_of_nonneg_left iht hη_nonneg]
          _ = B * η ^ Nat.succ t + q / (1 - η) := by
            rw [pow_succ]
            calc
              η * (B * η ^ t + q / (1 - η)) + q
                  = B * (η ^ t * η) + (η * (q / (1 - η)) + q) := by ring
              _ = B * (η ^ t * η) + q / (1 - η) := by rw [hgeom]
  
  have hdiff_pos : 0 < r - q / (1 - η) := sub_pos.mpr hr
  have hlim : Filter.Tendsto (fun t : ℕ => B * η ^ t) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hη_nonneg hη_lt_one).const_mul B
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hlim.eventually_lt_const hdiff_pos)
  refine Filter.eventually_atTop.2 ⟨N + T, ?_⟩
  intro n hn
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hTt : T ≤ T + t := Nat.le_add_right T t
  have ht := hT (T + t) hTt
  have hb : p (N + T + t) ≤ B * η ^ (T + t) + q / (1 - η) := by
    simpa [Nat.add_assoc] using hbound (T + t)
  linarith

theorem limsup_le_zero_of_eventually_lt_pos (p : ℕ → ℝ)
    (hp : ∀ y : ℝ, 0 < y → ∀ᶠ n in Filter.atTop, p n < y) :
    Filter.limsup p Filter.atTop ≤ 0 := by
  rw [Filter.limsup_eq]
  let S : Set ℝ := {a | ∀ᶠ n in Filter.atTop, p n ≤ a}
  change sInf S ≤ 0
  by_cases hS : BddBelow S
  · by_contra h
    have hpos : 0 < sInf S := lt_of_not_ge h
    have hmem : sInf S / 2 ∈ S := by
      exact (hp (sInf S / 2) (by linarith)).mono fun _ hn => hn.le
    have hle : sInf S ≤ sInf S / 2 := csInf_le hS hmem
    linarith
  · rw [csInf_of_not_bddBelow hS]
    norm_num

/-- Lemma 13: a contractive recurrence with asymptotically nonpositive error. -/
theorem lemma13 (p ε : ℕ → ℝ) (η : ℝ) (k₀ : ℕ)
    (hη : 0 < η ∧ η < 1)
    (hε : Filter.limsup ε Filter.atTop ≤ 0)
    (hε_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop ε)
    (hrec : ∀ k ≥ k₀, p (k + 1) ≤ η * p k + ε k) :
    Filter.limsup p Filter.atTop ≤ 0 := by
  rcases hη with ⟨hη_pos, hη_lt_one⟩
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hgap_pos : 0 < 1 - η := sub_pos.mpr hη_lt_one
  have hgap_ne : 1 - η ≠ 0 := ne_of_gt hgap_pos
  apply limsup_le_zero_of_eventually_lt_pos p
  intro y hy
  let q : ℝ := y * (1 - η) / 2
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hε_eventual : ∀ᶠ k in Filter.atTop, ε k ≤ q := by
    filter_upwards [Filter.eventually_lt_add_pos_of_limsup_le
      (u := ε) hε_bdd hε hq_pos] with k hk
    simpa using hk.le
  obtain ⟨Kε, hε_tail⟩ := Filter.eventually_atTop.1 hε_eventual
  let N : ℕ := max k₀ Kε
  have hrecq : ∀ k ≥ N, p (k + 1) ≤ η * p k + q := by
    intro k hk
    have hk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
    have hkε : Kε ≤ k := le_trans (le_max_right _ _) hk
    calc
      p (k + 1) ≤ η * p k + ε k := hrec k hk₀
      _ ≤ η * p k + q := by linarith [hε_tail k hkε]
  have hq_div_lt_y : q / (1 - η) < y := by
    have hq_div_eq : q / (1 - η) = y / 2 := by
      dsimp [q]
      field_simp [hgap_ne]
    rw [hq_div_eq]
    linarith
  exact eventually_lt_of_contract_recurrence p η q N hη_nonneg hη_lt_one hq_pos hrecq y hq_div_lt_y

end AttouchPeypouquetRedont2014
