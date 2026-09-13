import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.thm_9
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_4
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

namespace LorenzPock

private theorem finite_weighted_cauchy_schwarz {ι : Type*} [Fintype ι]
    (u v z : ι → ℝ) (hu : ∀ t, 0 ≤ u t) (hv : ∀ t, 0 ≤ v t)
    (hz : ∀ t, (z t) ^ 2 = u t * v t) :
    (∑ t, z t) ^ 2 ≤ (∑ t, u t) * ∑ t, v t := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun t _ => hu t) (fun t _ => hv t) (fun t _ => hz t)

/-- The power convention of Lemma 10: `0 ^ 0 = 0`, the usual real power otherwise.  The
paper states the entries (35) "using the convention that `0^0 = 0`", so that a zero entry of
`K` contributes `0` rather than `1` at the exponents `s = 0` and `s = 2`. -/
private noncomputable def paperPow (t p : ℝ) : ℝ := if t = 0 then 0 else t ^ p

private theorem paperPow_of_ne {t p : ℝ} (ht : t ≠ 0) : paperPow t p = t ^ p := by
  simp [paperPow, ht]

private theorem paperPow_nonneg {t p : ℝ} (ht : 0 ≤ t) : 0 ≤ paperPow t p := by
  by_cases h : t = 0
  · simp [paperPow, h]
  · rw [paperPow_of_ne h]
    exact Real.rpow_nonneg ht p

private theorem paperPow_split_abs_two (z s : ℝ) :
    paperPow |z| s * paperPow |z| (2 - s) = z ^ 2 := by
  by_cases hz : z = 0
  · subst z
    simp [paperPow]
  · have habs : 0 < |z| := abs_pos.mpr hz
    have hne : |z| ≠ 0 := ne_of_gt habs
    rw [paperPow_of_ne hne, paperPow_of_ne hne, ← Real.rpow_add habs]
    norm_num

private theorem inertial_scalar_bound (γ δ ε a : ℝ)
    (hγ : 0 < γ ∧ γ < 2) (hδ : 0 < δ ∧ δ < 2)
    (hε : 0 < ε ∧ ε < (9 - 4 * max γ δ) / (2 * max γ δ))
    (ha : 0 ≤ a ∧ a ≤
      1 + (Real.sqrt (9 - 4 * max γ δ - 2 * ε * max γ δ) - 3) / max γ δ) :
    (1 - a) ^ 2 / 2 ≤ (1 - 3 * a - ε) / γ ∧
      (1 - a) ^ 2 / 2 ≤ (1 - 3 * a - ε) / δ := by
  let L : ℝ := max γ δ
  have hLpos : 0 < L := lt_of_lt_of_le hγ.1 (le_max_left _ _)
  have hLlt : L < 2 := max_lt hγ.2 hδ.2
  have hγL : γ ≤ L := le_max_left _ _
  have hδL : δ ≤ L := le_max_right _ _
  have hrad : 0 ≤ 9 - 4 * L - 2 * ε * L := by
    have := (lt_div_iff₀ (show 0 < 2 * L by positivity)).mp hε.2
    dsimp [L] at this ⊢
    nlinarith
  have hsq : (Real.sqrt (9 - 4 * L - 2 * ε * L)) ^ 2 =
      9 - 4 * L - 2 * ε * L := Real.sq_sqrt hrad
  have hupper : L * a ≤ L - 3 + Real.sqrt (9 - 4 * L - 2 * ε * L) := by
    have h' : a ≤ (L - 3 + Real.sqrt (9 - 4 * L - 2 * ε * L)) / L := by
      rw [show (L - 3 + Real.sqrt (9 - 4 * L - 2 * ε * L)) / L =
        1 + (Real.sqrt (9 - 4 * L - 2 * ε * L) - 3) / L by
          field_simp [hLpos.ne']
          ring]
      simpa [L] using ha.2
    simpa [mul_comm] using (le_div_iff₀ hLpos).mp h'
  have hlower : L - 3 - Real.sqrt (9 - 4 * L - 2 * ε * L) ≤ L * a := by
    have hroot := Real.sqrt_nonneg (9 - 4 * L - 2 * ε * L)
    nlinarith [ha.1]
  have hproduct :
      (L * a - (L - 3 - Real.sqrt (9 - 4 * L - 2 * ε * L))) *
        (L * a - (L - 3 + Real.sqrt (9 - 4 * L - 2 * ε * L))) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlower) (sub_nonpos.mpr hupper)
  have hmain : L * (1 - a) ^ 2 ≤ 2 * (1 - 3 * a - ε) := by
    nlinarith
  have hc : 0 ≤ 1 - 3 * a - ε := by nlinarith
  have hbase : (1 - a) ^ 2 / 2 ≤ (1 - 3 * a - ε) / L := by
    apply (div_le_div_iff₀ (by norm_num) hLpos).mpr
    nlinarith
  exact ⟨hbase.trans (div_le_div_of_nonneg_left hc hγ.1 hγL),
    hbase.trans (div_le_div_of_nonneg_left hc hδ.1 hδL)⟩

/-- Lemma 10 diagonal preconditioners, with entries prescribed by (35), satisfy
the positivity and normalized operator-norm conditions (36)--(37). -/
theorem diagonal_preconditioner_bound (m n : ℕ) (K : Matrix (Fin m) (Fin n) ℝ)
    (D : Fin n → ℝ) (E : Fin m → ℝ) (γ δ r s : ℝ)
    (hγ : 0 < γ ∧ γ < 2) (hδ : 0 < δ ∧ δ < 2)
    (hr : 0 < r) (hs : 0 ≤ s ∧ s ≤ 2)
    (hD : ∀ j, 0 < D j) (hE : ∀ i, 0 < E i) :
    let τ : Fin n → ℝ := fun j ↦ (D j / γ + r * ∑ i, paperPow |K i j| (2 - s))⁻¹
    let σ : Fin m → ℝ := fun i ↦ (E i / δ + r⁻¹ * ∑ j, paperPow |K i j| s)⁻¹
    (∀ j, 0 < (τ j)⁻¹ - D j / 2) ∧ (∀ i, 0 < (σ i)⁻¹ - E i / 2) ∧
    (∀ x : Fin n → ℝ,
      ∑ i, (∑ j, K i j * x j) ^ 2 / ((σ i)⁻¹ - E i / 2) ≤
        ∑ j, ((τ j)⁻¹ - D j / 2) * x j ^ 2) ∧
    (∀ (α : ℕ → ℝ) (ε : ℝ),
      0 < ε ∧ ε < (9 - 4 * max γ δ) / (2 * max γ δ) →
      Monotone α →
      (∀ k, 0 ≤ α k ∧ α k ≤
        1 + (Real.sqrt (9 - 4 * max γ δ - 2 * ε * max γ δ) - 3) / max γ δ) →
      ∀ k,
        (∀ i, 0 ≤ (1 - 3 * α k - ε) / (σ i) - (1 - α k)^2 * E i / 2) ∧
        (∀ j, 0 ≤ (1 - 3 * α k - ε) / (τ j) - (1 - α k)^2 * D j / 2) ∧
        (∀ x : Fin n → ℝ,
          Real.sqrt (∑ i, (∑ j, K i j * x j) ^ 2 /
            ((1 - 3 * α k - ε) / (σ i) - (1 - α k)^2 * E i / 2)) ≤
          (1 - 3 * α k - ε)⁻¹ *
            Real.sqrt (∑ j, ((1 - 3 * α k - ε) / (τ j) -
              (1 - α k)^2 * D j / 2) * x j ^ 2))) := by
  dsimp only
  let a : Fin n → ℝ := fun j => ∑ i, paperPow |K i j| (2 - s)
  let b : Fin m → ℝ := fun i => ∑ j, paperPow |K i j| s
  let τ : Fin n → ℝ := fun j => (D j / γ + r * a j)⁻¹
  let σ : Fin m → ℝ := fun i => (E i / δ + r⁻¹ * b i)⁻¹
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    exact Finset.sum_nonneg fun i _ => paperPow_nonneg (abs_nonneg _)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact Finset.sum_nonneg fun j _ => paperPow_nonneg (abs_nonneg _)
  have hτden : ∀ j, 0 < D j / γ + r * a j := by
    intro j
    exact add_pos_of_pos_of_nonneg (div_pos (hD j) hγ.1)
      (mul_nonneg (le_of_lt hr) (ha j))
  have hσden : ∀ i, 0 < E i / δ + r⁻¹ * b i := by
    intro i
    exact add_pos_of_pos_of_nonneg (div_pos (hE i) hδ.1)
      (mul_nonneg (le_of_lt (inv_pos.mpr hr)) (hb i))
  have hτinv : ∀ j, (τ j)⁻¹ = D j / γ + r * a j := by
    intro j
    simp [τ]
  have hσinv : ∀ i, (σ i)⁻¹ = E i / δ + r⁻¹ * b i := by
    intro i
    simp [σ]
  have hτpos : ∀ j, 0 < (τ j)⁻¹ - D j / 2 := by
    intro j
    rw [hτinv]
    have hhalf : D j / 2 < D j / γ := (div_lt_div_iff₀ (by norm_num) hγ.1).mpr (by nlinarith [hD j, hγ.2])
    nlinarith [mul_nonneg (le_of_lt hr) (ha j)]
  have hσpos : ∀ i, 0 < (σ i)⁻¹ - E i / 2 := by
    intro i
    rw [hσinv]
    have hhalf : E i / 2 < E i / δ := (div_lt_div_iff₀ (by norm_num) hδ.1).mpr (by nlinarith [hE i, hδ.2])
    nlinarith [mul_nonneg (le_of_lt (inv_pos.mpr hr)) (hb i)]
  refine ⟨hτpos, hσpos, ?_, ?_⟩
  · intro x
    have hrow : ∀ i, (∑ j, K i j * x j) ^ 2 ≤
        b i * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 := by
      intro i
      have hfactor : ∀ j, (K i j * x j) ^ 2 =
          paperPow |K i j| s * (paperPow |K i j| (2 - s) * x j ^ 2) := by
        intro j
        rw [mul_pow, ← paperPow_split_abs_two (K i j) s]
        ring
      simpa [b] using finite_weighted_cauchy_schwarz
        (fun j => paperPow |K i j| s)
        (fun j => paperPow |K i j| (2 - s) * x j ^ 2)
        (fun j => K i j * x j)
        (fun j => paperPow_nonneg (abs_nonneg _))
        (fun j => mul_nonneg (paperPow_nonneg (abs_nonneg _)) (sq_nonneg _)) hfactor
    have hBbase : ∀ i, r⁻¹ * b i ≤ (σ i)⁻¹ - E i / 2 := by
      intro i
      rw [hσinv]
      have hhalf : E i / 2 ≤ E i / δ := le_of_lt
        ((div_lt_div_iff₀ (by norm_num) hδ.1).mpr (by nlinarith [hE i, hδ.2]))
      linarith
    have hterm : ∀ i, (∑ j, K i j * x j) ^ 2 / ((σ i)⁻¹ - E i / 2) ≤
        r * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 := by
      intro i
      have hBpos := hσpos i
      have hsum : 0 ≤ ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 :=
        Finset.sum_nonneg fun j _ => mul_nonneg (paperPow_nonneg (abs_nonneg _)) (sq_nonneg _)
      have hdiv : b i / ((σ i)⁻¹ - E i / 2) ≤ r := by
        apply (div_le_iff₀ hBpos).2
        calc
          b i = r * (r⁻¹ * b i) := by field_simp
          _ ≤ r * ((σ i)⁻¹ - E i / 2) :=
            mul_le_mul_of_nonneg_left (hBbase i) (le_of_lt hr)
      calc
        (∑ j, K i j * x j) ^ 2 / ((σ i)⁻¹ - E i / 2) ≤
            (b i * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2) /
              ((σ i)⁻¹ - E i / 2) :=
          div_le_div_of_nonneg_right (hrow i) (le_of_lt hBpos)
        _ = (b i / ((σ i)⁻¹ - E i / 2)) *
              (∑ j, paperPow |K i j| (2 - s) * x j ^ 2) := by ring
        _ ≤ r * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 :=
          mul_le_mul_of_nonneg_right hdiv hsum
    calc
      ∑ i, (∑ j, K i j * x j) ^ 2 / ((σ i)⁻¹ - E i / 2) ≤
          ∑ i, r * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = ∑ j, (r * a j) * x j ^ 2 := by
        simp only [a, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ j, ((τ j)⁻¹ - D j / 2) * x j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [hτinv]
        have hhalf : D j / 2 ≤ D j / γ := le_of_lt
          ((div_lt_div_iff₀ (by norm_num) hγ.1).mpr (by nlinarith [hD j, hγ.2]))
        nlinarith [sq_nonneg (x j)]
  · intro α ε hε hmono hα k
    let c : ℝ := 1 - 3 * α k - ε
    have hscalar := inertial_scalar_bound γ δ ε (α k) hγ hδ hε (hα k)
    have hc : 0 ≤ c := by
      dsimp [c]
      calc
        1 - 3 * α k - ε = γ * ((1 - 3 * α k - ε) / γ) := by
          field_simp [hγ.1.ne']
        _ ≥ 0 := mul_nonneg (le_of_lt hγ.1) (le_trans (by positivity) hscalar.1)
    have hσmod : ∀ i, 0 ≤ c / (σ i) - (1 - α k) ^ 2 * E i / 2 := by
      intro i
      have hfirst : 0 ≤ E i * (c / δ - (1 - α k) ^ 2 / 2) :=
        mul_nonneg (le_of_lt (hE i)) (sub_nonneg.mpr (by simpa [c] using hscalar.2))
      have hsecond : 0 ≤ c * (r⁻¹ * b i) :=
        mul_nonneg hc (mul_nonneg (le_of_lt (inv_pos.mpr hr)) (hb i))
      rw [div_eq_mul_inv, hσinv]
      rw [show c * (E i / δ + r⁻¹ * b i) - (1 - α k) ^ 2 * E i / 2 =
        E i * (c / δ - (1 - α k) ^ 2 / 2) + c * (r⁻¹ * b i) by ring]
      exact add_nonneg hfirst hsecond
    have hτmod : ∀ j, 0 ≤ c / (τ j) - (1 - α k) ^ 2 * D j / 2 := by
      intro j
      have hfirst : 0 ≤ D j * (c / γ - (1 - α k) ^ 2 / 2) :=
        mul_nonneg (le_of_lt (hD j)) (sub_nonneg.mpr (by simpa [c] using hscalar.1))
      have hsecond : 0 ≤ c * (r * a j) :=
        mul_nonneg hc (mul_nonneg (le_of_lt hr) (ha j))
      rw [div_eq_mul_inv, hτinv]
      rw [show c * (D j / γ + r * a j) - (1 - α k) ^ 2 * D j / 2 =
        D j * (c / γ - (1 - α k) ^ 2 / 2) + c * (r * a j) by ring]
      exact add_nonneg hfirst hsecond
    refine ⟨hσmod, hτmod, ?_⟩
    intro x
    let B : Fin m → ℝ := fun i ↦ c / (σ i) - (1 - α k) ^ 2 * E i / 2
    let A : Fin n → ℝ := fun j ↦ c / (τ j) - (1 - α k) ^ 2 * D j / 2
    have hBnonneg : ∀ i, 0 ≤ B i := by
      intro i
      simpa [B] using hσmod i
    have hAnonneg : ∀ j, 0 ≤ A j := by
      intro j
      simpa [A] using hτmod j
    have hcpos : 0 < c := by
      apply lt_of_le_of_ne hc
      intro hc0
      have hsc : (1 - α k) ^ 2 / 2 ≤ 0 := by
        have hsc' : (1 - α k) ^ 2 / 2 ≤ c / γ := by
          simpa [c] using hscalar.1
        rw [← hc0] at hsc'
        simpa using hsc'
      have hαone : α k = 1 := by
        nlinarith [sq_nonneg (1 - α k)]
      dsimp [c] at hc0
      nlinarith [hε.1]
    have hcinvpos : 0 < c⁻¹ := inv_pos.mpr hcpos
    have hcrinvpos : 0 < c * r⁻¹ :=
      mul_pos hcpos (inv_pos.mpr hr)
    have hBbase : ∀ i, c * (r⁻¹ * b i) ≤ B i := by
      intro i
      have hfirst : 0 ≤ E i * (c / δ - (1 - α k) ^ 2 / 2) :=
        mul_nonneg (le_of_lt (hE i))
          (sub_nonneg.mpr (by simpa [c] using hscalar.2))
      change c * (r⁻¹ * b i) ≤
        c / (σ i) - (1 - α k) ^ 2 * E i / 2
      rw [div_eq_mul_inv, hσinv]
      rw [show c * (E i / δ + r⁻¹ * b i) - (1 - α k) ^ 2 * E i / 2 =
        E i * (c / δ - (1 - α k) ^ 2 / 2) + c * (r⁻¹ * b i) by ring]
      linarith
    have hAbase : ∀ j, c * (r * a j) ≤ A j := by
      intro j
      have hfirst : 0 ≤ D j * (c / γ - (1 - α k) ^ 2 / 2) :=
        mul_nonneg (le_of_lt (hD j))
          (sub_nonneg.mpr (by simpa [c] using hscalar.1))
      change c * (r * a j) ≤
        c / (τ j) - (1 - α k) ^ 2 * D j / 2
      rw [div_eq_mul_inv, hτinv]
      rw [show c * (D j / γ + r * a j) - (1 - α k) ^ 2 * D j / 2 =
        D j * (c / γ - (1 - α k) ^ 2 / 2) + c * (r * a j) by ring]
      linarith
    have hrow : ∀ i, (∑ j, K i j * x j) ^ 2 ≤
        b i * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 := by
      intro i
      have hfactor : ∀ j, (K i j * x j) ^ 2 =
          paperPow |K i j| s * (paperPow |K i j| (2 - s) * x j ^ 2) := by
        intro j
        rw [mul_pow, ← paperPow_split_abs_two (K i j) s]
        ring
      simpa [b] using finite_weighted_cauchy_schwarz
        (fun j => paperPow |K i j| s)
        (fun j => paperPow |K i j| (2 - s) * x j ^ 2)
        (fun j => K i j * x j)
        (fun j => paperPow_nonneg (abs_nonneg _))
        (fun j => mul_nonneg (paperPow_nonneg (abs_nonneg _)) (sq_nonneg _)) hfactor
    have hterm : ∀ i, (∑ j, K i j * x j) ^ 2 / B i ≤
        (r / c) * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 := by
      intro i
      have hW : 0 ≤ ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 :=
        Finset.sum_nonneg fun j _ =>
          mul_nonneg (paperPow_nonneg (abs_nonneg _)) (sq_nonneg _)
      by_cases hB0 : B i = 0
      · have hb0 : b i = 0 := by
          have : c * (r⁻¹ * b i) = 0 := by
            apply le_antisymm
            · simpa [hB0] using hBbase i
            · exact mul_nonneg (le_of_lt hcpos)
                (mul_nonneg (le_of_lt (inv_pos.mpr hr)) (hb i))
          rcases mul_eq_zero.mp this with hzero | hzero
          · exact (ne_of_gt hcpos hzero).elim
          · rcases mul_eq_zero.mp hzero with hri | hbi
            · exact (ne_of_gt (inv_pos.mpr hr) hri).elim
            · exact hbi
        have hN0 : (∑ j, K i j * x j) ^ 2 = 0 := by
          apply le_antisymm
          · simpa [hb0] using hrow i
          · exact sq_nonneg _
        simp [hB0, hN0, mul_nonneg (le_of_lt (div_pos hr hcpos)) hW]
      · have hBpos : 0 < B i := lt_of_le_of_ne (hBnonneg i) (Ne.symm hB0)
        have hratio : b i / B i ≤ r / c := by
          apply (div_le_iff₀ hBpos).2
          have hmul := mul_le_mul_of_nonneg_left (hBbase i)
            (le_of_lt (div_pos hr hcpos))
          calc
            b i = (r / c) * (c * (r⁻¹ * b i)) := by
              field_simp [hr.ne', hcpos.ne'] <;> ring
            _ ≤ (r / c) * B i := hmul
        calc
          (∑ j, K i j * x j) ^ 2 / B i ≤
              (b i * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2) / B i :=
            div_le_div_of_nonneg_right (hrow i) (le_of_lt hBpos)
          _ = (b i / B i) * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 := by ring
          _ ≤ (r / c) * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 :=
            mul_le_mul_of_nonneg_right hratio hW
    have hsum : ∑ i, (∑ j, K i j * x j) ^ 2 / B i ≤
        (r / c) * ∑ j, a j * x j ^ 2 := by
      calc
        ∑ i, (∑ j, K i j * x j) ^ 2 / B i ≤
            ∑ i, (r / c) * ∑ j, paperPow |K i j| (2 - s) * x j ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
        _ = (r / c) * ∑ j, a j * x j ^ 2 := by
          simp only [a, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
    have hsq : ∑ i, (∑ j, K i j * x j) ^ 2 / B i ≤
        (c⁻¹) ^ 2 * ∑ j, A j * x j ^ 2 := by
      calc
        ∑ i, (∑ j, K i j * x j) ^ 2 / B i ≤
            (r / c) * ∑ j, a j * x j ^ 2 := hsum
        _ = ∑ j, (r / c) * (a j * x j ^ 2) := by rw [Finset.mul_sum]
        _ ≤ ∑ j, (c⁻¹) ^ 2 * (A j * x j ^ 2) := by
          apply Finset.sum_le_sum
          intro j _
          have hmul := mul_le_mul_of_nonneg_right (hAbase j) (sq_nonneg (x j))
          have hscale := mul_le_mul_of_nonneg_left hmul (sq_nonneg c⁻¹)
          calc
            (r / c) * (a j * x j ^ 2) =
                (c⁻¹) ^ 2 * (c * (r * a j) * x j ^ 2) := by
              field_simp [hcpos.ne'] <;> ring
            _ ≤ (c⁻¹) ^ 2 * (A j * x j ^ 2) := by
              convert hscale using 1 <;> ring
        _ = (c⁻¹) ^ 2 * ∑ j, A j * x j ^ 2 := by rw [Finset.mul_sum]
    have hsqrt := Real.sqrt_le_sqrt hsq
    have hR : 0 ≤ ∑ j, A j * x j ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hAnonneg j) (sq_nonneg _)
    calc
      Real.sqrt (∑ i, (∑ j, K i j * x j) ^ 2 /
          (c / (σ i) - (1 - α k) ^ 2 * E i / 2)) =
          Real.sqrt (∑ i, (∑ j, K i j * x j) ^ 2 / B i) := by rfl
      _ ≤ Real.sqrt ((c⁻¹) ^ 2 * ∑ j, A j * x j ^ 2) := hsqrt
      _ = c⁻¹ * Real.sqrt (∑ j, A j * x j ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg c⁻¹), Real.sqrt_sq_eq_abs,
          abs_of_pos hcinvpos]
      _ = (1 - 3 * α k - ε)⁻¹ *
          Real.sqrt (∑ j, (c / (τ j) - (1 - α k) ^ 2 * D j / 2) * x j ^ 2) := by
        simp only [A, c]

end LorenzPock
