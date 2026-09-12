import Mathlib

open Filter
open scoped Topology BigOperators

namespace BotCsetnek2015

/-- Lemma 2.3: summability for a two-step perturbed linear recurrence. -/
theorem lemma_2_3_two_step_summability (xi eps : Nat -> Real) (a b : Real)
    (hxi_nonneg : ∀ n, 0 <= xi n)
    (heps_nonneg : ∀ n, 0 <= eps n)
    (heps_sum : Summable eps)
    (hb_nonneg : 0 <= b)
    (hab : a + b < 1)
    (hrec : ∀ n, 1 <= n -> xi (n + 1) <= a * xi n + b * xi (n - 1) + eps n) :
    Summable xi := by
  have hden_pos : 0 < 1 - a - b := by linarith
  let C : Real := ((1 - a) * xi 0 + xi 1 + ∑' n, eps n) / (1 - a - b)
  have hshift_two : ∀ k : Nat,
      Finset.sum (Finset.range k) (fun m => xi (m + 2)) + xi 0 + xi 1 =
        Finset.sum (Finset.range (k + 2)) xi := by
    intro k
    induction k with
    | zero => simp [Finset.sum_range_succ]
    | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        rw [← ih]
        ring
  have hshift_one : ∀ k : Nat,
      Finset.sum (Finset.range k) (fun m => xi (m + 1)) + xi 0 =
        Finset.sum (Finset.range (k + 1)) xi := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        rw [← ih]
        ring
  have htail_le_tsum : ∀ k : Nat,
      Finset.sum (Finset.range k) (fun m => eps (m + 1)) <= ∑' n, eps n := by
    intro k
    rw [← Finset.sum_image]
    · exact heps_sum.sum_le_tsum ((Finset.range k).image (fun m => m + 1)) (by
        intro n hn
        exact heps_nonneg n)
    · intro x hx y hy hxy
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxy)
  have hpartial : ∀ k : Nat, 1 <= k ->
      (1 - a - b) * Finset.sum (Finset.range (k + 1)) xi <=
        (1 - a) * xi 0 + xi 1 + Finset.sum (Finset.range k) (fun m => eps (m + 1)) := by
    intro k hk
    have hsum_rec :
        Finset.sum (Finset.range k) (fun m => xi (m + 2)) <=
          a * Finset.sum (Finset.range k) (fun m => xi (m + 1)) +
          b * Finset.sum (Finset.range k) xi +
          Finset.sum (Finset.range k) (fun m => eps (m + 1)) := by
      calc
        Finset.sum (Finset.range k) (fun m => xi (m + 2))
            <= Finset.sum (Finset.range k)
                (fun m => a * xi (m + 1) + b * xi m + eps (m + 1)) := by
              exact Finset.sum_le_sum (fun m hm => by
                simpa [Nat.add_assoc] using
                  hrec (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
        _ = a * Finset.sum (Finset.range k) (fun m => xi (m + 1)) +
              b * Finset.sum (Finset.range k) xi +
              Finset.sum (Finset.range k) (fun m => eps (m + 1)) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
    set S : Real := Finset.sum (Finset.range (k + 1)) xi
    set L : Real := Finset.sum (Finset.range k) (fun m => xi (m + 2))
    set A : Real := Finset.sum (Finset.range k) (fun m => xi (m + 1))
    set B : Real := Finset.sum (Finset.range k) xi
    set E : Real := Finset.sum (Finset.range k) (fun m => eps (m + 1))
    have hLsum : L + xi 0 + xi 1 = S + xi (k + 1) := by
      dsimp [L, S]
      have hsucc :
          Finset.sum (Finset.range (k + 1)) xi + xi (k + 1) =
            Finset.sum (Finset.range (k + 2)) xi := by
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using
          (Finset.sum_range_succ xi (k + 1)).symm
      nlinarith [hshift_two k]
    have hAsum : A + xi 0 = S := by
      dsimp [A, S]
      exact hshift_one k
    have hBsum : B + xi k = S := by
      dsimp [B, S]
      simpa [Nat.succ_eq_add_one] using (Finset.sum_range_succ xi k).symm
    have hmain : S + xi (k + 1) - xi 0 - xi 1 <= (a + b) * S - a * xi 0 - b * xi k + E := by
      have hA' : A = S - xi 0 := by linarith
      have hB' : B = S - xi k := by linarith
      have hL' : L = S + xi (k + 1) - xi 0 - xi 1 := by linarith
      have hrec' : L <= a * A + b * B + E := by simpa [L, A, B, E] using hsum_rec
      rw [hL', hA', hB'] at hrec'
      nlinarith
    have hxkp1 : 0 <= xi (k + 1) := hxi_nonneg _
    have hbxk : 0 <= b * xi k := mul_nonneg hb_nonneg (hxi_nonneg _)
    dsimp [S, E] at hmain ⊢
    nlinarith
  have hbound : ∀ n : Nat, Finset.sum (Finset.range n) xi <= C := by
    intro n
    cases n with
    | zero =>
        have hnum_nonneg : 0 <= (1 - a) * xi 0 + xi 1 + ∑' n, eps n := by
          have ha_nonneg : 0 <= 1 - a := by linarith
          have htsum_nonneg : 0 <= ∑' n, eps n := tsum_nonneg heps_nonneg
          nlinarith [mul_nonneg ha_nonneg (hxi_nonneg 0), hxi_nonneg 1, htsum_nonneg]
        dsimp [C]
        exact div_nonneg hnum_nonneg hden_pos.le
    | succ n =>
        cases n with
        | zero =>
            rw [Finset.sum_range_one]
            have hnum_ge : (1 - a - b) * xi 0 <= (1 - a) * xi 0 + xi 1 + ∑' n, eps n := by
              have htsum_nonneg : 0 <= ∑' n, eps n := tsum_nonneg heps_nonneg
              have hbx0 : 0 <= b * xi 0 := mul_nonneg hb_nonneg (hxi_nonneg _)
              have hx1 : 0 <= xi 1 := hxi_nonneg _
              nlinarith
            dsimp [C]
            rw [div_eq_inv_mul]
            exact (le_inv_mul_iff₀ hden_pos).2 hnum_ge
        | succ k =>
            have hk : 1 <= k + 1 := by omega
            have hpart := hpartial (k + 1) hk
            have htail := htail_le_tsum (k + 1)
            have hnum : (1 - a - b) * Finset.sum (Finset.range ((k + 1) + 1)) xi <=
                (1 - a) * xi 0 + xi 1 + ∑' n, eps n := by
              nlinarith
            dsimp [C]
            rw [div_eq_inv_mul]
            exact (le_inv_mul_iff₀ hden_pos).2 hnum
  exact summable_of_sum_range_le hxi_nonneg hbound

end BotCsetnek2015
