import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_2

open scoped InnerProductSpace

open ERealFunction

namespace Nesterov1983

private theorem affine_linear_le_of_posHomogeneous {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : E → ℝ) (hhom : PositivelyHomogeneous F)
    (L : E →L[ℝ] ℝ) (c : ℝ) (hminor : ∀ x, L x + c ≤ F x) :
    ∀ x, L x ≤ F x := by
  intro x
  by_contra hnot
  have hbad : F x < L x := lt_of_not_ge hnot
  let d : ℝ := L x - F x
  have hd : 0 < d := sub_pos.mpr hbad
  obtain ⟨n, hn⟩ := exists_nat_gt ((-c) / d)
  let N : ℕ := n + 1
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hNgt : (-c) / d < (N : ℝ) := by
    calc
      (-c) / d < (n : ℝ) := hn
      _ < (N : ℝ) := by
        dsimp [N]
        norm_num
  have hscaled := hminor ((N : ℝ) • x)
  have hhomN := hhom hN x
  rw [hhomN] at hscaled
  rw [L.map_smul] at hscaled
  have hscaled' : (N : ℝ) * L x + c ≤ (N : ℝ) * F x := by
    simpa [smul_eq_mul] using hscaled
  have hcontra : -c < (N : ℝ) * d := by
    have := mul_lt_mul_of_pos_right hNgt hd
    field_simp [d] at this
    nlinarith
  dsimp [d] at hcontra
  nlinarith

private theorem riesz_mem_convexSubdifferential_of_affine_minorant {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → ℝ) (hF0 : F 0 = 0) (hhom : PositivelyHomogeneous F)
    (L : E →L[ℝ] ℝ) (c : ℝ) (hminor : ∀ x, L x + c ≤ F x) :
    let p := (InnerProductSpace.toDual ℝ E).symm L
    p ∈ subdifferential (fun y => (F y : EReal)) 0 ∧ ∀ x, L x = inner ℝ p x := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let p := (InnerProductSpace.toDual ℝ E).symm L
  have hL : ∀ x, L x ≤ F x :=
    affine_linear_le_of_posHomogeneous F hhom L c hminor
  have hp : p ∈ subdifferential (fun y => (F y : EReal)) 0 := by
    intro v
    change (⟪v - 0, p⟫_ℝ : EReal) + (F 0 : EReal) ≤ (F v : EReal)
    norm_cast
    simp only [hF0, sub_zero]
    rw [real_inner_comm]
    rw [show inner ℝ p v = L v from
      InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v) (y := L)]
    simpa using hL v
  refine ⟨hp, ?_⟩
  intro x
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := x) (y := L)).symm

/-- A finite convex positively homogeneous function is its subdifferential support function. -/
theorem supportFunction_representation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (F : E → ℝ)
    (hconv : ConvexOn ℝ Set.univ F) (hhom : PositivelyHomogeneous F) (u : E) :
    ∃ l ∈ subdifferential (fun y => (F y : EReal)) 0, F u = inner ℝ l u ∧
      ∀ l' ∈ subdifferential (fun y => (F y : EReal)) 0, inner ℝ l' u ≤ inner ℝ l u := by
  have htwo := hhom (by norm_num : (0 : ℝ) < 2) (0 : E)
  norm_num at htwo
  have hF0 : F 0 = 0 := by linarith
  have hcont : Continuous F :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hlsc : LowerSemicontinuous F := hcont.lowerSemicontinuous
  have haffine := hconv.real_univ_sSup_affine_eq hlsc
  have hne : (subdifferential (fun y => (F y : EReal)) 0).Nonempty := by
    obtain ⟨L, c, hle, _⟩ := hconv.exists_affine_le_of_lt (𝕜 := ℝ)
      (a := F 0 - 1) (show (0 : E) ∈ Set.univ by simp) (by linarith) isClosed_univ
      (lowerSemicontinuousOn_univ_iff.mpr hlsc)
    have hminor : ∀ x, L x + c ≤ F x := by
      intro x
      simpa using hle ⟨x, Set.mem_univ x⟩
    obtain ⟨hp, _⟩ := riesz_mem_convexSubdifferential_of_affine_minorant
      F hF0 hhom L c hminor
    exact ⟨_, hp⟩
  have hclosed : IsClosed (subdifferential (fun y => (F y : EReal)) 0) := by
    have hset : subdifferential (fun y => (F y : EReal)) 0 =
        ⋂ v : E, {l : E | F 0 + inner ℝ l (v - 0) ≤ F v} := by
      ext l
      rw [mem_convexSubdifferential_iff]
      simp
    rw [hset]
    apply isClosed_iInter
    intro v
    apply isClosed_le
    · fun_prop
    · fun_prop
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunitcompact : IsCompact (Metric.closedBall (0 : E) 1) :=
    ProperSpace.isCompact_closedBall 0 1
  obtain ⟨z, hz, hzmax⟩ := hunitcompact.exists_isMaxOn
    ⟨0, by
      rw [Metric.mem_closedBall, dist_self]
      norm_num⟩ (hcont.abs.continuousOn)
  let B : ℝ := |F z|
  have hB : ∀ x ∈ Metric.closedBall (0 : E) 1, |F x| ≤ B := by
    intro x hx
    exact hzmax hx
  have hBnonneg : 0 ≤ B := abs_nonneg _
  have hbounded : subdifferential (fun y => (F y : EReal)) 0 ⊆ Metric.closedBall 0 B := by
    intro l hl
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hl0 : l = 0
    · simp [hl0, hBnonneg]
    · let q : E := (‖l‖⁻¹ : ℝ) • l
      have hnorm : 0 < ‖l‖ := norm_pos_iff.mpr hl0
      have hqnorm : ‖q‖ = 1 := by
        dsimp [q]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀]
        exact ne_of_gt hnorm
      have hq : q ∈ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, hqnorm]
      have hlq : inner ℝ l q ≤ F q := by
        have hl' : ∀ v, F 0 + inner ℝ l (v - 0) ≤ F v :=
          (mem_convexSubdifferential_iff F 0 l).mp hl
        simpa [hF0, sub_zero] using hl' q
      have hinter : inner ℝ l q = ‖l‖ := by
        dsimp [q]
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [← hinter]
      exact le_trans hlq (le_trans (le_abs_self _) (hB q hq))
  have hcompact : IsCompact (subdifferential (fun y => (F y : EReal)) 0) :=
    (ProperSpace.isCompact_closedBall 0 B).of_isClosed_subset hclosed hbounded
  obtain ⟨l, hl, hlmax⟩ := hcompact.exists_isMaxOn hne
    (by fun_prop : ContinuousOn (fun x : E => inner ℝ x u) (subdifferential (fun y => (F y : EReal)) 0))
  have hsupport_le : ∀ l ∈ subdifferential (fun y => (F y : EReal)) 0, inner ℝ l u ≤ F u := by
    intro l hl
    have hl' : ∀ v, F 0 + inner ℝ l (v - 0) ≤ F v :=
      (mem_convexSubdifferential_iff F 0 l).mp hl
    simpa [hF0, sub_zero] using hl' u
  let A : Set (E → ℝ) :=
    {g | g ≤ F ∧ ∃ (L : E →L[ℝ] ℝ) (c : ℝ), g = L + Function.const E c}
  have hAne : A.Nonempty := by
    let L : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E l
    refine ⟨L, ?_, L, 0, ?_⟩
    · intro x
      change inner ℝ l x ≤ F x
      have hl' : ∀ v, F 0 + inner ℝ l (v - 0) ≤ F v :=
        (mem_convexSubdifferential_iff F 0 l).mp hl
      simpa [hF0, sub_zero] using hl' x
    · ext x
      simp
  have hA_le : ∀ g ∈ A, g u ≤ inner ℝ l u := by
    intro g hg
    obtain ⟨hgF, L, c, hgeq⟩ := hg
    have hminor : ∀ x, L x + c ≤ F x := by
      intro x
      simpa [hgeq] using hgF x
    have hc : c ≤ 0 := by
      have := hminor 0
      simpa [hF0] using this
    obtain ⟨hp, hrepr⟩ := riesz_mem_convexSubdifferential_of_affine_minorant
      F hF0 hhom L c hminor
    calc
      g u = L u + c := by simp [hgeq]
      _ ≤ L u := by linarith
      _ = inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) u := hrepr u
      _ ≤ inner ℝ l u := hlmax hp
  have haffineA : sSup A = F := by
    simpa [A] using haffine
  have hFu_le : F u ≤ inner ℝ l u := by
    letI : Nonempty {g // g ∈ A} := hAne.to_subtype
    rw [← congrFun haffineA u, sSup_apply]
    apply ciSup_le
    intro g
    exact hA_le g g.property
  have hleFu : inner ℝ l u ≤ F u := hsupport_le l hl
  have heq : F u = inner ℝ l u := le_antisymm hFu_le hleFu
  exact ⟨l, hl, heq, fun l' hl' => hlmax hl'⟩

end Nesterov1983
