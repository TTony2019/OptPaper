import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_4

/-!
# Interior characterization via support function
Let $C \subset H$ be a closed convex set in a real Hilbert space. Then
$0 \in \operatorname{int}(C)$ if and only if there exists $\alpha > 0$ such
that $\sigma_C(x) \geqslant \alpha |x|$ for all $x \in H$.

The closedness of `C` and the completeness of `H` are the hypotheses used by
the classical strict-separation proof of the reverse implication.
Cited from: classical result in convex analysis
(see e.g. R.T. Rockafellar, Convex Analysis, Princeton University Press, 1970).
-/
open Set
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If `0 ∈ C`, then the support function of `C` vanishes at `0`. -/
lemma supportFunction_zero_of_mem {C : Set H} (h0 : (0 : H) ∈ C) :
    supportFunction C 0 = 0 := by
  unfold supportFunction
  have h : ((fun z : H => (inner ℝ z 0 : EReal)) '' C) = {0} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, h0, by simp⟩
  rw [h, sSup_singleton]

/-- The support function of a set containing `0` in its interior is bounded
below by `α ‖x‖` for some positive `α`. -/
lemma supportFunction_lower_bound_of_interior {C : Set H}
    (hint : (0 : H) ∈ interior C) :
    ∃ (α : ℝ), α > 0 ∧
      ∀ x : H, supportFunction C x ≥ ((α * ‖x‖ : ℝ) : EReal) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hεpos, hε⟩ := hint
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have h0C : (0 : H) ∈ C := by
      exact hε (by simp [Metric.mem_ball, hεpos])
    simp [supportFunction_zero_of_mem h0C]
  · set z : H := (ε / 2 / ‖x‖) • x with hzdef
    have hz_norm : ‖z‖ = ε / 2 := by
      rw [hzdef, norm_smul, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hz_mem : z ∈ C := by
      apply hε
      rw [Metric.mem_ball, dist_zero_right, hz_norm]
      linarith
    have hinner : inner ℝ z x = ε / 2 * ‖x‖ := by
      rw [hzdef, inner_smul_left]
      simp only [RCLike.conj_to_real]
      rw [real_inner_self_eq_norm_sq]
      field_simp
    unfold supportFunction
    exact le_sSup ⟨z, hz_mem, by
      change (((inner ℝ z x) : ℝ) : EReal) = (((ε / 2 * ‖x‖) : ℝ) : EReal)
      rw [hinner]⟩

/-- Under the closedness and completeness hypotheses supplied by the classical
separation argument, the support-function lower bound puts the open ball of
radius `α` around `0` inside `C`. -/
lemma closedConvexBoundGivesBall [CompleteSpace H] {C : Set H}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {α : ℝ} (hα : α > 0)
    (hbound : ∀ x : H,
      supportFunction C x ≥ ((α * ‖x‖ : ℝ) : EReal)) :
    Metric.ball (0 : H) α ⊆ C := by
  have _ : α > 0 := hα
  intro y hy
  rw [Metric.mem_ball, dist_zero_right] at hy
  by_contra hyC
  obtain ⟨f, u, hfu, huy⟩ :=
    geometric_hahn_banach_closed_point hconv hclosed hyC
  set v : H := (InnerProductSpace.toDual ℝ H).symm f with hvdef
  have hv_apply : ∀ x : H, f x = inner ℝ v x := by
    intro x
    rw [hvdef]
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H)
      (x := x) (y := f)).symm
  have h2 : supportFunction C v ≤ (u : EReal) := by
    unfold supportFunction
    refine sSup_le ?_
    rintro b ⟨z, hz, rfl⟩
    have hz' : f z < u := hfu z hz
    rw [hv_apply z] at hz'
    change ((inner ℝ z v : ℝ) : EReal) ≤ (u : EReal)
    rw [real_inner_comm v z]
    exact le_of_lt (EReal.coe_lt_coe_iff.mpr hz')
  have h3 : (u : EReal) < ((inner ℝ v y : ℝ) : EReal) := by
    rw [hv_apply y] at huy
    exact EReal.coe_lt_coe_iff.mpr huy
  have hchain : ((α * ‖v‖ : ℝ) : EReal) < ((‖v‖ * ‖y‖ : ℝ) : EReal) := by
    calc ((α * ‖v‖ : ℝ) : EReal) ≤ supportFunction C v := hbound v
      _ ≤ (u : EReal) := h2
      _ < ((inner ℝ v y : ℝ) : EReal) := h3
      _ ≤ ((‖v‖ * ‖y‖ : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (real_inner_le_norm v y)
  have hreal : α * ‖v‖ < ‖v‖ * ‖y‖ := EReal.coe_lt_coe_iff.mp hchain
  have hnpos : 0 < ‖v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h] at hreal
      simp at hreal
    · exact h
  nlinarith [hreal, mul_lt_mul_of_pos_left hy hnpos]

/-- The reverse implication of the interior characterization under the
closedness and completeness hypotheses needed by the separation argument. -/
lemma closedConvexBoundGivesInterior [CompleteSpace H] {C : Set H}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {α : ℝ} (hα : α > 0)
    (hbound : ∀ x : H,
      supportFunction C x ≥ ((α * ‖x‖ : ℝ) : EReal)) :
    (0 : H) ∈ interior C := by
  refine interior_mono (closedConvexBoundGivesBall hclosed hconv hα hbound) ?_
  simp [Metric.isOpen_ball.interior_eq, Metric.mem_ball, hα]

/-- For a closed convex set `C` in a real Hilbert space, `0 ∈ int(C)` iff
there exists `α > 0` such that `σ_C(x) ≥ α ‖x‖` for all `x`. -/
theorem interior_zero_iff_supportFunction [CompleteSpace H] (C : Set H)
    (hclosed : IsClosed C)
    (hC : Convex ℝ C) :
    (0 ∈ interior C) ↔
      ∃ (α : ℝ), α > 0 ∧ ∀ x, supportFunction C x ≥ ((α * ‖x‖ : ℝ) : EReal) := by
  constructor
  · exact supportFunction_lower_bound_of_interior
  · -- `IsClosed C` and `[CompleteSpace H]` supply the hypotheses of the
    -- strict-separation helper, which closes the reverse implication.
    rintro ⟨α, hα, hbound⟩
    exact closedConvexBoundGivesInterior hclosed hC hα hbound
