import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_7
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_lem_1
namespace Alvarez2002
/-- Uniform Lojasiewicz inequality near a compact connected critical set. -/
theorem connected_critical_set_lojasiewicz {N : Type*} [Fintype N]
    (Ω A : Set (EuclideanSpace ℝ N)) (Φ : EuclideanSpace ℝ N → ℝ)
    (gradΦ : EuclideanSpace ℝ N → EuclideanSpace ℝ N)
    (hΩ : IsOpen Ω) (hanalytic : IsRealAnalyticOn Ω Φ) (hAΩ : A ⊆ Ω) (hA : A.Nonempty)
    (_hgrad : ∀ x v,
      HasDerivAt (fun t : ℝ => Φ (x + t • v)) (inner ℝ (gradΦ x) v) 0)
    (hcritical : ∀ a ∈ A, gradΦ a = 0) (hconnected : IsConnected A) :
    (∃ c : ℝ, ∀ a ∈ A, Φ a = c) ∧
    (IsCompact A → ∃ σ θ c : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      (∀ a ∈ A, Φ a = c) ∧
      ∀ x, Metric.infDist x A < σ → Real.rpow |Φ x - c| (1 - θ) ≤ ‖gradΦ x‖) := by
  rcases hanalytic with ⟨_, hanalyticOn⟩
  have hlocal : ∀ a ∈ A, ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ x, ‖x - a‖ < σ → Real.rpow |Φ x - Φ a| (1 - θ) ≤ ‖gradΦ x‖ := by
    intro a ha
    exact lojasiewicz_gradient_inequality Φ gradΦ a ⟨Ω, ⟨hΩ, hanalyticOn⟩, hAΩ ha⟩
      _hgrad (hcritical a ha)
  have hlocally_constant : ∀ a ∈ A, ∃ σ : ℝ, 0 < σ ∧
      ∀ x ∈ A, ‖x - a‖ < σ → Φ x = Φ a := by
    intro a ha
    rcases hlocal a ha with ⟨σ, θ, hσ, hθ, hθlt, hineq⟩
    refine ⟨σ, hσ, ?_⟩
    intro x hx hxa
    have hz : Real.rpow |Φ x - Φ a| (1 - θ) = 0 := by
      apply le_antisymm
      · simpa [hcritical x hx] using hineq x hxa
      · exact Real.rpow_nonneg (abs_nonneg _) _
    have habs : |Φ x - Φ a| = 0 :=
      (Real.rpow_eq_zero (abs_nonneg _) (by linarith)).mp hz
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  let a0 : EuclideanSpace ℝ N := Classical.choose hA
  have ha0 : a0 ∈ A := Classical.choose_spec hA
  let c : ℝ := Φ a0
  let P : Set {x // x ∈ A} := {x | Φ x = c}
  have hPopen : IsOpen P := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, hx⟩ hxP
    rcases hlocally_constant x hx with ⟨σ, hσ, hloc⟩
    filter_upwards [Metric.ball_mem_nhds (⟨x, hx⟩ : {x // x ∈ A}) hσ] with y hy
    change dist y.val x < σ at hy
    change Φ y.val = c
    exact (hloc y.val y.property (by simpa [dist_eq_norm] using hy)).trans hxP
  have hPclosed : IsClosed P := by
    exact IsClosed.preimage (hanalyticOn.continuousOn.mono hAΩ).restrict isClosed_singleton
  letI : PreconnectedSpace {x // x ∈ A} := Subtype.preconnectedSpace hconnected.isPreconnected
  have hPall : Set.univ ⊆ P :=
    isPreconnected_univ.subset_isClopen ⟨hPclosed, hPopen⟩ ⟨⟨a0, ha0⟩, trivial, rfl⟩
  have hconst : ∀ a ∈ A, Φ a = c := by
    intro a ha
    have hmem := hPall (show (⟨a, ha⟩ : {x // x ∈ A}) ∈ Set.univ by trivial)
    exact hmem
  constructor
  · exact ⟨c, hconst⟩
  intro hcompact
  choose σ θ hσ hθpos hθlt hineq using hlocal
  let U : (a : {a // a ∈ A}) → Set (EuclideanSpace ℝ N) :=
    fun a => Metric.ball a (σ a a.property)
  have hUopen : ∀ a, IsOpen (U a) := fun a => Metric.isOpen_ball
  have hUcover : A ⊆ ⋃ a, U a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (hσ x hx)
  obtain ⟨t, htcover⟩ := hcompact.elim_finite_subcover U hUopen hUcover
  have ht : t.Nonempty := by
    by_contra ht
    simp only [Finset.not_nonempty_iff_eq_empty] at ht
    rcases hA with ⟨x, hx⟩
    have : x ∈ (∅ : Set (EuclideanSpace ℝ N)) := by simpa [ht] using htcover hx
    exact this
  let θ0 : ℝ := t.inf' ht (fun a => θ a a.property)
  have hθ0pos : 0 < θ0 := by
    rw [show θ0 = t.inf' ht (fun a => θ a a.property) by rfl]
    exact (Finset.lt_inf'_iff ht).2 (fun a ha => hθpos a a.property)
  have hθ0le : ∀ a ∈ t, θ0 ≤ θ a a.property := by
    intro a ha
    exact Finset.inf'_le _ ha
  obtain ⟨a1, ha1⟩ := ht
  have hθ0lt : θ0 < 1 / 2 :=
    lt_of_le_of_lt (hθ0le a1 ha1) (hθlt a1 a1.property)
  have hsmall_nhd : ∀ a ∈ A, ∃ ε : ℝ, 0 < ε ∧
      ∀ x, dist x a < ε → |Φ x - c| < 1 := by
    intro a ha
    have hat : AnalyticAt ℝ Φ a := hanalyticOn a (hAΩ ha)
    rcases (Metric.continuousAt_iff.mp hat.continuousAt 1 zero_lt_one) with ⟨ε, hε, hεprop⟩
    refine ⟨ε, hε, ?_⟩
    intro x hxa
    have hdist := hεprop hxa
    simpa [hconst a ha, Real.dist_eq] using hdist
  choose ε hε hεsmall using hsmall_nhd
  let V : (a : {a // a ∈ A}) → Set (EuclideanSpace ℝ N) :=
    fun a => Metric.ball a (ε a a.property)
  have hVopen : ∀ a, IsOpen (V a) := by
    intro a
    exact Metric.isOpen_ball
  have hVcover : A ⊆ ⋃ a, V a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (hε x hx)
  obtain ⟨u, hucover⟩ := hcompact.elim_finite_subcover V hVopen hVcover
  let W : Set (EuclideanSpace ℝ N) := (⋃ a ∈ t, U a) ∩ (⋃ a ∈ u, V a)
  have hWopen : IsOpen W :=
    (isOpen_biUnion fun a _ => hUopen a).inter (isOpen_biUnion fun a _ => hVopen a)
  have hWcover : A ⊆ W := fun x hx => ⟨htcover hx, hucover hx⟩
  obtain ⟨δ, hδ, hδW⟩ := hcompact.exists_thickening_subset_open hWopen hWcover
  refine ⟨δ, θ0, c, hδ, hθ0pos, hθ0lt, hconst, ?_⟩
  intro x hx
  have hxW : x ∈ W := hδW ((Metric.mem_thickening_iff_infDist_lt hA).2 hx)
  rcases Set.mem_iUnion₂.1 hxW.1 with ⟨a, ha, hxa⟩
  rcases Set.mem_iUnion₂.1 hxW.2 with ⟨b, hb, hxb⟩
  have hsmall : |Φ x - c| ≤ 1 := le_of_lt (hεsmall b b.property x
    (by simpa [V, Metric.mem_ball] using hxb))
  have hlocalineq := hineq a a.property x
    (by simpa [U, Metric.mem_ball, dist_eq_norm] using hxa)
  have hlocalineq' : Real.rpow |Φ x - c| (1 - θ a a.property) ≤ ‖gradΦ x‖ := by
    simpa [hconst a a.property] using hlocalineq
  by_cases hz : |Φ x - c| = 0
  · rw [hz]
    exact (Real.zero_rpow (x := 1 - θ0) (by linarith)).le.trans (norm_nonneg _)
  · have hpos : 0 < |Φ x - c| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    apply le_trans (Real.rpow_le_rpow_of_exponent_ge hpos hsmall (by linarith [hθ0le a ha]))
      hlocalineq'
end Alvarez2002
