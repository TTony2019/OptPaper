import Mathlib.Analysis.InnerProductSpace.Basic
import Foundation.SetValued.Monotone
import Foundation.SetValued.MaximalMonotone
import Foundation.SetValued.Minty
import Foundation.FixedPoint.Averaged

/-!
# Resolvent existence and choice for maximal monotone operators

Every maximal monotone operator on a Hilbert space has a resolvent point at
every positive parameter, and a canonical single-valued resolvent
representative is available.  Also, positive scalar multiples of a maximal
monotone operator are maximal monotone.
-/

namespace SetValuedOperator

open scoped Pointwise

/-- The set-valued operator `Id + rho A`. -/
def identityAddScaled [AddCommGroup H] [Module ℝ H] (A : SetValuedOperator H H) (rho : ℝ) :
    SetValuedOperator H H :=
  fun z => {z + rho • a | a ∈ A z}

/-- The resolvent of a set-valued operator `A` is the inverse of `Id + A`. -/
abbrev resolvent [AddCommGroup H] [Module ℝ H] (A : SetValuedOperator H H) :
    SetValuedOperator H H :=
  SetValuedOperator.inverse (identityAddScaled A 1)

/- Lean surface notation for the textbook resolvent `J_A`. -/
notation:max "J[" A:max "]" => SetValuedOperator.resolvent A

/-- The resolvent unfolds to the inverse of `Id + A`. -/
theorem resolvent_def [AddCommGroup H] [Module ℝ H] (A : SetValuedOperator H H) :
    J[A] = SetValuedOperator.inverse (identityAddScaled A 1) :=
  rfl

/-- Membership in `J[rho A]` is equivalent to the legacy `Id + rho A` formulation. -/
theorem mem_resolvent_smul_iff [AddCommGroup H] [Module ℝ H]
    (A : SetValuedOperator H H) (rho : ℝ) (x y : H) :
    y ∈ J[(rho • A)] x ↔ x ∈ A.identityAddScaled rho y := by
  simp [resolvent_def, SetValuedOperator.mem_inverse_iff,
    Set.mem_smul_set, identityAddScaled]

/-- Positive scalar multiples of a maximal monotone operator are maximal
monotone. -/
theorem positive_scaled_maximal_monotone
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

/-- A maximal monotone operator has a resolvent point at every positive
parameter. -/
theorem resolvent_exists_of_maximal_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone) (rho : ℝ) (hrho : 0 < rho) (y : H) :
    ∃ x, x ∈ J[(rho • T)] y := by
  rcases minty_surjective_of_maximal_monotone
      (T := fun x : H => rho • T x) (positive_scaled_maximal_monotone hT hrho) y with
    ⟨x, u, hu, hy⟩
  rcases hu with ⟨v, hv, rfl⟩
  refine ⟨x, ?_⟩
  rw [mem_resolvent_smul_iff]
  exact ⟨v, hv, hy.symm⟩

/-- The resolvent point of a monotone operator at a positive parameter is unique. -/
theorem resolvent_unique_of_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (hmono : T.IsMonotone) {r : ℝ} (hr : 0 < r)
    {y u v : H} (hu : u ∈ J[(r • T)] y) (hv : v ∈ J[(r • T)] y) : u = v := by
  rw [mem_resolvent_smul_iff] at hu hv
  dsimp [identityAddScaled] at hu hv
  rcases hu with ⟨a, ha, hyu⟩
  rcases hv with ⟨b, hb, hyv⟩
  have huv : u - v = r • (b - a) := by
    have hu' : u = y - r • a := by
      calc u = (u + r • a) - r • a := (add_sub_cancel_right _ _).symm
           _ = y - r • a := by rw [hyu]
    have hv' : v = y - r • b := by
      calc v = (v + r • b) - r • b := (add_sub_cancel_right _ _).symm
           _ = y - r • b := by rw [hyv]
    rw [hu', hv', smul_sub]
    abel
  have hmono' : 0 ≤ inner ℝ (a - b) (u - v) := hmono a ha b hb
  rw [huv, real_inner_smul_right] at hmono'
  have hinner : inner ℝ (a - b) (b - a) = -‖a - b‖ ^ 2 := by
    have : b - a = -(a - b) := by abel
    rw [this, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hinner] at hmono'
  have hab : a = b := by
    have hsquare : ‖a - b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a - b‖]
    have hnorm : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  rw [hab] at huv
  exact sub_eq_zero.mp (by simpa using huv)

/-- A maximal monotone operator has exactly one resolvent point at every positive parameter. -/
theorem resolvent_existsUnique_of_maximal_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (mu : ℝ) (hmu : 0 < mu) (x : H) :
    ∃! p : H, p ∈ J[(mu • T)] x := by
  rcases resolvent_exists_of_maximal_monotone T hT mu hmu x with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact resolvent_unique_of_monotone hT.1 hmu hq hp

/-- Compatibility form of `resolvent_existsUnique_of_maximal_monotone` using
`identityAddScaled` membership. -/
theorem resolvent_exists_unique_of_maximal_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    {mu : ℝ} (hmu : 0 < mu) (x : H) :
    ∃! z : H, x ∈ T.identityAddScaled mu z := by
  rcases resolvent_existsUnique_of_maximal_monotone T hT mu hmu x with ⟨z, hz, huniq⟩
  refine ⟨z, (mem_resolvent_smul_iff T mu x z).mp hz, ?_⟩
  intro q hq
  exact huniq q ((mem_resolvent_smul_iff T mu x q).mpr hq)

/-- The canonical single-valued resolvent of a maximal monotone operator. -/
noncomputable def resolventMap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (mu : ℝ) (hmu : 0 < mu) : H → H :=
  fun x => Classical.choose
    (resolvent_existsUnique_of_maximal_monotone T hT mu hmu x)

/-- The canonical resolvent representative belongs to the resolvent. -/
theorem resolventMap_mem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (mu : ℝ) (hmu : 0 < mu) (x : H) :
    resolventMap T hT mu hmu x ∈ J[(mu • T)] x := by
  simpa [resolventMap] using
    (Classical.choose_spec (resolvent_existsUnique_of_maximal_monotone T hT mu hmu x)).1

/-- The scaled resolvent residual belongs to the underlying operator. -/
theorem resolventMap_residual_mem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (mu : ℝ) (hmu : 0 < mu) (x : H) :
    mu⁻¹ • (x - resolventMap T hT mu hmu x) ∈ T (resolventMap T hT mu hmu x) := by
  let z := resolventMap T hT mu hmu x
  have hJ : z ∈ J[(mu • T)] x := by
    simpa [z] using resolventMap_mem T hT mu hmu x
  have hscaled : x ∈ T.identityAddScaled mu z :=
    (mem_resolvent_smul_iff T mu x z).mp hJ
  rcases hscaled with ⟨u, hu, hxu⟩
  have hres : mu⁻¹ • (x - z) = u := by
    rw [← hxu, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hmu.ne', one_smul]
  change mu⁻¹ • (x - z) ∈ T z
  rw [hres]
  exact hu

/-- The set-valued resolvent is the singleton-valued operator induced by `resolventMap`. -/
theorem resolvent_eq_resolventMap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (mu : ℝ) (hmu : 0 < mu) :
    J[(mu • T)] = (resolventMap T hT mu hmu).toSetValuedOperator := by
  ext x z
  constructor
  · intro hz
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    exact resolvent_unique_of_monotone hT.1 hmu hz (resolventMap_mem T hT mu hmu x)
  · intro hz
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hz
    subst z
    exact resolventMap_mem T hT mu hmu x

/-- A total extension of the canonical resolvent map, retained for APIs that index by all real
parameters. Its value at a nonpositive parameter is the arbitrary value `0`. -/
noncomputable def maximal_monotone_resolvent_choice
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone) : ℝ → H → H :=
  fun rho y => if hrho : 0 < rho then resolventMap T hT rho hrho y else 0

theorem maximal_monotone_resolvent_choice_mem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SetValuedOperator H H) (hT : T.IsMaximalMonotone)
    (rho : ℝ) (hrho : 0 < rho) (y : H) :
    maximal_monotone_resolvent_choice T hT rho y ∈ J[(rho • T)] y := by
  rw [maximal_monotone_resolvent_choice, dif_pos hrho]
  exact resolventMap_mem T hT rho hrho y

/-- A maximal monotone operator admits a single-valued selection of its resolvent at a positive
parameter. -/
theorem resolvent_selection_exists_of_maximal_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    {mu : ℝ} (hmu : 0 < mu) :
    ∃ J : H → H, ∀ x : H, J x ∈ J[(mu • A)] x := by
  exact ⟨resolventMap A hA mu hmu, resolventMap_mem A hA mu hmu⟩

/-- A single-valued resolvent representative of a monotone operator fixes
exactly the zeros of the operator: `J x = x ↔ 0 ∈ A x`. -/
theorem resolvent_fixed_iff_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) (hmono : T.IsMonotone) {r : ℝ} (hr : 0 < r)
    (J : H → H) (hJ : ∀ x : H, J x ∈ J[(r • T)] x) (x : H) :
    J x = x ↔ (0 : H) ∈ T x := by
  constructor
  · intro hfix
    have hx : x ∈ J[(r • T)] x := by simpa [hfix] using hJ x
    rw [mem_resolvent_smul_iff] at hx
    dsimp [identityAddScaled] at hx
    rcases hx with ⟨a, ha, hxeq⟩
    have hsmul : r • a = 0 := by
      calc r • a = (x + r • a) - x := by abel
           _ = x - x := by rw [hxeq]
           _ = 0 := by abel
    have ha0 : a = 0 := by
      rcases smul_eq_zero.mp hsmul with hr0 | ha0
      · exact False.elim (hr.ne' hr0)
      · exact ha0
    simpa [ha0] using ha
  · intro hz
    have hx : x ∈ J[(r • T)] x := by
      rw [mem_resolvent_smul_iff]
      dsimp [identityAddScaled]
      exact ⟨(0 : H), hz, by simp⟩
    exact resolvent_unique_of_monotone hmono hr (hJ x) hx

/-- Any single-valued selection of the resolvent of a monotone operator is
nonexpansive: `‖J u - J v‖ ≤ ‖u - v‖`. -/
theorem resolvent_selection_nonexpansive_single
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) (hmono : T.IsMonotone) {r : ℝ} (hr : 0 < r)
    (J : H → H) (hJ : ∀ x : H, J x ∈ J[(r • T)] x) (u v : H) :
    ‖J u - J v‖ ≤ ‖u - v‖ := by
  have hu := hJ u
  have hv := hJ v
  rw [mem_resolvent_smul_iff] at hu hv
  dsimp [identityAddScaled] at hu hv
  rcases hu with ⟨a, ha, hu⟩
  rcases hv with ⟨b, hb, hv⟩
  have hd : u - v = (J u - J v) + r • (a - b) := by
    calc
      u - v = (J u + r • a) - (J v + r • b) := by rw [hu, hv]
      _ = (J u - J v) + r • (a - b) := by rw [smul_sub]; abel
  have hfirm : ‖J u - J v‖ ^ 2 ≤ inner ℝ (J u - J v) (u - v) := by
    rw [hd, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hm : 0 ≤ inner ℝ (J u - J v) (a - b) := by
      rw [real_inner_comm]
      exact hmono a ha b hb
    nlinarith [mul_nonneg hr.le hm]
  have hcs : inner ℝ (J u - J v) (u - v) ≤ ‖J u - J v‖ * ‖u - v‖ :=
    real_inner_le_norm _ _
  have hs : ‖J u - J v‖ ^ 2 ≤ ‖J u - J v‖ * ‖u - v‖ := hfirm.trans hcs
  by_cases hz : ‖J u - J v‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hp : 0 < ‖J u - J v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- Any parameter-indexed single-valued selection of the resolvent of a monotone
operator is nonexpansive at each positive parameter. -/
theorem resolvent_selection_nonexpansive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) (hmono : T.IsMonotone) (J : ℝ → H → H)
    (hJ : ∀ rho : ℝ, 0 < rho → ∀ x : H, J rho x ∈ J[(rho • T)] x)
    {r : ℝ} (hr : 0 < r) (u v : H) : ‖J r u - J r v‖ ≤ ‖u - v‖ := by
  exact resolvent_selection_nonexpansive_single T hmono hr (J r) (hJ r hr) u v

/-- Any single-valued selection of the resolvent of a monotone operator at a
positive parameter is firmly nonexpansive on the whole space (hence
`1 / 2`-averaged via `firmlyNonexpansiveOn_iff_averagedWith_half`). -/
theorem resolvent_selection_firmlyNonexpansiveOn
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {A : SetValuedOperator H H} (hAmono : A.IsMonotone) {mu : ℝ} (hmu : 0 < mu)
    (J : H → H) (hJ : ∀ x : H, J x ∈ J[(mu • A)] x) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ => J x) := by
  rw [firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner]
  intro x y
  have hx : x ∈ A.identityAddScaled mu (J x) := by
    exact (SetValuedOperator.mem_resolvent_smul_iff A mu x (J x)).mp (hJ x)
  have hy : y ∈ A.identityAddScaled mu (J y) := by
    exact (SetValuedOperator.mem_resolvent_smul_iff A mu y (J y)).mp (hJ y)
  rcases hx with ⟨a, ha, hxa⟩
  rcases hy with ⟨b, hb, hyb⟩
  have hdiff : x - y = (J x - J y) + mu • (a - b) := by
    calc
      x - y = (J x + mu • a) - y := congrArg (· - y) hxa.symm
      _ = (J x + mu • a) - (J y + mu • b) := congrArg ((J x + mu • a) - ·) hyb.symm
      _ = (J x - J y) + (mu • a - mu • b) := by abel
      _ = (J x - J y) + mu • (a - b) := by rw [smul_sub]
  rw [hdiff, inner_add_right, real_inner_smul_right]
  have hmono : 0 ≤ inner ℝ (J x - J y) (a - b) := by
    simpa [real_inner_comm] using hAmono a ha b hb
  have hself : inner ℝ (J x - J y) (J x - J y) = ‖J x - J y‖ ^ 2 := by simp
  rw [hself]
  nlinarith [mul_nonneg hmu.le hmono]

/-- The resolvent equation `J_lambda x = J_mu ((mu / lambda) • x +
(1 - mu / lambda) • J_lambda x)` and the parameter Lipschitz estimate
`‖J_lambda x - J_mu x‖ ≤ |lambda - mu| * ‖lambda⁻¹ • (x - J_lambda x)‖`
for positive parameters `lambda`, `mu`. -/
theorem resolvent_equation_and_parameter_estimate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) (hmono : T.IsMonotone)
    (J : ℝ → H → H)
    (hJ : ∀ rho : ℝ, 0 < rho → ∀ x : H, J rho x ∈ J[(rho • T)] x) :
    ∀ (lambda mu : ℝ), 0 < lambda → 0 < mu → ∀ x : H,
      J lambda x = J mu ((mu / lambda) • x + (1 - mu / lambda) • J lambda x) ∧
      ‖J lambda x - J mu x‖ ≤ |lambda - mu| * ‖lambda⁻¹ • (x - J lambda x)‖ := by
  intro lambda mu hlambda hmu x
  have hres : J lambda x = J mu ((mu / lambda) • x + (1 - mu / lambda) • J lambda x) := by
    have hp := hJ lambda hlambda x
    rw [mem_resolvent_smul_iff] at hp
    dsimp [identityAddScaled] at hp
    rcases hp with ⟨a, ha, hx⟩
    have hy : (mu / lambda) • x + (1 - mu / lambda) • J lambda x = J lambda x + mu • a := by
      calc
        (mu / lambda) • x + (1 - mu / lambda) • J lambda x =
            (mu / lambda) • (J lambda x + lambda • a) +
              (1 - mu / lambda) • J lambda x := by rw [hx]
        _ = J lambda x + mu • a := by
          rw [smul_add, smul_smul, div_mul_cancel₀ mu hlambda.ne']
          module
    have hp' : J lambda x ∈ J[(mu • T)]
        ((mu / lambda) • x + (1 - mu / lambda) • J lambda x) := by
      rw [mem_resolvent_smul_iff]
      dsimp [identityAddScaled]
      exact ⟨a, ha, hy.symm⟩
    exact resolvent_unique_of_monotone hmono hmu hp' (hJ mu hmu _)
  have hparam : ‖J lambda x - J mu x‖ ≤
      |lambda - mu| * ‖lambda⁻¹ • (x - J lambda x)‖ := by
    calc
      ‖J lambda x - J mu x‖ =
          ‖J mu ((mu / lambda) • x + (1 - mu / lambda) • J lambda x) - J mu x‖ := by
        rw [← hres]
      _ ≤ ‖((mu / lambda) • x + (1 - mu / lambda) • J lambda x) - x‖ :=
        resolvent_selection_nonexpansive T hmono J hJ hmu _ _
      _ = |lambda - mu| * ‖lambda⁻¹ • (x - J lambda x)‖ := by
        rw [show (mu / lambda) • x + (1 - mu / lambda) • J lambda x - x =
          (1 - mu / lambda) • (J lambda x - x) by module]
        rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
        rw [norm_smul, Real.norm_eq_abs]
        have hscalar : |1 - mu / lambda| = |lambda - mu| * |lambda⁻¹| := by
          calc
            |1 - mu / lambda| = |(lambda - mu) / lambda| := by
              congr 1
              field_simp [hlambda.ne']
            _ = |lambda - mu| / |lambda| := abs_div _ _
            _ = |lambda - mu| * |lambda|⁻¹ := by rw [div_eq_mul_inv]
            _ = |lambda - mu| * |lambda⁻¹| := by rw [abs_inv]
        rw [hscalar]
        ring
  exact ⟨hres, hparam⟩

/-- Averagedness of the two forward-backward ingredients: a resolvent selection
of a maximal monotone operator is `1 / 2`-averaged (firmly nonexpansive), and
the forward step `x ↦ x - mu • B x` is `mu / (2 * lam)`-averaged whenever `B`
is `lam`-cocoercive and `0 < mu < 2 * lam`. -/
theorem resolvent_selection_averaged_half_and_forward_step_averaged
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : SetValuedOperator H H) (B : H → H) (lam mu : ℝ)
    (hA : SetValuedOperator.IsMaximalMonotone A)
    (hB : CocoerciveOn lam Set.univ (fun x : Set.univ => B x))
    (hlam : 0 < lam) (hmu : 0 < mu ∧ mu < 2 * lam) :
    (∃ J : H → H, (∀ x, J x ∈ J[(mu • A)] x) ∧
      AveragedWith (1 / 2 : ℝ) (fun x : Set.univ => J x)) ∧
      AveragedWith (mu / (2 * lam)) (fun x : Set.univ => (x : H) - mu • B x) := by
  rcases hmu with ⟨hmu_pos, hmu_lt⟩
  constructor
  · rcases resolvent_selection_exists_of_maximal_monotone A hA hmu_pos with ⟨J, hJ⟩
    refine ⟨J, hJ, ?_⟩
    exact (firmlyNonexpansiveOn_iff_averagedWith_half (fun x : Set.univ => J x)).mp
      (resolvent_selection_firmlyNonexpansiveOn hA.1 hmu_pos J hJ)
  · have hforward :=
      (cocoerciveOn_iff_averagedWith_id_sub_smul hlam ⟨hmu_pos, hmu_lt⟩
        (fun x : Set.univ => B x)).mp hB
    exact hforward

/-- The maximal-monotone sum theorem (Bauschke--Combettes, Lemma 2.4): if `A` is
maximal monotone and `B` is monotone with full domain and a Lipschitz selection,
then the pointwise sum `A + B` is maximal monotone.

Promoted from `Attouch_Convergence_of_a_Relaxed_Inertial_Forward_Backward_Algorithm_for_Structured_Monotone_Inclusions_2019`
(`ext_thm_1`). -/
theorem maximal_monotone_add_of_monotone_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    (hB : B.IsMonotone) (hBdom : B.dom = Set.univ)
    (hBLipschitz : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y u v, u ∈ B x → v ∈ B y →
      ‖u - v‖ ≤ L * ‖x - y‖) :
    IsMaximalMonotone (fun x : H => A x + B x) := by
  classical
  rcases hBLipschitz with ⟨L, hL, hBLipschitz⟩
  have hBnonempty : ∀ x : H, (B x).Nonempty := by
    intro x
    apply (SetValuedOperator.mem_dom_iff B x).mp
    rw [hBdom]
    simp
  let b : H → H := fun x => Classical.choose (hBnonempty x)
  have hb_mem : ∀ x : H, b x ∈ B x := fun x => Classical.choose_spec (hBnonempty x)
  have hb_lip : ∀ x z : H, ‖b x - b z‖ ≤ L * ‖x - z‖ := by
    intro x z
    exact hBLipschitz x z (b x) (b z) (hb_mem x) (hb_mem z)
  have hsum_mono : IsMonotone (fun x : H => A x + B x) := by
    intro x y w hw w' hw'
    rcases hw with ⟨u, hu, v, hv, rfl⟩
    rcases hw' with ⟨u', hu', v', hv', rfl⟩
    rw [show (u + v) - (u' + v') = (u - u') + (v - v') by abel,
      inner_add_left]
    exact add_nonneg (hA.1 u hu u' hu') (hB v hv v' hv')
  let r : ℝ := (L + 1)⁻¹
  have hL1 : 0 < L + 1 := by linarith
  have hr : 0 < r := by
    dsimp [r]
    exact inv_pos.mpr hL1
  have hrl : r * L < 1 := by
    dsimp [r]
    rw [inv_mul_lt_iff₀ hL1]
    linarith
  let J : H → H := maximal_monotone_resolvent_choice A hA r
  have hJ : ∀ u : H, J u ∈ J[(r • A)] u :=
    maximal_monotone_resolvent_choice_mem A hA r hr
  have hJlip : LipschitzWith 1 J := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    simpa [dist_eq_norm] using
      resolvent_selection_nonexpansive_single A hA.1 hr J hJ u v
  let S : SetValuedOperator H H := fun x => r • (A x + B x)
  have hscaled_mono : S.IsMonotone := by
    intro x y u hu v hv
    change u ∈ r • (A x + B x) at hu
    change v ∈ r • (A y + B y) at hv
    rcases hu with ⟨u', hu', rfl⟩
    rcases hv with ⟨v', hv', rfl⟩
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg hr.le (hsum_mono u' hu' v' hv')
  have hsurj : ∀ y : H, ∃ x : H, ∃ u ∈ S x,
      y = x + u := by
    intro y
    let K : NNReal := ⟨r * L, mul_nonneg hr.le hL⟩
    have hK : K < 1 := by
      exact_mod_cast hrl
    have hcontract : ContractingWith K (fun z : H => J (y - r • b z)) := by
      refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
      intro x z
      simp only [dist_eq_norm]
      have hJbound : ‖J (y - r • b x) - J (y - r • b z)‖
          ≤ ‖(y - r • b x) - (y - r • b z)‖ := by
        simpa using hJlip.norm_sub_le (y - r • b x) (y - r • b z)
      calc
        ‖J (y - r • b x) - J (y - r • b z)‖
            ≤ ‖(y - r • b x) - (y - r • b z)‖ := hJbound
        _ = ‖r • (b z - b x)‖ := by
          congr 1
          module
        _ = r * ‖b z - b x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        _ = r * ‖b x - b z‖ := by rw [norm_sub_rev]
        _ ≤ r * (L * ‖x - z‖) := mul_le_mul_of_nonneg_left (hb_lip x z) hr.le
        _ = K * ‖x - z‖ := by
          change r * (L * ‖x - z‖) = (r * L) * ‖x - z‖
          ring
    let x : H := ContractingWith.fixedPoint (fun z : H => J (y - r • b z)) hcontract
    have hfix : J (y - r • b x) = x := by
      exact hcontract.fixedPoint_isFixedPt
    have hxres : x ∈ (r • A).resolvent (y - r • b x) := by
      simpa [hfix] using hJ (y - r • b x)
    have hxid : y - r • b x ∈ A.identityAddScaled r x := by
      exact (SetValuedOperator.mem_resolvent_smul_iff A r (y - r • b x) x).mp hxres
    rcases hxid with ⟨a, ha, hEq⟩
    refine ⟨x, r • (a + b x), ?_, ?_⟩
    · change r • (a + b x) ∈ S x
      exact ⟨a + b x, ⟨a, ha, b x, hb_mem x, rfl⟩, rfl⟩
    calc
      y = (y - r • b x) + r • b x := by module
      _ = (x + r • a) + r • b x := by rw [← hEq]
      _ = x + r • (a + b x) := by rw [smul_add]; module
  have hscaled_max : S.IsMaximalMonotone :=
    maximal_monotone_of_minty_surjective hscaled_mono hsurj
  have hback := positive_scaled_maximal_monotone
    (T := S) hscaled_max (inv_pos.mpr hr)
  simpa [S, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hback

/-! ### Resolvent distance between maximal monotone operators
Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/def_7 -/

/-- The resolvent-based distance `d_{λ,ρ}(A,B)` between maximal monotone operators `A`, `B`,
through their canonical resolvent representatives. -/
noncomputable def resolventDistance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (_hρ : 0 < ρ) : ℝ :=
  lam * sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧
    q = ‖(lam⁻¹ • (u - resolventMap A hA lam hlam u)) -
      (lam⁻¹ • (u - resolventMap B hB lam hlam u))‖}

/-- The resolvent representatives are nonexpansive, so their discrepancy on a bounded ball is
bounded above. -/
theorem resolventMap_discrepancy_bdd {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone) (lam rho : ℝ)
    (hlam : 0 < lam) : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ rho ∧
      q = ‖resolventMap A hA lam hlam u - resolventMap B hB lam hlam u‖} := by
  let JA := resolventMap A hA lam hlam
  let JB := resolventMap B hB lam hlam
  refine ⟨2 * rho + ‖JA 0 - JB 0‖, ?_⟩
  rintro q ⟨u, hu, rfl⟩
  have hJA : ‖JA u - JA 0‖ ≤ ‖u - 0‖ :=
    resolvent_selection_nonexpansive_single A hA.1 hlam JA
      (fun x => resolventMap_mem A hA lam hlam x) u 0
  have hJB : ‖JB u - JB 0‖ ≤ ‖u - 0‖ :=
    resolvent_selection_nonexpansive_single B hB.1 hlam JB
      (fun x => resolventMap_mem B hB lam hlam x) u 0
  have hdecomp : JA u - JB u = (JA u - JA 0) + (JA 0 - JB 0) + (JB 0 - JB u) := by
    module
  rw [hdecomp]
  calc
    ‖(JA u - JA 0) + (JA 0 - JB 0) + (JB 0 - JB u)‖
        ≤ ‖JA u - JA 0‖ + ‖JA 0 - JB 0‖ + ‖JB 0 - JB u‖ := by
          calc
            _ ≤ ‖(JA u - JA 0) + (JA 0 - JB 0)‖ + ‖JB 0 - JB u‖ := norm_add_le _ _
            _ ≤ _ := add_le_add_left (norm_add_le _ _) _
    _ ≤ 2 * rho + ‖JA 0 - JB 0‖ := by
      have hJA' : ‖JA u - JA 0‖ ≤ rho :=
        hJA.trans (by simpa only [sub_zero] using hu)
      have hJB' : ‖JB 0 - JB u‖ ≤ rho := by
        rw [norm_sub_rev]
        exact hJB.trans (by simpa only [sub_zero] using hu)
      nlinarith

private theorem resolventDistance_sup_pos_mul {S : Set ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hne : S.Nonempty) (hS : BddAbove S) :
    lam * sSup S = sSup ((fun q : ℝ => lam * q) '' S) := by
  have hIne : ((fun q : ℝ => lam * q) '' S).Nonempty := hne.image _
  have hIbdd : BddAbove ((fun q : ℝ => lam * q) '' S) := by
    rcases hS with ⟨b, hb⟩
    refine ⟨lam * b, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact mul_le_mul_of_nonneg_left (hb hq) hlam.le
  apply le_antisymm
  · have hdiv : sSup S ≤ sSup ((fun q : ℝ => lam * q) '' S) / lam := by
      apply csSup_le hne
      intro q hq
      apply (le_div_iff₀ hlam).mpr
      simpa [mul_comm] using le_csSup hIbdd ⟨q, hq, rfl⟩
    calc
      lam * sSup S ≤ lam * (sSup ((fun q : ℝ => lam * q) '' S) / lam) :=
        mul_le_mul_of_nonneg_left hdiv hlam.le
      _ = sSup ((fun q : ℝ => lam * q) '' S) := by field_simp
  · apply csSup_le hIne
    rintro _ ⟨q, hq, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup hS hq) hlam.le

/-- The resolvent form of the defining display,
`d_{λ,ρ}(A,B) = sup_{u ∈ B(0,ρ)} ‖J_λ^A u - J_λ^B u‖`. -/
theorem resolventDistance_eq_resolvent_sup {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    resolventDistance A B hA hB lam ρ hlam hρ =
      sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧
        q = ‖resolventMap A hA lam hlam u - resolventMap B hB lam hlam u‖} := by
  let JA := resolventMap A hA lam hlam
  let JB := resolventMap B hB lam hlam
  let Y : Set ℝ := {q | ∃ u : H, ‖u‖ ≤ ρ ∧
    q = ‖lam⁻¹ • (u - JA u) - lam⁻¹ • (u - JB u)‖}
  let R : Set ℝ := {q | ∃ u : H, ‖u‖ ≤ ρ ∧ q = ‖JA u - JB u‖}
  have hYne : Y.Nonempty := ⟨_, 0, by simpa using hρ.le, rfl⟩
  have hRbdd : BddAbove R := by
    simpa only [R, JA, JB] using resolventMap_discrepancy_bdd A B hA hB lam ρ hlam
  have hpoint : ∀ u : H,
      lam * ‖lam⁻¹ • (u - JA u) - lam⁻¹ • (u - JB u)‖ = ‖JA u - JB u‖ := by
    intro u
    have hlam0 : lam ≠ 0 := ne_of_gt hlam
    have hsub : lam⁻¹ • (u - JA u) - lam⁻¹ • (u - JB u) = lam⁻¹ • (JB u - JA u) := by
      module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), norm_sub_rev]
    field_simp
  have himage : R = (fun q : ℝ => lam * q) '' Y := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, hpoint u⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, hpoint u⟩
  have hYbdd : BddAbove Y := by
    rcases hRbdd with ⟨b, hb⟩
    refine ⟨b / lam, ?_⟩
    rintro q ⟨u, hu, rfl⟩
    apply (le_div_iff₀ hlam).mpr
    rw [mul_comm, hpoint]
    exact hb ⟨u, hu, rfl⟩
  unfold resolventDistance
  change lam * sSup Y = sSup R
  rw [himage, ← resolventDistance_sup_pos_mul hlam hYne hYbdd]

/-- The scaled-residual form is definitionally the value of `d_{λ,ρ}`. -/
theorem resolventDistance_eq_yosida_sup {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    resolventDistance A B hA hB lam ρ hlam hρ =
      lam * sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧
        q = ‖(lam⁻¹ • (u - resolventMap A hA lam hlam u)) -
          (lam⁻¹ • (u - resolventMap B hB lam hlam u))‖} := rfl



end SetValuedOperator
