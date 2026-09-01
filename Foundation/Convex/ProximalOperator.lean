import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Convex.Gamma0
import Foundation.Convex.MoreauEnvelope
import Foundation.Convex.ArgminExistence
import Foundation.Optimization.Argmin
import Foundation.FixedPoint.Nonexpansive

/-!
# The proximity operator

The proximal points of a `]-∞,+∞]`-valued function, the single-valued proximity
operator `Prox[f, hf]` (defined when every base point has a unique proximal
point), and its scaled variant `Prox[γ, f, hf]`.
-/

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap08/Example_8_10 -/

/-- Example 8.10: the squared norm function `x ↦ ‖x‖ ^ 2` is uniformly convex on the whole space
of a real inner product space. -/
lemma uniformConvexOn_norm_sq [InnerProductSpace ℝ H] :
    UniformConvexOn (Set.univ : Set H) (fun r : ℝ ↦ r ^ 2) (fun x : H ↦ ‖x‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by
    linarith
  rw [hb_eq]
  have hgap :
      ‖a • x + (1 - a) • y‖ ^ 2 =
        a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 - a * (1 - a) * ‖x - y‖ ^ 2 := by
    linarith [norm_sq_affine_combination_add_weighted_norm_sub_sq x y a]
  exact le_of_eq hgap

/-- Example 8.10: the squared norm function `x ↦ ‖x‖ ^ 2` is strictly convex on the whole space of
a real inner product space. -/
theorem strictConvexOn_norm_sq [InnerProductSpace ℝ H] :
    StrictConvexOn ℝ Set.univ (fun x : H ↦ ‖x‖ ^ 2) := by
  refine uniformConvexOn_norm_sq.strictConvexOn ?_
  intro r hr
  exact sq_pos_of_ne_zero hr

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Definition_12_23 -/

/-- The unit proximal objective at `x`, whose minimizers are the proximal points of `f` at `x`. -/
noncomputable def proximalObjective (f : H → Set.Ioi (⊥ : EReal)) (x : H) : H → EReal :=
  fun y ↦ (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))

/-- Definition 12 23: the proximal points of `f` at `x` are the minimizers of the regularized
objective `y ↦ f y + (1 / 2) ‖x - y‖^2`. -/
def proximalPoints (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Set H :=
  Argmin (proximalObjective f x)

/-- Predicate form of Definition 12 23: `p` is a proximal point of `f` at `x` when it belongs to
the argmin set of the regularized objective at `x`. -/
abbrev IsProxPoint (f : H → Set.Ioi (⊥ : EReal)) (x p : H) : Prop :=
  p ∈ proximalPoints f x

/-- A point is proximal exactly when it realizes the value of the unit Moreau envelope. -/
theorem isProxPoint_iff_moreauEnvelope_eq (f : H → Set.Ioi (⊥ : EReal)) (x p : H) :
    IsProxPoint f x p ↔
      ({}^[⟨(1 : ℝ), by simp [Set.mem_Ioi]⟩] f) x =
        (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
  have hunit : (0 : ℝ) < 1 := by
    norm_num
  let γ : Set.Ioi (0 : ℝ) := ⟨(1 : ℝ), hunit⟩
  have hmoreau :
      ({}^[γ] f) x =
        ⨅ y : H, (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
    simpa [γ] using
      (moreauEnvelope_apply (f := f) (γ := γ) (x := x))
  have hobjective_iInf :
      iInf (proximalObjective f x) =
        ⨅ y : H, (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
    rfl
  have hiff :
      IsProxPoint f x p ↔
        ({}^[γ] f) x =
          (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    rw [IsProxPoint, proximalPoints, mem_argmin_iff_eq_sInf, sInf_range]
    constructor
    · intro hp
      rw [hmoreau, ← hobjective_iInf]
      simpa [proximalObjective] using hp.symm
    · intro hp
      rw [hmoreau, ← hobjective_iInf] at hp
      simpa [proximalObjective] using hp.symm
  simpa [γ] using hiff

/-- A function has a unique proximal point at every base point when the regularized objective
`y ↦ f y + (1 / 2) ‖x - y‖^2` admits a unique minimizer for every `x`. -/
def HasUniqueProxPoint (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ x : H, ∃! p : H, p ∈ proximalPoints f x

/-- The proximity operator attached to a function with unique proximal points sends `x` to its
unique proximal point. -/
noncomputable def proximityOperator (f : H → Set.Ioi (⊥ : EReal)) (hf : HasUniqueProxPoint f) :
    H → H :=
  fun x ↦ (hf x).choose

/-- The value of the proximity operator is a proximal point. -/
theorem proximityOperator_isProxPoint (f : H → Set.Ioi (⊥ : EReal))
    (hf : HasUniqueProxPoint f) (x : H) :
    IsProxPoint f x (proximityOperator f hf x) := by
  exact (hf x).choose_spec.1

/-- Any proximal point at `x` coincides with the value of the proximity operator at `x`. -/
theorem eq_proximityOperator_of_isProxPoint (f : H → Set.Ioi (⊥ : EReal))
    (hf : HasUniqueProxPoint f) {x p : H} (hp : IsProxPoint f x p) :
    p = proximityOperator f hf x := by
  exact ExistsUnique.unique (hf x) hp (proximityOperator_isProxPoint f hf x)

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/ProximityOperator -/

section

variable [InnerProductSpace ℝ H]
variable {f : H → Set.Ioi (⊥ : EReal)}

/-- Helper for ProximityOperator: the quadratic penalty in the proximal objective. -/
private noncomputable def quadraticPenalty (x : H) : H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2).toEReal

/-- Helper for ProximityOperator: the bundled proximal objective is the sum of `f` and the
quadratic penalty. -/
private noncomputable def proximalObjectiveIoi (x : H) : H → Set.Ioi (⊥ : EReal) :=
  f + quadraticPenalty x

/-- Helper for ProximityOperator: coercing the quadratic penalty back to `EReal` gives the
expected real formula. -/
@[simp] private theorem quadraticPenalty_apply (x y : H) :
    (quadraticPenalty (H := H) x y : EReal) = (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
  simp [quadraticPenalty]

/-- Helper for ProximityOperator: coercing the bundled proximal objective back to `EReal`
recovers the proximal objective from Definition 12.23. -/
@[simp] private theorem proximalObjectiveIoi_asEReal (x : H) :
    (proximalObjectiveIoi (f := f) x).asEReal = proximalObjective f x := by
  funext y
  simp [proximalObjectiveIoi, proximalObjective, quadraticPenalty]

/-- Helper for ProximityOperator: a continuous convex real-valued function on all of `H`
canonically yields a member of `Γ₀(H)` after applying `toEReal`. -/
private theorem real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨?_, ?_, ?_⟩
    · rw [Function.effectiveDomain_toEReal]
      exact (Set.univ_nonempty : (Set.univ : Set H).Nonempty)
    · rw [Function.effectiveDomain_toEReal]
    · intro x _ y _ a ha0 ha1
      have hreal :
          φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp : x ∈ (Set.univ : Set H)) (by simp : y ∈ (Set.univ : Set H))
            ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      have hcast :
          (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
            (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

/-- Helper for ProximityOperator: the quadratic penalty belongs to `Γ₀(H)`. -/
private theorem quadraticPenalty_mem_gammaZero (x : H) :
    quadraticPenalty (H := H) x ∈ Γ₀(H) := by
  have hcont : Continuous fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    exact continuous_const.mul ((continuous_norm.comp (continuous_const.sub continuous_id)).pow 2)
  have hbase : _root_.ConvexOn ℝ Set.univ (fun z : H ↦ ‖z‖ ^ 2) := by
    exact (strictConvexOn_norm_sq (H := H)).convexOn
  have hconv : _root_.ConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    have hsq :
        ‖x - (a • y + b • z)‖ ^ 2 ≤ a * ‖x - y‖ ^ 2 + b * ‖x - z‖ ^ 2 := by
      have hrewrite :
          x - (a • y + b • z) = a • (x - y) + b • (x - z) := by
        calc
          x - (a • y + b • z) = (a + b) • x - (a • y + b • z) := by simp [hab]
          _ = a • x + b • x - (a • y + b • z) := by rw [add_smul]
          _ = a • (x - y) + b • (x - z) := by
                rw [smul_sub, smul_sub]
                abel_nf
      simpa [hrewrite] using
        hbase.2 (by simp : x - y ∈ (Set.univ : Set H)) (by simp : x - z ∈ (Set.univ : Set H))
          ha hb hab
    have htarget :
        (1 / 2 : ℝ) * ‖x - (a • y + b • z)‖ ^ 2 ≤
          a * ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
      nlinarith
    simpa [smul_eq_mul] using htarget
  simpa [quadraticPenalty, Function.toEReal_apply] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (H := H)
      (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) hcont hconv

omit [InnerProductSpace ℝ H] in
/-- Helper for ProximityOperator: the quadratic penalty is finite everywhere. -/
private theorem effectiveDomain_quadraticPenalty_eq_univ (x : H) :
    effectiveDomain (quadraticPenalty (H := H) x) = Set.univ := by
  ext y
  simp [quadraticPenalty]

/-- Helper for ProximityOperator: the bundled proximal objective again belongs to `Γ₀(H)`. -/
private theorem proximalObjectiveIoi_mem_gammaZero_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    proximalObjectiveIoi (f := f) x ∈ Γ₀(H) := by
  have hquad : quadraticPenalty (H := H) x ∈ Γ₀(H) :=
    quadraticPenalty_mem_gammaZero (H := H) x
  rcases hf.2.nonempty with ⟨p, hp⟩
  have hdom : (effectiveDomain f ∩ effectiveDomain (quadraticPenalty (H := H) x)).Nonempty := by
    refine ⟨p, hp, ?_⟩
    simp [effectiveDomain_quadraticPenalty_eq_univ (H := H) x]
  simpa [proximalObjectiveIoi] using
    pointwiseAdd_mem_gammaZero f (quadraticPenalty (H := H) x) hf hquad hdom

/-- Helper for ProximityOperator: the real quadratic penalty is strictly convex on `Set.univ`. -/
private theorem quadraticPenalty_real_strictConvexOn_univ (x : H) :
    _root_.StrictConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
  have hbase' :
      _root_.StrictConvexOn ℝ Set.univ (((fun z : H ↦ ‖z‖ ^ 2) ∘ fun z : H ↦ z - x)) := by
    simpa [Function.comp, sub_eq_add_neg, add_comm] using
      (strictConvexOn_norm_sq (H := H)).translate_right (-x)
  have hbase :
      _root_.StrictConvexOn ℝ Set.univ (fun z : H ↦ ‖x - z‖ ^ 2) := by
    convert hbase' using 1
    ext z
    simp [Function.comp, norm_sub_rev]
  have hscaled :
      _root_.StrictConvexOn ℝ Set.univ (fun z : H ↦ (1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
    refine ⟨hbase.1, ?_⟩
    intro z₁ _ z₂ _ hz a b ha hb hab
    have hineq :
        ‖x - (a • z₁ + b • z₂)‖ ^ 2 <
          a * ‖x - z₁‖ ^ 2 + b * ‖x - z₂‖ ^ 2 :=
      hbase.2 (by simp) (by simp) hz ha hb hab
    calc
      (1 / 2 : ℝ) * ‖x - (a • z₁ + b • z₂)‖ ^ 2
          < (1 / 2 : ℝ) * (a * ‖x - z₁‖ ^ 2 + b * ‖x - z₂‖ ^ 2) := by
              exact mul_lt_mul_of_pos_left hineq (by positivity)
      _ = a * ((1 / 2 : ℝ) * ‖x - z₁‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z₂‖ ^ 2) := by
            ring
  exact hscaled

/-- Helper for ProximityOperator: strict convexity on `Set.univ` survives the everywhere-finite
`toEReal` coercion. -/
private theorem strictlyConvex_toEReal_of_strictConvexOn_univ
    {φ : H → ℝ} (hφ : _root_.StrictConvexOn ℝ Set.univ φ) :
    StrictlyConvex φ.toEReal := by
  intro x hx y hy hxy a ha0 ha1
  have hb0 : 0 < 1 - a := sub_pos.mpr ha1
  have hab : a + (1 - a) = 1 := by
    ring
  have hineq :
      φ (a • x + (1 - a) • y) < a * φ x + (1 - a) * φ y :=
    hφ.2 (by simp) (by simp) hxy ha0 hb0 hab
  have hineqE :
      (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) <
        (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  calc
    (φ.toEReal (a • x + (1 - a) • y) : EReal)
        = (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) := by
            simp [Function.toEReal_apply]
    _ < (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := hineqE
    _ = (a : EReal) * (φ.toEReal x : EReal) + (1 - a : EReal) * (φ.toEReal y : EReal) := by
          simp [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add]

/-- Helper for ProximityOperator: the quadratic penalty is strictly convex. -/
private theorem quadraticPenalty_strictlyConvex (x : H) :
    StrictlyConvex (quadraticPenalty (H := H) x) := by
  simpa [quadraticPenalty, Function.toEReal_apply] using
    strictlyConvex_toEReal_of_strictConvexOn_univ
      (H := H) (quadraticPenalty_real_strictConvexOn_univ (H := H) x)

/-- Helper for ProximityOperator: the real quadratic penalty is strongly convex with constant `1`
on all of `H`. -/
private theorem quadraticPenalty_strongConvexOn_univ (x : H) :
    StrongConvexOn (Set.univ : Set H) (1 : ℝ) (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
  rw [strongConvexOn_iff_convex]
  have hconst :
      _root_.ConvexOn ℝ (Set.univ : Set H) (fun _ : H ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2) :=
    convexOn_const _ convex_univ
  have hlin : _root_.ConvexOn ℝ (Set.univ : Set H) (fun y : H ↦ -⟪x, y⟫_ℝ) := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    apply le_of_eq
    have hreal :
        -⟪x, a • y + b • z⟫_ℝ = a * (-⟪x, y⟫_ℝ) + b * (-⟪x, z⟫_ℝ) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      ring
    simpa [smul_eq_mul] using hreal
  have haff :
      _root_.ConvexOn ℝ (Set.univ : Set H) (fun y : H ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2 - ⟪x, y⟫_ℝ) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hconst.add hlin
  convert haff using 1
  ext y
  rw [norm_sub_sq_real]
  ring

omit [InnerProductSpace ℝ H] in
/-- Helper for ProximityOperator: the quadratic penalty is supercoercive. -/
private theorem quadraticPenalty_supercoercive (x : H) :
    Supercoercive (quadraticPenalty (H := H) x).asEReal := by
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  let R : ℝ := max (2 * ‖x‖) (8 * (|ξ| + 1))
  have hR :
      ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop, R ≤ ‖y‖ := by
    simpa [R] using
      (Filter.Tendsto.eventually_ge_atTop
        (Filter.tendsto_comap : Filter.Tendsto (fun y : H ↦ ‖y‖)
          (Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop) Filter.atTop) R)
  filter_upwards [hR] with y hyR
  have hyx : 2 * ‖x‖ ≤ ‖y‖ := le_trans (le_max_left _ _) hyR
  have hybig : 8 * (|ξ| + 1) ≤ ‖y‖ := le_trans (le_max_right _ _) hyR
  have hy_pos : 0 < ‖y‖ := by
    have hpos : (0 : ℝ) < 8 * (|ξ| + 1) := by
      positivity
    exact lt_of_lt_of_le hpos hybig
  have hdist : ‖y‖ / 2 ≤ ‖x - y‖ := by
    have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (y - x) x
    have haux : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
      simpa [norm_sub_rev, add_comm] using htri
    nlinarith
  have htail : ξ < ‖y‖ / 8 := by
    have hbound : |ξ| + 1 ≤ ‖y‖ / 8 := by
      nlinarith
    linarith [le_abs_self ξ]
  have hquad :
      ‖y‖ / 8 ≤ ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := by
    have hsq : ‖y‖ ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by
      nlinarith [hdist]
    have hmul : (‖y‖ / 8) * ‖y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      nlinarith [hsq]
    exact (le_div_iff₀ hy_pos).2 hmul
  have hreal :
      ξ < ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := lt_of_lt_of_le htail hquad
  have hmul :
      (ξ : EReal) * ‖y‖ < (quadraticPenalty (H := H) x y : EReal) := by
    have hmul_real : ξ * ‖y‖ < (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      exact (lt_div_iff₀ hy_pos).1 hreal
    simpa [quadraticPenalty] using
      (show (((ξ * ‖y‖ : ℝ) : EReal)) <
          (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) from by
            exact_mod_cast hmul_real)
  exact (EReal.lt_div_iff (by exact_mod_cast hy_pos) (by simp)).2 hmul

/-- ProximityOperator: a function in `Γ₀(H)` has a unique proximal point at every base point. -/
theorem hasUniqueProxPoint_of_mem_gammaZero [CompleteSpace H]
    (hf : f ∈ Γ₀(H)) :
    HasUniqueProxPoint f := by
  intro x
  have hsum_gamma : proximalObjectiveIoi (f := f) x ∈ Γ₀(H) :=
    proximalObjectiveIoi_mem_gammaZero_of_mem_gammaZero hf x
  have hsum_super : Supercoercive (proximalObjectiveIoi (f := f) x).asEReal := by
    exact
      pointwiseAdd_supercoercive_of_mem_gammaZero f (quadraticPenalty (H := H) x) hf
        (quadraticPenalty_supercoercive (H := H) x)
  have hsum_coe : Coercive (proximalObjectiveIoi (f := f) x).asEReal :=
    coercive_of_supercoercive hsum_super
  have hsum_strict : StrictlyConvex (proximalObjectiveIoi (f := f) x) := by
    exact
      hf.2.add_strictlyConvex_effectiveDomain (quadraticPenalty_strictlyConvex (H := H) x)
  rcases existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex
    hsum_gamma hsum_coe hsum_strict with ⟨p, hp, hp_unique⟩
  refine ⟨p, ?_, ?_⟩
  · rw [proximalPoints, ← proximalObjectiveIoi_asEReal (H := H) x]
    exact hp
  · intro q hq
    rw [proximalPoints] at hq
    rw [← proximalObjectiveIoi_asEReal (H := H) x] at hq
    exact hp_unique q hq

/-- The proximity operator of a `Γ₀(H)` function, written `Prox[f, hf]`. The witness `f` is
inferred from `hf : f ∈ Γ₀(H)`, mirroring the positional Bauschke expansion (a named `(f := f)`
hole would break whenever the first argument is not literally named `f`). -/
notation "Prox[" f ", " hf "]" => proximityOperator f (hasUniqueProxPoint_of_mem_gammaZero hf)

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/ScaledProximityOperator -/

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The scaled proximity operator `Prox_{γ f}`, realized as the ordinary proximity operator of the
positively scaled function `γ • f`. The source-facing Lean notation is `Prox[γ, f, hf]`. -/
noncomputable def scaledProximityOperator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) : H → H :=
  proximityOperator (γ • f) (hasUniqueProxPoint_of_mem_gammaZero (f := γ • f) (smul_mem_gammaZero f hf γ))

/-- The scaled proximity operator `Prox_{γ f}`, written `Prox[γ, f, hf]`. -/
notation "Prox[" γ ", " f ", " hf "]" => scaledProximityOperator f hf γ

end ERealFunction

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Proposition_12_26 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 12 26: on the effective domain, the proximal objective is the
corresponding finite real-valued expression. -/
private theorem proximalObjective_eq_coe_toReal_add_quadratic
    (f : H → Set.Ioi (⊥ : EReal)) (x z : H) (hz : z ∈ effectiveDomain f) :
    proximalObjective f x z =
      (((f z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal) := by
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  rw [proximalObjective, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_add]
  simp

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 12 26: outside the effective domain, the proximal objective is `⊤`
because the function value itself is `⊤`. -/
private theorem proximalObjective_eq_top_of_not_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (x z : H) (hz : z ∉ effectiveDomain f) :
    proximalObjective f x z = ⊤ := by
  have hz_top : (f z : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz))
  rw [proximalObjective, hz_top, EReal.top_add_coe]

/-- Helper for Proposition 12 26: subtracting a point on the segment from `x` isolates the
residual `x - p` minus the scaled chord. -/
private theorem sub_lineMap_eq_sub_smul_sub (x p y : H) (α : ℝ) :
    x - AffineMap.lineMap p y α = (x - p) - α • (y - p) := by
  rw [sub_eq_add_neg, AffineMap.lineMap_apply_module', sub_eq_add_neg]
  abel_nf

/-- Helper for Proposition 12 26: a proximal point has finite function value. -/
private theorem mem_effectiveDomain_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x p : H}
    (hp : IsProxPoint f x p) :
    p ∈ effectiveDomain f := by
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  rcases hconv.nonempty with ⟨q, hq⟩
  have hobj_q_ne_top : proximalObjective f x q ≠ ⊤ := by
    rw [proximalObjective_eq_coe_toReal_add_quadratic f x q hq]
    exact EReal.coe_ne_top _
  by_contra hp_dom
  have hobj_p_top : proximalObjective f x p = ⊤ :=
    proximalObjective_eq_top_of_not_mem_effectiveDomain f x p hp_dom
  have hpq : proximalObjective f x p ≤ proximalObjective f x q := hp q
  rw [hobj_p_top] at hpq
  exact hobj_q_ne_top (top_le_iff.mp hpq)

/-- Helper for Proposition 12 26: along an interior segment from a proximal point toward an
effective-domain point, the source variational inequality holds up to a quadratic error term. -/
private theorem inner_add_le_add_quadratic_error_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x p : H}
    (hp : IsProxPoint f x p) {y : H} (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤
      (f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2 := by
  have hp_dom : p ∈ effectiveDomain f := mem_effectiveDomain_of_isProxPoint f hconv hp
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  let z : H := AffineMap.lineMap p y α
  have hz_eq : z = α • y + (1 - α) • p := by
    simpa [z, add_comm, add_left_comm, add_assoc] using (AffineMap.lineMap_apply_module p y α)
  have hz : z ∈ effectiveDomain f := by
    rw [hz_eq]
    exact hconv.convex_effectiveDomain hy hp_dom hα0.le (sub_nonneg.mpr hα1.le) (by linarith)
  have hmin :
      (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (f z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    have hpz : proximalObjective f x p ≤ proximalObjective f x z := hp z
    rw [proximalObjective_eq_coe_toReal_add_quadratic f x p hp_dom,
      proximalObjective_eq_coe_toReal_add_quadratic f x z hz] at hpz
    exact_mod_cast hpz
  have hconv_real :
      (f z : EReal).toReal ≤
        α * (f y : EReal).toReal + (1 - α) * (f p : EReal).toReal := by
    rw [hz_eq]
    exact hconv.toReal_convexOn_effectiveDomain.2 hy hp_dom hα0.le (sub_nonneg.mpr hα1.le)
      (by linarith)
  have hstep :
      (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (α * (f y : EReal).toReal + (1 - α) * (f p : EReal).toReal) +
          (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    exact le_trans hmin (add_le_add hconv_real le_rfl)
  have hnorm :
      ‖x - z‖ ^ 2 =
        ‖x - p‖ ^ 2 - 2 * α * ⟪y - p, x - p⟫_ℝ + α ^ 2 * ‖y - p‖ ^ 2 := by
    simpa [z, sub_lineMap_eq_sub_smul_sub, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hα0.le, pow_two, mul_assoc, mul_left_comm, mul_comm,
      real_inner_comm] using
      (norm_sub_sq_real (x - p) (α • (y - p)))
  have hscaled :
      α * (⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal) ≤
        α * (f y : EReal).toReal + (α ^ 2 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
    nlinarith [hstep, hnorm]
  have hscaled' :
      α * (⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal) ≤
        α * ((f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2) := by
    have hfactor :
        α * ((f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2) =
          α * (f y : EReal).toReal + (α ^ 2 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
      ring
    rwa [hfactor]
  exact le_of_mul_le_mul_left hscaled' hα0

/-- Helper for Proposition 12 26: proximal points satisfy the finite variational inequality
against every finite comparison point. -/
private theorem inner_add_toReal_le_toReal_of_isProxPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) {x p y : H}
    (hp : IsProxPoint f x p) (hy : y ∈ effectiveDomain f) :
    ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let δ : ℝ := min 1 (2 * ε / (‖y - p‖ ^ 2 + 1))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    positivity
  rcases exists_nat_one_div_lt hδ_pos with ⟨n, hn⟩
  let α : ℝ := 1 / (n + 1 : ℝ)
  have hα0 : 0 < α := by
    dsimp [α]
    positivity
  have hα_lt_δ : α < δ := by
    simpa [α] using hn
  have hα1 : α < 1 := lt_of_lt_of_le hα_lt_δ (min_le_left _ _)
  have hαε : (α / 2 : ℝ) * ‖y - p‖ ^ 2 ≤ ε := by
    have hα_lt :
        α < 2 * ε / (‖y - p‖ ^ 2 + 1) := lt_of_lt_of_le hα_lt_δ (min_le_right _ _)
    have hden_pos : 0 < ‖y - p‖ ^ 2 + 1 := by positivity
    have hmain : α * (‖y - p‖ ^ 2 + 1) < 2 * ε := by
      exact (lt_div_iff₀ hden_pos).mp hα_lt
    have hle :
        α * ‖y - p‖ ^ 2 ≤ α * (‖y - p‖ ^ 2 + 1) := by
      nlinarith [show 0 ≤ α by exact le_of_lt hα0]
    have haux : α * ‖y - p‖ ^ 2 < 2 * ε := lt_of_le_of_lt hle hmain
    nlinarith
  have herr :=
    inner_add_le_add_quadratic_error_of_isProxPoint f hconv hp hy hα0 hα1
  have hbound :
      (f y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2 ≤ (f y : EReal).toReal + ε := by
    nlinarith
  exact le_trans herr hbound

/-- Helper for Proposition 12 26: the textbook variational inequality forces `p` to have a
finite value under `f`. -/
private theorem mem_effectiveDomain_of_variational_inequality
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H)
    (hvar : ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal)) :
    p ∈ effectiveDomain f := by
  rcases hconv.nonempty with ⟨q, hq⟩
  by_contra hp_dom
  have hfp_top : (f p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp_dom))
  have hq_top : (f q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq)
  have hqineq : (⟪q - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f q : EReal) := hvar q
  rw [hfp_top] at hqineq
  have hqeq : (f q : EReal) = ⊤ := by
    simpa using hqineq
  exact hq_top hqeq

/-- Helper for Proposition 12 26: the textbook variational inequality implies that `p`
minimizes the proximal objective pointwise. -/
private theorem proximalObjective_le_of_forall_inner_add_le
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H)
    (hvar : ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal)) :
    ∀ y, proximalObjective f x p ≤ proximalObjective f x y := by
  have hp_dom : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_variational_inequality f hconv x p hvar
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hfy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hvar_real :
        ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
      have hcast :
          (((⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
            (((f y : EReal).toReal : ℝ) : EReal) := by
        have hyvar := hvar y
        rw [← EReal.coe_toReal hfp_top hfp_bot, ← EReal.coe_toReal hfy_top hfy_bot,
          ← EReal.coe_add] at hyvar
        exact hyvar
      exact_mod_cast hcast
    have hquad :
        (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
          (f y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      have hnorm :
          ‖x - y‖ ^ 2 =
            ‖x - p‖ ^ 2 - 2 * ⟪y - p, x - p⟫_ℝ + ‖y - p‖ ^ 2 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, real_inner_comm] using
          (norm_sub_sq_real (x - p) (y - p))
      nlinarith [hvar_real, hnorm]
    have hcast :
        (((f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal) ≤
          (((f y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
      exact_mod_cast hquad
    simpa [proximalObjective_eq_coe_toReal_add_quadratic f x p hp_dom,
      proximalObjective_eq_coe_toReal_add_quadratic f x y hy] using hcast
  · have hy_top : proximalObjective f x y = ⊤ :=
      proximalObjective_eq_top_of_not_mem_effectiveDomain f x y hy
    rw [hy_top]
    exact le_top

/-- Helper for Proposition 12 26: on the effective domain, a real-valued variational inequality
casts back to the corresponding `EReal` inequality. -/
private theorem ereal_inner_add_le_of_toReal
    (f : H → Set.Ioi (⊥ : EReal)) {x p y : H}
    (hp : p ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hreal : ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal) :
    (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal) := by
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hcast :
      (((⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_toReal hfp_top hfp_bot, EReal.coe_toReal hfy_top hfy_bot, EReal.coe_add] using
    hcast

/-- Proposition 12 26: if `f` is convex on its effective domain (in particular if `f ∈ Γ₀(H)`),
then a point `p` is a proximal point of `f` at `x` exactly when it satisfies the textbook
variational inequality `(12.25)`,
`⟪y - p, x - p⟫ + f(p) ≤ f(y)` for every `y ∈ H`. -/
theorem isProxPoint_iff_forall_inner_add_le
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) (x p : H) :
    IsProxPoint f x p ↔
      ∀ y, (⟪y - p, x - p⟫_ℝ : EReal) + (f p : EReal) ≤ (f y : EReal) := by
  constructor
  · intro hp y
    by_cases hy : y ∈ effectiveDomain f
    · have hp_dom : p ∈ effectiveDomain f := mem_effectiveDomain_of_isProxPoint f hconv hp
      have hreal :
          ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal :=
        inner_add_toReal_le_toReal_of_isProxPoint f hconv hp hy
      exact ereal_inner_add_le_of_toReal f hp_dom hy hreal
    · have hfy_top : (f y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
      rw [hfy_top]
      exact le_top
  · intro hvar
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
    intro y
    exact proximalObjective_le_of_forall_inner_add_le f hconv x p hvar y

end

end ERealFunction

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Proposition_12_28 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f g : H → Set.Ioi (⊥ : EReal)}






/-- Helper for Proposition 12 28: proximal points at two base points satisfy the pairwise firm
inequality that characterizes firm nonexpansiveness. -/
private theorem prox_point_pairwise_firm_inequality
    (hf : f ∈ Γ₀(H)) {x y p q : H} (hp : IsProxPoint f x p) (hq : IsProxPoint f y q) :
    ‖p - q‖ ^ (2 : ℕ) ≤ inner ℝ (p - q) (x - y) := by
  have hp_dom : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint f hf.2 hp
  have hq_dom : q ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint f hf.2 hq
  have hpq :
      ⟪q - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f q : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint f hf.2 hp hq_dom
  have hqp :
      ⟪p - q, y - q⟫_ℝ + (f q : EReal).toReal ≤ (f p : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint f hf.2 hq hp_dom
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hsub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hqpd : q - p = -d := by
    dsimp [d]
    abel_nf
  have hrewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by rw [hqpd]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by rw [hsub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hsum
  have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d] using hfinal

/-- Proposition 12 28 (1): for `f ∈ Γ₀(H)`, the proximity operator `Prox_f` is firmly
nonexpansive. -/
theorem proximityOperator_firmlyNonexpansive_of_mem_gammaZero (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (Prox[f, hf]) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  exact prox_point_pairwise_firm_inequality (f := f) hf
    (proximityOperator_isProxPoint (f := f) (hasUniqueProxPoint_of_mem_gammaZero hf) x)
    (proximityOperator_isProxPoint (f := f) (hasUniqueProxPoint_of_mem_gammaZero hf) y)

/-- Proposition 12.28 (2): for `f ∈ Γ₀(H)`, the residual map `Id - Prox_f` is firmly
nonexpansive. -/
theorem id_sub_proximityOperator_firmlyNonexpansive_of_mem_gammaZero (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (id - Prox[f, hf]) := by
  have hFirm :
      FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ Prox[f, hf] x) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      proximityOperator_firmlyNonexpansive_of_mem_gammaZero (f := f) hf
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  simpa [residualMap] using
    (firmlyNonexpansiveOn_residualMap_iff
      (Set.univ : Set H) (fun x : Set.univ ↦ Prox[f, hf] x)).2 hFirm

end

end ERealFunction
