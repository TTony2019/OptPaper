import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Analysis.Semicontinuity
import Foundation.Topology.Sequences

/-!
# The `Γ` and `Γ₀` classes of convex functions

The textbook classes of convex lower semicontinuous functions: `Γ(H)` for
extended-real-valued functions and `Γ₀(H)` for proper `]-∞,+∞]`-valued
functions with convexity imposed on the effective domain (so that properness
is built into the definition).
-/

open Filter Set

universe u

namespace ERealFunction

variable {H : Type u}

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Definition_9_2 -/

/-- Jensen convexity for an extended-real-valued function on a real module. -/
def IsConvex [AddCommMonoid H] [Module ℝ H] (f : H → EReal) : Prop :=
  ∀ ⦃x y : H⦄ ⦃a : ℝ⦄, 0 ≤ a → a ≤ 1 →
    f (a • x + (1 - a) • y) ≤ (a : EReal) * f x + (1 - a : EReal) * f y

/-- Definition 9.2: `gamma H` is the textbook class `Γ(ℋ)` of extended-real-valued functions on a
real sequential topological module that are convex and lower semicontinuous. -/
def gamma (H : Type u) [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H] :
    Set (H → EReal) :=
  {f | IsConvex f ∧ LowerSemicontinuous f}

notation "Γ(" H ")" => gamma H

/-- Membership in `Γ(H)` means Jensen convexity and lower semicontinuity. -/
theorem mem_gamma_iff [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H]
    (f : H → EReal) :
    f ∈ Γ(H) ↔ IsConvex f ∧ LowerSemicontinuous f := by
  rfl

/-- A proper function with a convex epigraph is Jensen convex.  The properness hypothesis is
needed at points where the function value is `⊤`, where the epigraph carries no information. -/
theorem isConvex_of_convex_epigraph [AddCommMonoid H] [Module ℝ H]
    {f : H → EReal} (hproper : IsProper f)
    (hconv : Convex ℝ (ERealFunction.epigraph f)) : IsConvex f := by
  intro x y a ha0 ha1
  by_cases hxt : f x = ⊤
  · by_cases ha0' : a = 0
    · subst a
      simp [hxt]
    · by_cases ha1' : a = 1
      · subst a
        rw [hxt]
        rw [← EReal.coe_one, ← EReal.coe_sub]
        simp
      · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha0')
        rw [hxt, EReal.coe_mul_top_of_pos hapos]
        rw [← EReal.coe_one, ← EReal.coe_sub]
        have hne : ((1 - a : ℝ) : EReal) * f y ≠ ⊥ := by
          intro hbot
          rcases (EReal.mul_eq_bot ((1 - a : ℝ) : EReal) (f y)).mp hbot with
            ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h3, _⟩ | ⟨h3', _⟩
          · exact (EReal.coe_ne_bot (1 - a)) h1
          · exact (hproper.1 y) h2
          · exact (EReal.coe_ne_top (1 - a)) h3
          · have hlt : (1 - a : ℝ) < 0 := by exact_mod_cast h3'
            linarith
        rw [EReal.top_add_of_ne_bot hne]
        exact le_top
  by_cases hyt : f y = ⊤
  · by_cases ha0' : a = 0
    · subst a
      simp [hyt]
    · by_cases ha1' : a = 1
      · subst a
        rw [hyt]
        rw [← EReal.coe_one, ← EReal.coe_sub]
        simp
      · have hbpos : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 ha1')
        rw [hyt]
        rw [← EReal.coe_one, ← EReal.coe_sub]
        rw [EReal.coe_mul_top_of_pos hbpos]
        have hne : (a : EReal) * f x ≠ ⊥ := by
          intro hbot
          rcases (EReal.mul_eq_bot (a : EReal) (f x)).mp hbot with
            ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h3, _⟩ | ⟨_, h4⟩
          · exact (EReal.coe_ne_bot a) h1
          · exact (hproper.1 x) h2
          · exact (EReal.coe_ne_top a) h3
          · exact hxt h4
        rw [EReal.add_top_of_ne_bot hne]
        exact le_top
  · have hx : (x, (f x).toReal) ∈ ERealFunction.epigraph f := by
      rw [ERealFunction.mem_epigraph_iff]
      exact EReal.le_coe_toReal hxt
    have hy : (y, (f y).toReal) ∈ ERealFunction.epigraph f := by
      rw [ERealFunction.mem_epigraph_iff]
      exact EReal.le_coe_toReal hyt
    have h := hconv (b := 1 - a) hx hy ha0 (by linarith) (by linarith)
    rw [ERealFunction.mem_epigraph_iff] at h
    norm_cast at h
    simpa [EReal.real_smul_def, EReal.coe_toReal hxt (hproper.1 x),
      EReal.coe_toReal hyt (hproper.1 y)] using h

/-- The Chapter 9 source-facing convexity owner is the same data as convexity on the whole space
in mathlib's `ConvexOn` API. -/
theorem IsConvex.convexOn_univ [AddCommMonoid H] [Module ℝ H] {f : H → EReal}
    (hf : IsConvex f) :
    _root_.ConvexOn ℝ (Set.univ : Set H) f := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have ha1 : a ≤ 1 := by
      linarith
    have hb_eq : b = 1 - a := by
      linarith
    subst b
    simpa [EReal.real_smul_def] using hf (x := x) (y := y) ha ha1

/-- Multiplying a member of `Γ(ℋ)` by a nonnegative real scalar again yields a member of
`Γ(ℋ)`. -/
theorem const_mul_mem_gamma_of_nonneg
    [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H]
    {f : H → EReal} (hf : f ∈ Γ(H)) {a : ℝ} (ha : 0 ≤ a) :
    (fun x ↦ (a : EReal) * f x) ∈ Γ(H) := by
  rw [mem_gamma_iff] at hf ⊢
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · intro x y b hb0 hb1
    calc
      (a : EReal) * f (b • x + (1 - b) • y) ≤
          (a : EReal) * ((b : EReal) * f x + (1 - b : EReal) * f y) := by
            exact mul_le_mul_of_nonneg_left (hf_convex hb0 hb1) (by exact_mod_cast ha)
      _ = (b : EReal) * ((a : EReal) * f x) + (1 - b : EReal) * ((a : EReal) * f y) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast ha) (EReal.coe_ne_top a)]
            congr 1 <;> ac_rfl
  · rw [lowerSemicontinuous_iff_le_liminf]
    intro x
    have haE : (0 : EReal) ≤ (a : EReal) := by
      exact_mod_cast ha
    calc
      (a : EReal) * f x ≤ (a : EReal) * Filter.liminf f (nhds x) :=
        (monotone_mul_left_of_nonneg haE) (hf_lsc.le_liminf x)
      _ = Filter.liminf (fun y ↦ (a : EReal) * f y) (nhds x) := by
        symm
        exact EReal.liminf_const_mul_of_nonneg_of_ne_top haE (EReal.coe_ne_top a)

/-- Helper for Definition 9.2: on a sequential space, lower semicontinuity is equivalent to the
sequential liminf inequality along convergent sequences. -/
theorem lowerSemicontinuous_iff_seq_tendsto_le_liminf [TopologicalSpace H] [SequentialSpace H]
    (f : H → EReal) :
    LowerSemicontinuous f ↔
      ∀ ⦃x : H⦄ ⦃u : ℕ → H⦄,
        Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf x u hu
    calc
      f x ≤ liminf f (nhds x) := hf.le_liminf x
      _ ≤ liminf f (Filter.map u atTop) := Filter.liminf_le_liminf_of_le hu
      _ = liminf (f ∘ u) atTop := by rw [Filter.liminf_comp]
  · intro hseq
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    apply IsSeqClosed.isClosed
    intro u x hu hx
    have h_liminf : f x ≤ liminf (f ∘ u) atTop := hseq hx
    have h_le_y : liminf (f ∘ u) atTop ≤ y := by
      refine Filter.liminf_le_of_le ?_ ?_
      · exact by isBoundedDefault
      · intro b hb
        let ⟨n, hbn, hun⟩ := (hb.and (Eventually.of_forall hu)).exists
        exact hbn.trans hun
    exact h_liminf.trans h_le_y

/-- Membership in `Γ(H)` is equivalent to Jensen convexity together with the sequential liminf
criterion for lower semicontinuity. -/
theorem mem_gamma_iff_seq_tendsto_le_liminf
    [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H]
    (f : H → EReal) :
    f ∈ Γ(H) ↔
      IsConvex f ∧
        ∀ ⦃x : H⦄ ⦃u : ℕ → H⦄,
          Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  rw [mem_gamma_iff, lowerSemicontinuous_iff_seq_tendsto_le_liminf]

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Definition_9_12 -/

variable [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

/-- Definition 9.12: `Γ₀(H)` is the set of lower semicontinuous convex `]-∞,+∞]`-valued
functions on `H`, with convexity imposed on the effective domain so that properness is built into
the definition. -/
def gammaZero (H : Type u) [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] :
    Set (H → Set.Ioi (⊥ : EReal)) :=
  {f | LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∧ ConvexOn f (effectiveDomain f)}

notation "Γ₀(" H ")" => gammaZero H

/-- Membership in `Γ₀(H)` means lower semicontinuity together with convexity on the effective
domain. -/
@[simp] theorem mem_gammaZero_iff {f : H → Set.Ioi (⊥ : EReal)} :
    f ∈ Γ₀(H) ↔
      LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∧ ConvexOn f (effectiveDomain f) :=
  Iff.rfl

/-- Precomposing a `Γ₀(K)` function with a continuous linear equivalence preserves membership in
`Γ₀`. -/
theorem mem_gammaZero_comp_continuousLinearEquiv
    {K : Type*} [TopologicalSpace K] [AddCommGroup K] [Module ℝ K]
    {f : K → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(K))
    (e : H ≃L[ℝ] K) :
    f ∘ e ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · simpa [Function.comp] using hf.1.comp e.continuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hf.2.nonempty with ⟨y, hy⟩
      refine ⟨e.symm y, ?_⟩
      rw [mem_effectiveDomain_iff] at hy ⊢
      simpa [Function.comp] using hy
    · intro x hx y hy a ha0 ha1
      have hx' : e x ∈ effectiveDomain f := by
        rw [mem_effectiveDomain_iff] at hx ⊢
        simpa [Function.comp] using hx
      have hy' : e y ∈ effectiveDomain f := by
        rw [mem_effectiveDomain_iff] at hy ⊢
        simpa [Function.comp] using hy
      simpa [Function.comp, map_add, map_smul] using
        hf.2.ineq (x := e x) hx' (y := e y) hy' (α := a) ha0 ha1

/-- A proper `EReal`-valued function, packaged pointwise as an `]-∞,+∞]`-valued function. -/
noncomputable abbrev properIoi (f : H → EReal) (hproper : IsProper f) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨f x, bot_lt_iff_ne_bot.mpr (hproper.1 x)⟩

/-- Coercing `properIoi f hproper` back to `EReal` recovers the original function. -/
@[simp] theorem properIoi_apply {X : Type*} {f : X → EReal} (hproper : IsProper f) (x : X) :
    (properIoi f hproper x : EReal) = f x :=
  rfl

/-- The canonical `EReal` coercion of `properIoi f hproper` is exactly `f`. -/
@[simp] theorem asEReal_properIoi {X : Type*} {f : X → EReal} (hproper : IsProper f) :
    (properIoi f hproper).asEReal = f :=
  rfl

/-- A real-valued member of `Γ(H)` yields a member of `Γ₀(H)` after the canonical coercion to
`]-∞,+∞]`. -/
theorem toEReal_mem_gammaZero_of_mem_gamma
    [SequentialSpace H] {f : H → ℝ} (hf : (fun x : H ↦ (f x : EReal)) ∈ gamma H) :
    f.toEReal ∈ Γ₀(H) := by
  rw [mem_gamma_iff] at hf
  rw [mem_gammaZero_iff]
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · simpa [Function.toEReal_apply] using hf_lsc
  · refine ⟨by simp [Function.effectiveDomain_toEReal], ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy a ha0 ha1
      simpa [Function.toEReal_apply] using hf_convex ha0.le ha1.le

/-- Outside the effective domain of an `]-∞,+∞]`-valued function, the coerced value is `⊤`. -/
private theorem asEReal_eq_top_of_not_mem_effectiveDomain
    {K : Type*} {f : K → Set.Ioi (⊥ : EReal)} {x : K} (hx : x ∉ effectiveDomain f) :
    f.asEReal x = ⊤ := by
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- Coercing a `Γ₀(K)` function to `EReal` gives a member of `γ(K)`. -/
theorem asEReal_mem_gamma_of_mem_gammaZero
    [SequentialSpace H] {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal ∈ gamma H := by
  rw [mem_gammaZero_iff] at hf
  rw [mem_gamma_iff]
  rcases hf with ⟨hf_lsc, hf_convex⟩
  refine ⟨?_, hf_lsc⟩
  intro x y a ha0 ha1
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    have hx1 : ((1 : ℝ) • x + (1 - (1 : ℝ)) • y) = x := by
      simp
    rw [hx1]
    have hzero : (1 - (1 : EReal)) * f.asEReal y = 0 := by
      have hcoef_zero : (1 - (1 : EReal)) = 0 := by
        exact EReal.sub_self (x := (1 : EReal)) (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
      rw [hcoef_zero]
      simp
    simp [Function.asEReal_apply, hzero]
  have h0a : (0 : ℝ) ≠ a := by
    intro h
    exact ha_zero h.symm
  have ha_pos : 0 < a := lt_of_le_of_ne ha0 h0a
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha1 ha_one
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  change f.asEReal (a • x + (1 - a) • y) ≤
    (a : EReal) * f.asEReal x + (1 - (a : EReal)) * f.asEReal y
  by_cases hx : x ∈ effectiveDomain f
  · by_cases hy : y ∈ effectiveDomain f
    · exact hf_convex.ineq hx hy ha_pos ha_lt_one
    · have hy_top : f.asEReal y = ⊤ :=
        asEReal_eq_top_of_not_mem_effectiveDomain hy
      have hx_term_ne_bot : (a : EReal) * f.asEReal x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inr (ne_of_gt (f x).2), Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha0)⟩
      rw [hy_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
      rw [EReal.add_top_of_ne_bot hx_term_ne_bot]
      exact le_top
  · have hx_top : f.asEReal x = ⊤ :=
      asEReal_eq_top_of_not_mem_effectiveDomain hx
    have hcoef_nonneg : (0 : EReal) ≤ 1 - (a : EReal) := by
      exact_mod_cast sub_nonneg.mpr ha1
    have hy_term_ne_bot : (1 - (a : EReal)) * f.asEReal y ≠ ⊥ := by
      have hcoef_ne_bot : (1 - (a : EReal)) ≠ ⊥ := by
        rw [hcoef_eq]
        exact EReal.coe_ne_bot (1 - a)
      have hcoef_ne_top : (1 - (a : EReal)) ≠ ⊤ := by
        rw [hcoef_eq]
        exact EReal.coe_ne_top (1 - a)
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl hcoef_ne_bot, Or.inr (ne_of_gt (f y).2), Or.inl hcoef_ne_top,
        Or.inl hcoef_nonneg⟩
    rw [hx_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos)]
    rw [EReal.top_add_of_ne_bot hy_term_ne_bot]
    exact le_top

/-- A proper member of `Γ(H)` becomes a member of `Γ₀(H)` through `properIoi`. -/
theorem properIoi_mem_gammaZero_of_mem_gamma
    [SequentialSpace H] {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    properIoi f hproper ∈ Γ₀(H) := by
  rw [mem_gamma_iff] at hf
  rw [mem_gammaZero_iff]
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · simpa using hf_lsc
  · refine ⟨?_, ?_, ?_⟩
    · simpa [effectiveDomain, dom] using hproper.2
    · intro x hx
      exact hx
    · intro x hx y hy a ha0 ha1
      simpa using hf_convex ha0.le ha1.le

/-- A function in `Γ₀(H)` is proper as an extended-real-valued function. -/
theorem isProper_of_mem_gammaZero {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    IsProper (fun x : H ↦ (f x : EReal)) := by
  refine ⟨?_, ConvexOn.nonempty hf.2⟩
  intro x hx
  simpa [hx] using (f x).2

/-- A member of `Γ₀(H)` has a convex real-height epigraph when viewed through its canonical
underlying `EReal`-valued function. -/
theorem convex_epigraph_asEReal_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Convex ℝ (epigraph f.asEReal) := by
  refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
  intro x y hx hy α hα0 hα1
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hf.2.ineq hx' hy' hα0 hα1

/-- The lower level sets of a function with convex real-height epigraph are convex. -/
theorem convex_lowerLevelSet_of_convex_epigraph (f : H → EReal) (ξ : ℝ)
    (hf : Convex ℝ (epigraph f)) :
    Convex ℝ (lowerLevelSet f ξ) := by
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  have hx_mem : (x, ξ) ∈ epigraph f := by
    rw [mem_epigraph_iff]
    exact hx
  have hy_mem : (y, ξ) ∈ epigraph f := by
    rw [mem_epigraph_iff]
    exact hy
  have hcombo_mem : (a • (x, ξ) + b • (y, ξ)) ∈ epigraph f :=
    (convex_iff_forall_pos.mp hf) hx_mem hy_mem ha hb hab
  change f (a • x + b • y) ≤ (ξ : EReal)
  rw [mem_epigraph_iff] at hcombo_mem
  have hcombo_le : f (a • x + b • y) ≤ ((a * ξ + b * ξ : ℝ) : EReal) := by
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
  have hξeq : ((a * ξ + b * ξ : ℝ) : EReal) = (ξ : EReal) := by
    congr 1
    rw [← add_mul]
    rw [hab, one_mul]
  exact hcombo_le.trans_eq hξeq

/-- Hence every real lower level set of a member of `Γ₀(H)` is convex. -/
theorem convex_lowerLevelSet_asEReal_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (ξ : ℝ) :
    Convex ℝ (lowerLevelSet f.asEReal ξ) :=
  convex_lowerLevelSet_of_convex_epigraph f.asEReal ξ (convex_epigraph_asEReal_of_mem_gammaZero hf)

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Proposition_9_30 -/

/-- The canonical additive identity on `]-∞,+∞]`-valued functions is the constant-zero
function. -/
noncomputable instance : Zero (H → Set.Ioi (⊥ : EReal)) :=
  ⟨fun _ ↦ ⟨0, EReal.bot_lt_coe 0⟩⟩

/-- The canonical source-facing addition on `]-∞,+∞]`-valued functions is pointwise addition. -/
noncomputable instance : Add (H → Set.Ioi (⊥ : EReal)) :=
  ⟨pointwiseAdd⟩

/-- The canonical source-facing additive structure on `]-∞,+∞]`-valued functions is pointwise
addition. -/
noncomputable instance : AddCommMonoid (H → Set.Ioi (⊥ : EReal)) where
  zero := 0
  add := (· + ·)
  add_assoc f g h := by
    funext x
    apply Subtype.ext
    change ((f x : EReal) + (g x : EReal)) + (h x : EReal) =
      (f x : EReal) + ((g x : EReal) + (h x : EReal))
    simp [add_assoc]
  zero_add f := by
    funext x
    apply Subtype.ext
    change (0 : EReal) + (f x : EReal) = (f x : EReal)
    simp
  add_zero f := by
    funext x
    apply Subtype.ext
    change (f x : EReal) + (0 : EReal) = (f x : EReal)
    simp
  nsmul := nsmulRec
  nsmul_zero := by
    intro f
    rfl
  nsmul_succ := by
    intro n f
    rfl
  add_comm f g := by
    funext x
    apply Subtype.ext
    change (f x : EReal) + (g x : EReal) = (g x : EReal) + (f x : EReal)
    simp [add_comm]

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Coercing the additive identity of `]-∞,+∞]`-valued functions to `EReal` recovers the constant
zero function. -/
@[simp] theorem zero_apply (x : H) :
    ((0 : H → Set.Ioi (⊥ : EReal)) x : EReal) = 0 :=
  rfl

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Coercing `f + g` to `EReal` recovers ordinary pointwise addition. -/
@[simp] theorem add_apply (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    ((f + g) x : EReal) = (f x : EReal) + (g x : EReal) :=
  rfl

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 9.30: the effective domain of the pointwise sum is exactly the
intersection of the effective domains of the summands. -/
theorem mem_effectiveDomain_pointwiseAdd_iff
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ effectiveDomain (f + g) ↔
      x ∈ effectiveDomain f ∧ x ∈ effectiveDomain g := by
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, mem_effectiveDomain_iff,
    add_apply, lt_top_iff_ne_top, lt_top_iff_ne_top, lt_top_iff_ne_top]
  exact EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2))
    (ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2))

omit [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] in
/-- If the effective domains of `f` and `g` meet, then the effective domain of `f + g` is
nonempty. -/
theorem effectiveDomain_add_nonempty_of_inter_nonempty
    (f g : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    (effectiveDomain (f + g)).Nonempty := by
  rcases hdom with ⟨x, hx, hgx⟩
  refine ⟨x, ?_⟩
  exact (mem_effectiveDomain_pointwiseAdd_iff f g x).2 ⟨hx, hgx⟩

variable [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

/-- Helper for Proposition 9.30: the sum of two lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
private theorem lowerSemicontinuous_add_ereal
    {g h : H → EReal} (hg : LowerSemicontinuous g) (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using
        (EReal.le_liminf_add :
          Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
            Filter.liminf (g + h) (nhds x))

/-- The pointwise sum of two members of `Γ₀(H)` again belongs to `Γ₀(H)` as soon as their
effective domains meet. -/
theorem pointwiseAdd_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal))
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    f + g ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · simpa [pointwiseAdd_apply] using lowerSemicontinuous_add_ereal hf.1 hg.1
  · refine ⟨effectiveDomain_add_nonempty_of_inter_nonempty f g hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    rcases (mem_effectiveDomain_pointwiseAdd_iff f g x).1 hx with ⟨hx_f, hx_g⟩
    rcases (mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy with ⟨hy_f, hy_g⟩
    calc
      (pointwiseAdd f g (α • x + (1 - α) • y) : EReal)
          = (f (α • x + (1 - α) • y) : EReal) +
              (g (α • x + (1 - α) • y) : EReal) := by
            simp [pointwiseAdd_apply]
      _ ≤ ((α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal))) +
            ((α : EReal) * (g x : EReal) + (((1 - α : ℝ) : EReal) * (g y : EReal))) := by
            exact add_le_add (hf.2.ineq hx_f hy_f hα hα_lt_one) (hg.2.ineq hx_g hy_g hα hα_lt_one)
      _ = (α : EReal) * ((f x : EReal) + (g x : EReal)) +
            (((1 - α : ℝ) : EReal) * ((f y : EReal) + (g y : EReal))) := by
            have hα_nonneg : (0 : EReal) ≤ (α : EReal) := EReal.coe_nonneg.mpr hα.le
            have hβ_nonneg : (0 : EReal) ≤ (((1 - α : ℝ) : EReal)) :=
              EReal.coe_nonneg.mpr (sub_nonneg.mpr hα_lt_one.le)
            have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
            have hβ_ne_top : (((1 - α : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top (1 - α)
            rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
              EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
            simp [add_assoc, add_left_comm]
      _ = (α : EReal) * (pointwiseAdd f g x : EReal) +
            (((1 - α : ℝ) : EReal) * (pointwiseAdd f g y : EReal)) := by
            simp [pointwiseAdd_apply]

end ERealFunction
