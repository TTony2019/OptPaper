import Mathlib
import Mathlib.Tactic
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Fréchet and limiting subdifferentials

Sequential definitions of the Fréchet and Mordukhovich limiting subdifferentials for
extended-real-valued functions on real inner product spaces.
-/

open Filter
open scoped Topology

namespace ERealFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite-value Fréchet quotient, regarded as an extended real. -/
def frechetQuotient (f : E → EReal) (x v y : E) : EReal :=
  (((f y).toReal - (f x).toReal - inner ℝ v (y - x)) / ‖y - x‖ : ℝ)

/-- The Fréchet subdifferential of an extended-real-valued function. -/
def frechetSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v |
    x ∈ effectiveDom f ∧
      0 ≤ Filter.liminf
        (fun y : E ↦ frechetQuotient f x v y)
        (nhdsWithin x ({y | y ≠ x} ∩ effectiveDom f))}

/-- The Mordukhovich limiting subdifferential, defined by value-convergent sequences of
Fréchet subgradients. -/
def limitingSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v |
    x ∈ effectiveDom f ∧
      ∃ xs : ℕ → E, ∃ vs : ℕ → E,
        Tendsto xs atTop (nhds x) ∧
        Tendsto (fun n ↦ f (xs n)) atTop (nhds (f x)) ∧
        (∀ n, vs n ∈ frechetSubdifferential f (xs n)) ∧
        Tendsto vs atTop (nhds v)}

/-- Domain of the limiting subdifferential. -/
def limitingSubdifferentialDomain (f : E → EReal) : Set E :=
  {x | (limitingSubdifferential f x).Nonempty}

/-- Critical points with respect to the limiting subdifferential. -/
def limitingCriticalPoints (f : E → EReal) : Set E :=
  {x | (0 : E) ∈ limitingSubdifferential f x}

/-- Every Fréchet subgradient is a limiting subgradient. -/
theorem frechetSubdifferential_subset_limitingSubdifferential (f : E → EReal) (x : E) :
    frechetSubdifferential f x ⊆ limitingSubdifferential f x := by
  exact fun v hv ↦
    ⟨hv.1, ⟨fun _ ↦ x, fun _ ↦ v, tendsto_const_nhds, tendsto_const_nhds,
      fun _ ↦ hv, tendsto_const_nhds⟩⟩

/-- A point in the limiting-subdifferential domain has a finite function value. -/
theorem finite_at_mem_limitingSubdifferentialDomain {f : E → EReal} {x : E}
    (hx : x ∈ limitingSubdifferentialDomain f) :
    f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  rcases hx with ⟨v, hv⟩
  exact (mem_effectiveDom_iff f x).mp hv.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Adding a finite real-valued term does not change the effective domain. -/
@[simp] theorem mem_effectiveDom_addReal_iff (f : E → EReal) (h : E → ℝ) (x : E) :
    x ∈ effectiveDom (fun y ↦ EReal.sumWithTopBotAsTop (f y) (h y : EReal)) ↔
      x ∈ effectiveDom f := by
  rw [mem_effectiveDom_iff_exists_real, mem_effectiveDom_iff_exists_real,
    EReal.exists_real_eq_sumWithTopBotAsTop_iff]
  constructor
  · rintro ⟨hfx, _⟩
    exact hfx
  · intro hfx
    exact ⟨hfx, ⟨h x, rfl⟩⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The real value of an extended-real function after adding a finite real-valued term. -/
theorem addReal_toReal_of_mem_effectiveDom {f : E → EReal} {h : E → ℝ} {x : E}
    (hx : x ∈ effectiveDom f) :
    (EReal.sumWithTopBotAsTop (f x) (h x : EReal)).toReal = (f x).toReal + h x := by
  rcases (mem_effectiveDom_iff_exists_real f x).mp hx with ⟨r, hr⟩
  rw [hr]
  change (((r : EReal) + (h x : EReal)).toReal = ((r : EReal).toReal + h x))
  rw [← EReal.coe_add]
  exact EReal.toReal_coe (r + h x)

private theorem finite_ereal_tendsto_iff_toReal {α : Type*} {l : Filter α}
    {z : α → EReal} {a : EReal}
    (hz : ∀ i, z i ≠ ⊤ ∧ z i ≠ ⊥) (ha : a ≠ ⊤ ∧ a ≠ ⊥) :
    Tendsto z l (nhds a) ↔ Tendsto (fun i ↦ (z i).toReal) l (nhds a.toReal) := by
  constructor
  · intro hzT
    exact (EReal.tendsto_toReal ha.1 ha.2).comp hzT
  · intro hreal
    have hcoe :
        Tendsto (fun i ↦ (((z i).toReal : ℝ) : EReal)) l
          (nhds (((a.toReal : ℝ) : EReal))) :=
      (EReal.tendsto_coe).2 hreal
    have hsrc : (fun i ↦ (((z i).toReal : ℝ) : EReal)) = z := by
      funext i
      exact EReal.coe_toReal (hz i).1 (hz i).2
    have htgt : (((a.toReal : ℝ) : EReal)) = a := EReal.coe_toReal ha.1 ha.2
    simpa [hsrc, htgt] using hcoe

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem addReal_value_tendsto
    {f : E → EReal} {h : E → ℝ} {xs : ℕ → E} {x : E}
    (hxs_eff : ∀ n, xs n ∈ effectiveDom f) (hx_eff : x ∈ effectiveDom f)
    (hf : Tendsto (fun n ↦ f (xs n)) atTop (nhds (f x)))
    (hh : Tendsto (fun n ↦ h (xs n)) atTop (nhds (h x))) :
    Tendsto (fun n ↦ EReal.sumWithTopBotAsTop (f (xs n)) (h (xs n) : EReal)) atTop
      (nhds (EReal.sumWithTopBotAsTop (f x) (h x : EReal))) := by
  have hfxs_fin : ∀ n, f (xs n) ≠ ⊤ ∧ f (xs n) ≠ ⊥ :=
    fun n ↦ (mem_effectiveDom_iff f (xs n)).mp (hxs_eff n)
  have hfx_fin : f x ≠ ⊤ ∧ f x ≠ ⊥ := (mem_effectiveDom_iff f x).mp hx_eff
  have hsum_eff : ∀ n,
      xs n ∈ effectiveDom (fun y ↦ EReal.sumWithTopBotAsTop (f y) (h y : EReal)) :=
    fun n ↦ (mem_effectiveDom_addReal_iff f h (xs n)).2 (hxs_eff n)
  have hsum_x_eff :
      x ∈ effectiveDom (fun y ↦ EReal.sumWithTopBotAsTop (f y) (h y : EReal)) :=
    (mem_effectiveDom_addReal_iff f h x).2 hx_eff
  have hsum_fin : ∀ n,
      EReal.sumWithTopBotAsTop (f (xs n)) (h (xs n) : EReal) ≠ ⊤ ∧
        EReal.sumWithTopBotAsTop (f (xs n)) (h (xs n) : EReal) ≠ ⊥ :=
    fun n ↦ (mem_effectiveDom_iff _ _).mp (hsum_eff n)
  have hsum_x_fin :
      EReal.sumWithTopBotAsTop (f x) (h x : EReal) ≠ ⊤ ∧
        EReal.sumWithTopBotAsTop (f x) (h x : EReal) ≠ ⊥ :=
    (mem_effectiveDom_iff _ _).mp hsum_x_eff
  apply (finite_ereal_tendsto_iff_toReal hsum_fin hsum_x_fin).2
  simpa only [addReal_toReal_of_mem_effectiveDom hx_eff,
    addReal_toReal_of_mem_effectiveDom (f := f) (h := h) (hxs_eff _)] using
    ((finite_ereal_tendsto_iff_toReal hfxs_fin hfx_fin).1 hf).add hh

private theorem liminf_nonneg_add_tendsto_zero {α : Type*} {l : Filter α}
    (q : α → EReal) (r : α → ℝ) (hq : 0 ≤ Filter.liminf q l)
    (hr : Tendsto r l (nhds 0)) :
    0 ≤ Filter.liminf (fun a ↦ q a + (r a : EReal)) l := by
  by_cases hne : l.NeBot
  · haveI : l.NeBot := hne
    have hrE : Tendsto (fun a ↦ (r a : EReal)) l (nhds (0 : EReal)) :=
      (EReal.tendsto_coe).2 hr
    have hlimr : Filter.liminf (fun a ↦ (r a : EReal)) l = 0 :=
      Filter.Tendsto.liminf_eq hrE
    calc
      (0 : EReal) = (0 : EReal) + 0 := by simp
      _ ≤ Filter.liminf q l + Filter.liminf (fun a ↦ (r a : EReal)) l := by
        rw [hlimr]
        exact add_le_add hq le_rfl
      _ ≤ Filter.liminf (fun a ↦ q a + (r a : EReal)) l := by
        simpa [Pi.add_apply] using
          (EReal.le_liminf_add (u := q) (v := fun a ↦ (r a : EReal)) (f := l))
  · have hlbot : l = ⊥ := (Filter.not_neBot).mp hne
    subst l
    simp

section SmoothPerturbation

variable [CompleteSpace E]

private theorem smooth_remainder_quotient_tendsto_zero
    {h : E → ℝ} {g : E} {x : E} (hh : HasGradientAt h g x) :
    Tendsto
      (fun y : E ↦ (h y - h x - inner ℝ g (y - x)) / ‖y - x‖)
      (nhdsWithin x {y | y ≠ x}) (nhds 0) := by
  have ho :
      (fun y ↦ h y - h x - inner ℝ g (y - x)) =o[nhds x] (fun y ↦ y - x) :=
    hasGradientAt_iff_isLittleO.mp hh
  have hoNorm :
      (fun y ↦ h y - h x - inner ℝ g (y - x)) =o[nhds x]
        (fun y ↦ ‖y - x‖) :=
    ho.norm_right
  exact (Asymptotics.IsLittleO.tendsto_div_nhds_zero hoNorm).mono_left nhdsWithin_le_nhds

/-- A Fréchet subgradient remains a subgradient after a differentiable finite perturbation. -/
theorem frechetSubdifferential_addReal_of_mem
    {f : E → EReal} {h : E → ℝ} {g x w : E}
    (hh : HasGradientAt h g x) (hw : w ∈ frechetSubdifferential f x) :
    w + g ∈ frechetSubdifferential
      (fun y ↦ EReal.sumWithTopBotAsTop (f y) (h y : EReal)) x := by
  constructor
  · exact (mem_effectiveDom_addReal_iff f h x).2 hw.1
  · let S : Set E := {y | y ≠ x} ∩ effectiveDom f
    let rem : E → ℝ := fun y ↦
      (h y - h x - inner ℝ g (y - x)) / ‖y - x‖
    have hset :
        ({y : E | y ≠ x} ∩
            effectiveDom (fun z ↦ EReal.sumWithTopBotAsTop (f z) (h z : EReal))) = S := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_addReal_iff, S]
    have hrem : Tendsto rem (nhdsWithin x S) (nhds 0) :=
      (smooth_remainder_quotient_tendsto_zero hh).mono_left
        (nhdsWithin_mono x fun _ hy ↦ hy.1)
    have hpert :
        0 ≤ Filter.liminf
          (fun y : E ↦ frechetQuotient f x w y + ((rem y : ℝ) : EReal))
          (nhdsWithin x S) :=
      liminf_nonneg_add_tendsto_zero (fun y : E ↦ frechetQuotient f x w y) rem
        (by simpa [S] using hw.2) hrem
    have hquot :
        ∀ᶠ y in nhdsWithin x S,
          frechetQuotient
              (fun z ↦ EReal.sumWithTopBotAsTop (f z) (h z : EReal)) x (w + g) y =
            frechetQuotient f x w y + ((rem y : ℝ) : EReal) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro y hy
      change frechetQuotient
          (fun z ↦ EReal.sumWithTopBotAsTop (f z) (h z : EReal)) x (w + g) y =
        frechetQuotient f x w y + ((rem y : ℝ) : EReal)
      unfold frechetQuotient rem
      rw [addReal_toReal_of_mem_effectiveDom hy.2,
        addReal_toReal_of_mem_effectiveDom hw.1]
      exact_mod_cast (by rw [inner_add_left]; ring_nf)
    have hlim := Filter.liminf_congr hquot
    simpa [S, hset, hlim] using hpert

/-- A limiting subgradient remains a limiting subgradient after a continuously differentiable
finite perturbation, expressed using an explicit continuous gradient field. -/
theorem limitingSubdifferential_addReal_of_mem
    {f : E → EReal} {h : E → ℝ} {g : E → E} {x w : E}
    (hh : ∀ y, HasGradientAt h (g y) y) (hg : Continuous g)
    (hw : w ∈ limitingSubdifferential f x) :
    w + g x ∈ limitingSubdifferential
      (fun y ↦ EReal.sumWithTopBotAsTop (f y) (h y : EReal)) x := by
  rcases hw with ⟨hx_eff, xs, ws, hxs, hf, hwsFrechet, hws⟩
  have hxs_eff : ∀ n, xs n ∈ effectiveDom f := fun n ↦ (hwsFrechet n).1
  have hhT : Tendsto h (nhds x) (nhds (h x)) := (hh x).continuousAt
  have hhxs : Tendsto (fun n ↦ h (xs n)) atTop (nhds (h x)) := hhT.comp hxs
  exact ⟨(mem_effectiveDom_addReal_iff f h x).2 hx_eff, xs,
    fun n ↦ ws n + g (xs n), hxs,
    addReal_value_tendsto hxs_eff hx_eff hf hhxs,
    fun n ↦ frechetSubdifferential_addReal_of_mem (hh (xs n)) (hwsFrechet n),
    hws.add ((hg.tendsto x).comp hxs)⟩

end SmoothPerturbation

section L2Product

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A Fréchet subgradient lifts through the first projection of a Hilbert product. -/
theorem frechetSubdifferential_comp_fst
    {f : E → EReal} {x v : E} {y : F}
    (hv : v ∈ frechetSubdifferential f x) :
    WithLp.toLp 2 (v, 0) ∈ frechetSubdifferential
      (fun z : WithLp 2 (E × F) ↦ f z.fst) (WithLp.toLp 2 (x, y)) := by
  let z0 : WithLp 2 (E × F) := WithLp.toLp 2 (x, y)
  let v0 : WithLp 2 (E × F) := WithLp.toLp 2 (v, 0)
  change v0 ∈ frechetSubdifferential (fun z : WithLp 2 (E × F) ↦ f z.fst) z0
  constructor
  · change x ∈ effectiveDom f
    exact hv.1
  · apply (Filter.le_liminf_iff).2
    intro a ha
    have hbase := (Filter.le_liminf_iff).1 hv.2 a ha
    have hbaseGood :
        ∀ᶠ u in nhdsWithin x (effectiveDom f),
          u = x ∨ a < frechetQuotient f x v u := by
      rw [eventually_nhdsWithin_iff] at hbase ⊢
      filter_upwards [hbase] with u hu
      intro hu_eff
      by_cases hux : u = x
      · exact Or.inl hux
      · exact Or.inr (hu ⟨hux, hu_eff⟩)
    have hfst :
        Tendsto (fun z : WithLp 2 (E × F) ↦ z.fst)
          (nhdsWithin z0
            ({z | z ≠ z0} ∩ effectiveDom (fun z : WithLp 2 (E × F) ↦ f z.fst)))
          (nhdsWithin x (effectiveDom f)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · exact
          ((WithLp.continuous_fst (p := 2) (α := E) (β := F)).tendsto z0).mono_left
            nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact hz.2
    filter_upwards [hfst.eventually hbaseGood, self_mem_nhdsWithin] with z hzGood hz
    by_cases hzx : z.fst = x
    · simpa [frechetQuotient, z0, v0, hzx, WithLp.prod_inner_apply] using ha
    · have hbaseQuot : a < frechetQuotient f x v z.fst := hzGood.resolve_left hzx
      let N : ℝ :=
        (f z.fst).toReal - (f x).toReal - inner ℝ v (z.fst - x)
      have hbaseQuot' : a < ((N / ‖z.fst - x‖ : ℝ) : EReal) := by
        simpa [frechetQuotient, N] using hbaseQuot
      have hfstNormPos : 0 < ‖z.fst - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
      have hz_ne : z ≠ z0 := hz.1
      have hprodNormPos : 0 < ‖z - z0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne)
      have hnormLe : ‖z.fst - x‖ ≤ ‖z - z0‖ := by
        simpa [z0] using
          WithLp.norm_fst_le (α := E) (β := F) (p := 2) (z - z0)
      have hprodQuot :
          frechetQuotient (fun q : WithLp 2 (E × F) ↦ f q.fst) z0 v0 z =
            ((N / ‖z - z0‖ : ℝ) : EReal) := by
        unfold frechetQuotient
        simp only [z0, v0, WithLp.prod_inner_apply, WithLp.toLp_fst]
        simp [N]
      rw [hprodQuot]
      by_cases hN : 0 ≤ N
      · exact ha.trans_le (EReal.coe_nonneg.mpr (div_nonneg hN hprodNormPos.le))
      · exact hbaseQuot'.trans_le (by
          exact_mod_cast
            ((div_le_div_iff₀ hfstNormPos hprodNormPos).2 (by
              have hNneg : N < 0 := lt_of_not_ge hN
              nlinarith)))

/-- A limiting subgradient lifts through the first projection of a Hilbert product. -/
theorem limitingSubdifferential_comp_fst
    {f : E → EReal} {x v : E} {y : F}
    (hv : v ∈ limitingSubdifferential f x) :
    WithLp.toLp 2 (v, 0) ∈ limitingSubdifferential
      (fun z : WithLp 2 (E × F) ↦ f z.fst) (WithLp.toLp 2 (x, y)) := by
  rcases hv with ⟨hx_eff, xs, vs, hxs, hf, hfrechet, hvs⟩
  refine ⟨?_, fun n ↦ WithLp.toLp 2 (xs n, y),
    fun n ↦ WithLp.toLp 2 (vs n, 0), ?_, ?_, ?_, ?_⟩
  · change x ∈ effectiveDom f
    exact hx_eff
  · have hpair : Tendsto (fun n ↦ (xs n, y)) atTop (nhds (x, y)) := by
      rw [Prod.tendsto_iff]
      exact ⟨hxs, tendsto_const_nhds⟩
    exact
      ((WithLp.prod_continuous_toLp (p := 2) (α := E) (β := F)).tendsto (x, y)).comp
        hpair
  · simpa using hf
  · intro n
    exact frechetSubdifferential_comp_fst (hfrechet n)
  · have hpair : Tendsto (fun n ↦ (vs n, (0 : F))) atTop (nhds (v, 0)) := by
      rw [Prod.tendsto_iff]
      exact ⟨hvs, tendsto_const_nhds⟩
    exact
      ((WithLp.prod_continuous_toLp (p := 2) (α := E) (β := F)).tendsto (v, 0)).comp
        hpair

end L2Product

private theorem tendsto_atTop_diagonal_of_rows
    {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    (target : ℕ → A) (limit : A) (row : ℕ → ℕ → A)
    (htarget : Tendsto target atTop (nhds limit))
    (hrow : ∀ n, Tendsto (row n) atTop (nhds (target n))) :
    ∃ pick : ℕ → ℕ, Tendsto (fun n ↦ row n (pick n)) atTop (nhds limit) := by
  classical
  rcases Filter.exists_antitone_basis (nhds limit) with ⟨B, hB⟩
  let C : ℕ → Set A := fun j ↦ interior (B j)
  have hC_mem : ∀ j, C j ∈ nhds limit := by
    intro j
    have hBj : B j ∈ nhds limit := (hB.mem_iff).2 ⟨j, subset_rfl⟩
    exact (isOpen_interior).mem_nhds ((mem_interior_iff_mem_nhds).2 hBj)
  have hC_open : ∀ j, IsOpen (C j) := fun _ ↦ isOpen_interior
  have hC_subset : ∀ j, C j ⊆ B j := fun _ ↦ interior_subset
  let Nrow : ℕ → ℕ → ℕ := fun n j ↦
    if hmem : target n ∈ C j then
      Classical.choose (Filter.eventually_atTop.mp ((hrow n) ((hC_open j).mem_nhds hmem)))
    else 0
  have hNrow :
      ∀ n j, target n ∈ C j → ∀ k, k ≥ Nrow n j → row n k ∈ C j := by
    intro n j hmem
    dsimp [Nrow]
    rw [dif_pos hmem]
    exact Classical.choose_spec
      (Filter.eventually_atTop.mp ((hrow n) ((hC_open j).mem_nhds hmem)))
  let pick : ℕ → ℕ := fun n ↦ (Finset.range (n + 1)).sup (fun j ↦ Nrow n j)
  refine ⟨pick, ?_⟩
  intro U hU
  rcases (hB.mem_iff).1 hU with ⟨j, hBjU⟩
  have hCU : C j ⊆ U := subset_trans (hC_subset j) hBjU
  rcases Filter.eventually_atTop.mp (htarget (hC_mem j)) with ⟨Ntarget, hNtarget⟩
  refine Filter.eventually_atTop.mpr ⟨max j Ntarget, ?_⟩
  intro n hn
  have hnj : j ≤ n := le_trans (le_max_left _ _) hn
  have hnT : Ntarget ≤ n := le_trans (le_max_right _ _) hn
  have htarget_mem : target n ∈ C j := hNtarget n hnT
  have hj_mem : j ∈ Finset.range (n + 1) := by simp [hnj]
  have hpick_ge : Nrow n j ≤ pick n := by
    dsimp [pick]
    exact Finset.le_sup hj_mem
  exact hCU (hNrow n j htarget_mem (pick n) hpick_ge)

/-- Closed-graph criterion for the limiting subdifferential. -/
theorem limitingSubdifferential_closedGraph {f : E → EReal} {x v : E}
    (xs vs : ℕ → E)
    (hx_eff : x ∈ effectiveDom f)
    (hsub : ∀ n, vs n ∈ limitingSubdifferential f (xs n))
    (hxv : Tendsto (fun n ↦ (xs n, vs n)) atTop (nhds (x, v)))
    (hf : Tendsto (fun n ↦ f (xs n)) atTop (nhds (f x))) :
    v ∈ limitingSubdifferential f x := by
  classical
  choose rowX rowV hrowX hrowF hrowFrechet hrowV using
    (fun n ↦ (hsub n).2)
  have htarget :
      Tendsto (fun n ↦ ((xs n, vs n), f (xs n))) atTop
        (nhds ((x, v), f x)) := Filter.Tendsto.prodMk_nhds hxv hf
  have hrows : ∀ n,
      Tendsto (fun k ↦ ((rowX n k, rowV n k), f (rowX n k))) atTop
        (nhds ((xs n, vs n), f (xs n))) := by
    intro n
    exact Filter.Tendsto.prodMk_nhds (Filter.Tendsto.prodMk_nhds (hrowX n) (hrowV n))
      (hrowF n)
  rcases tendsto_atTop_diagonal_of_rows
      (fun n ↦ ((xs n, vs n), f (xs n)))
      ((x, v), f x)
      (fun n k ↦ ((rowX n k, rowV n k), f (rowX n k)))
      htarget hrows with ⟨pick, hdiagProd⟩
  refine ⟨hx_eff, ?_⟩
  refine ⟨fun n ↦ rowX n (pick n), fun n ↦ rowV n (pick n), ?_, ?_, ?_, ?_⟩
  · have hdiagPair :
        Tendsto (fun n ↦ (rowX n (pick n), rowV n (pick n))) atTop (nhds x ×ˢ nhds v) :=
      Filter.Tendsto.fst (by simpa [nhds_prod_eq] using hdiagProd)
    exact Filter.Tendsto.fst hdiagPair
  · exact Filter.Tendsto.snd (by simpa [nhds_prod_eq] using hdiagProd)
  · intro n
    exact hrowFrechet n (pick n)
  · have hdiagPair :
        Tendsto (fun n ↦ (rowX n (pick n), rowV n (pick n))) atTop (nhds x ×ˢ nhds v) :=
      Filter.Tendsto.fst (by simpa [nhds_prod_eq] using hdiagProd)
    exact Filter.Tendsto.snd hdiagPair

/-- Fermat's rule for the limiting subdifferential. -/
theorem zero_mem_limitingSubdifferential_of_isMinOn {f : E → EReal} {x : E}
    (hx : x ∈ effectiveDom f) (hmin : IsMinOn f Set.univ x) :
    (0 : E) ∈ limitingSubdifferential f x := by
  apply frechetSubdifferential_subset_limitingSubdifferential
  constructor
  · exact hx
  · refine Filter.le_liminf_of_le
      (f := nhdsWithin x ({y | y ≠ x} ∩ effectiveDom f))
      (u := fun y : E ↦ frechetQuotient f x (0 : E) y)
      (a := (0 : EReal)) (by isBoundedDefault) ?_
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro y hy
    rcases hy with ⟨_hy_ne, hy_eff⟩
    have hx_ne_bot : f x ≠ ⊥ := ((mem_effectiveDom_iff f x).mp hx).2
    have hy_ne_top : f y ≠ ⊤ := ((mem_effectiveDom_iff f y).mp hy_eff).1
    have hxy : f x ≤ f y := by
      have hmin_all : ∀ y, f x ≤ f y := by
        simpa [IsMinOn, IsMinFilter] using hmin
      exact hmin_all y
    have hreal : (f x).toReal ≤ (f y).toReal :=
      EReal.toReal_le_toReal hxy hx_ne_bot hy_ne_top
    unfold frechetQuotient
    exact EReal.coe_nonneg.mpr (div_nonneg (by simpa using sub_nonneg.mpr hreal) (norm_nonneg _))

end

end ERealFunction
