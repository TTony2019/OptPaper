import Mathlib
import Mathlib.Tactic
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Analysis.LimitingSubdifferential
import Foundation.Analysis.Semicontinuity

open Filter
open scoped Topology BigOperators

namespace BotCsetnek2015

abbrev EuclideanSpace (m : ℕ) := _root_.EuclideanSpace ℝ (Fin m)

open ERealFunction

/-- Foundation definition recalled for the paper notation `dom f`. -/
recall ERealFunction.dom

/-- Foundation definition recalled for proper extended-real-valued functions. -/
recall ERealFunction.IsProper

/-- Add a real-valued perturbation to an extended-real-valued function. -/
noncomputable def erealAddReal (a : EReal) (r : ℝ) : EReal :=
  EReal.sumWithTopBotAsTop a (r : EReal)

/-- The extended-real objective `f + h` used throughout the paper. -/
noncomputable def objectiveSum {m : ℕ} (f : EuclideanSpace m → EReal)
    (h : EuclideanSpace m → ℝ) : EuclideanSpace m → EReal :=
  fun x ↦ erealAddReal (f x) (h x)

/-- Foundation's finite-value Frechet quotient in the paper's notation. -/
recall ERealFunction.frechetQuotient

/--
The Frechet/viscosity subdifferential from the paper.  Since Lean's `EReal`
also contains `⊥`, the formal domain guard uses `effectiveDom`, matching the
paper's codomain `]-∞,+∞]` and keeping the quotient on finite values.
-/
recall ERealFunction.frechetSubdifferential

/--
The limiting/Mordukhovich subdifferential: limits of Frechet subgradients
along value-convergent sequences at finite effective-domain points.
-/
recall ERealFunction.limitingSubdifferential

/-- Domain of the limiting subdifferential. -/
recall ERealFunction.limitingSubdifferentialDomain

/-- Limiting critical points: `0 ∈ partial f x`. -/
recall ERealFunction.limitingCriticalPoints

/-- The inclusion of the Frechet subdifferential in the limiting subdifferential. -/
theorem frechetSubdifferential_subset_limitingSubdifferential {m : ℕ}
    (f : EuclideanSpace m → EReal) (x : EuclideanSpace m) :
    frechetSubdifferential f x ⊆ limitingSubdifferential f x := by
  exact fun v hv ↦
    ⟨hv.1, ⟨fun _ ↦ x, fun _ ↦ v, tendsto_const_nhds, tendsto_const_nhds,
      fun _ ↦ hv, tendsto_const_nhds⟩⟩

theorem tendsto_atTop_diagonal_of_rows
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
  have hj_mem : j ∈ Finset.range (n + 1) := by
    simp [hnj]
  have hpick_ge : Nrow n j ≤ pick n := by
    dsimp [pick]
    exact Finset.le_sup hj_mem
  exact hCU (hNrow n j htarget_mem (pick n) hpick_ge)

/-- Closed graph criterion for the limiting subdifferential used in the paper. -/
theorem limitingSubdifferential_closed_graph {m : ℕ}
    {f : EuclideanSpace m → EReal} {x : EuclideanSpace m} {v : EuclideanSpace m}
    (xs : ℕ → EuclideanSpace m) (vs : ℕ → EuclideanSpace m)
    (hx_eff : x ∈ ERealFunction.effectiveDom f)
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

/-- Fermat rule in the nonsmooth limiting-subdifferential setting. -/
theorem fermat_rule_limitingSubdifferential {m : ℕ} {f : EuclideanSpace m → EReal}
    {x : EuclideanSpace m} (hx : x ∈ ERealFunction.effectiveDom f)
    (hmin : IsMinOn f Set.univ x) :
    (0 : EuclideanSpace m) ∈ limitingSubdifferential f x := by
  apply frechetSubdifferential_subset_limitingSubdifferential
  constructor
  · exact hx
  · refine Filter.le_liminf_of_le
      (f := nhdsWithin x ({y | y ≠ x} ∩ ERealFunction.effectiveDom f))
      (u := fun y : EuclideanSpace m ↦
        frechetQuotient f x (0 : EuclideanSpace m) y)
      (a := (0 : EReal)) (by isBoundedDefault) ?_
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro y hy
    rcases hy with ⟨_hy_ne, hy_eff⟩
    have hx_ne_bot : f x ≠ ⊥ := ((ERealFunction.mem_effectiveDom_iff f x).mp hx).2
    have hy_ne_top : f y ≠ ⊤ := ((ERealFunction.mem_effectiveDom_iff f y).mp hy_eff).1
    have hmin_all : ∀ y, f x ≤ f y := by
      simpa [IsMinOn, IsMinFilter] using hmin
    have hxy : f x ≤ f y := hmin_all y
    have hreal : (f x).toReal ≤ (f y).toReal :=
      EReal.toReal_le_toReal hxy hx_ne_bot hy_ne_top
    have hnum :
        0 ≤ (f y).toReal - (f x).toReal -
          inner ℝ (0 : EuclideanSpace m) (y - x) := by
      simpa using sub_nonneg.mpr hreal
    unfold frechetQuotient
    exact EReal.coe_nonneg.mpr (div_nonneg hnum (norm_nonneg _))

theorem objectiveSum_effectiveDom_iff {m : ℕ}
    (f : EuclideanSpace m → EReal) (h : EuclideanSpace m → ℝ)
    (x : EuclideanSpace m) :
    x ∈ ERealFunction.effectiveDom (objectiveSum f h) ↔
      x ∈ ERealFunction.effectiveDom f := by
  rw [ERealFunction.mem_effectiveDom_iff_exists_real,
    ERealFunction.mem_effectiveDom_iff_exists_real]
  unfold objectiveSum erealAddReal
  rw [EReal.exists_real_eq_sumWithTopBotAsTop_iff]
  constructor
  · rintro ⟨hfx, _⟩
    exact hfx
  · intro hfx
    exact ⟨hfx, ⟨h x, rfl⟩⟩

theorem objectiveSum_toReal_of_effective {m : ℕ}
    {f : EuclideanSpace m → EReal} {h : EuclideanSpace m → ℝ}
    {x : EuclideanSpace m} (hx : x ∈ ERealFunction.effectiveDom f) :
    (objectiveSum f h x).toReal = (f x).toReal + h x := by
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real f x).mp hx with ⟨r, hr⟩
  unfold objectiveSum erealAddReal
  rw [hr]
  change (((r : EReal) + (h x : EReal)).toReal = ((r : EReal).toReal + h x))
  rw [← EReal.coe_add]
  exact EReal.toReal_coe (r + h x)

theorem finite_ereal_tendsto_iff_toReal {α : Type*} {l : Filter α}
    {z : α → EReal} {a : EReal}
    (hz : ∀ i, z i ≠ ⊤ ∧ z i ≠ ⊥) (ha : a ≠ ⊤ ∧ a ≠ ⊥) :
    Tendsto z l (nhds a) ↔
      Tendsto (fun i ↦ (z i).toReal) l (nhds a.toReal) := by
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
    have htgt : (((a.toReal : ℝ) : EReal)) = a :=
      EReal.coe_toReal ha.1 ha.2
    simpa [hsrc, htgt] using hcoe

theorem objectiveSum_value_tendsto_iff {m : ℕ}
    {f : EuclideanSpace m → EReal} {h : EuclideanSpace m → ℝ}
    {xs : ℕ → EuclideanSpace m} {x : EuclideanSpace m}
    (hxs_eff : ∀ n, xs n ∈ ERealFunction.effectiveDom f)
    (hx_eff : x ∈ ERealFunction.effectiveDom f)
    (hhx : Tendsto (fun n ↦ h (xs n)) atTop (nhds (h x))) :
    Tendsto (fun n ↦ objectiveSum f h (xs n)) atTop
        (nhds (objectiveSum f h x)) ↔
      Tendsto (fun n ↦ f (xs n)) atTop (nhds (f x)) := by
  have hfxs_fin : ∀ n, f (xs n) ≠ ⊤ ∧ f (xs n) ≠ ⊥ := by
    intro n
    exact (ERealFunction.mem_effectiveDom_iff f (xs n)).mp (hxs_eff n)
  have hfx_fin : f x ≠ ⊤ ∧ f x ≠ ⊥ :=
    (ERealFunction.mem_effectiveDom_iff f x).mp hx_eff
  have hobj_xs_eff :
      ∀ n, xs n ∈ ERealFunction.effectiveDom (objectiveSum f h) := by
    intro n
    exact (objectiveSum_effectiveDom_iff f h (xs n)).2 (hxs_eff n)
  have hobj_x_eff : x ∈ ERealFunction.effectiveDom (objectiveSum f h) :=
    (objectiveSum_effectiveDom_iff f h x).2 hx_eff
  have hobj_xs_fin :
      ∀ n, objectiveSum f h (xs n) ≠ ⊤ ∧ objectiveSum f h (xs n) ≠ ⊥ := by
    intro n
    exact (ERealFunction.mem_effectiveDom_iff (objectiveSum f h) (xs n)).mp
      (hobj_xs_eff n)
  have hobj_x_fin : objectiveSum f h x ≠ ⊤ ∧ objectiveSum f h x ≠ ⊥ :=
    (ERealFunction.mem_effectiveDom_iff (objectiveSum f h) x).mp hobj_x_eff
  constructor
  · intro hobj
    have hobjReal :
        Tendsto (fun n ↦ (objectiveSum f h (xs n)).toReal) atTop
          (nhds (objectiveSum f h x).toReal) :=
      (finite_ereal_tendsto_iff_toReal hobj_xs_fin hobj_x_fin).1 hobj
    have hsumReal :
        Tendsto (fun n ↦ (f (xs n)).toReal + h (xs n)) atTop
          (nhds ((f x).toReal + h x)) := by
      have hs_eq :
          (fun n ↦ (objectiveSum f h (xs n)).toReal) =
            (fun n ↦ (f (xs n)).toReal + h (xs n)) := by
        funext n
        exact objectiveSum_toReal_of_effective (hxs_eff n)
      have hx_eq : (objectiveSum f h x).toReal = (f x).toReal + h x :=
        objectiveSum_toReal_of_effective hx_eff
      simpa [hs_eq, hx_eq] using hobjReal
    have hsub :
        Tendsto (fun n ↦ ((f (xs n)).toReal + h (xs n)) - h (xs n)) atTop
          (nhds (((f x).toReal + h x) - h x)) :=
      hsumReal.sub hhx
    have hfReal :
        Tendsto (fun n ↦ (f (xs n)).toReal) atTop (nhds (f x).toReal) := by
      convert hsub using 1
      · ext n
        ring_nf
      · ring_nf
    exact (finite_ereal_tendsto_iff_toReal hfxs_fin hfx_fin).2 hfReal
  · intro hfVal
    have hfReal :
        Tendsto (fun n ↦ (f (xs n)).toReal) atTop (nhds (f x).toReal) :=
      (finite_ereal_tendsto_iff_toReal hfxs_fin hfx_fin).1 hfVal
    have hsumReal :
        Tendsto (fun n ↦ (f (xs n)).toReal + h (xs n)) atTop
          (nhds ((f x).toReal + h x)) :=
      hfReal.add hhx
    have hobjReal :
        Tendsto (fun n ↦ (objectiveSum f h (xs n)).toReal) atTop
          (nhds (objectiveSum f h x).toReal) := by
      have hs_eq :
          (fun n ↦ (objectiveSum f h (xs n)).toReal) =
            (fun n ↦ (f (xs n)).toReal + h (xs n)) := by
        funext n
        exact objectiveSum_toReal_of_effective (hxs_eff n)
      have hx_eq : (objectiveSum f h x).toReal = (f x).toReal + h x :=
        objectiveSum_toReal_of_effective hx_eff
      simpa [hs_eq, hx_eq] using hsumReal
    exact (finite_ereal_tendsto_iff_toReal hobj_xs_fin hobj_x_fin).2 hobjReal

theorem gradient_tendsto_of_contDiff_one {m : ℕ}
    {h : EuclideanSpace m → ℝ} (hh : ContDiff ℝ 1 h)
    {xs : ℕ → EuclideanSpace m} {x : EuclideanSpace m}
    (hxs : Tendsto xs atTop (nhds x)) :
    Tendsto (fun n ↦ gradient h (xs n)) atTop (nhds (gradient h x)) := by
  let e := EuclideanSpace.equiv (Fin m) ℝ
  have hc : Tendsto (fun n ↦ e (gradient h (xs n))) atTop
      (nhds (e (gradient h x))) := by
    rw [tendsto_pi_nhds]
    intro i
    let vi : EuclideanSpace m := EuclideanSpace.single (𝕜 := ℝ) i 1
    have hfd : Continuous (fun y ↦ fderiv ℝ h y) :=
      hh.continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have happ_cont : Continuous fun y ↦ (fderiv ℝ h y) vi :=
      (continuous_clm_apply.mp hfd) vi
    have happ := (happ_cont.tendsto x).comp hxs
    have hdiff : ∀ y, DifferentiableAt ℝ h y :=
      hh.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    convert happ using 1
    · ext n
      dsimp
      calc
        e (gradient h (xs n)) i = inner ℝ (gradient h (xs n)) vi := by
          symm
          simpa [e, vi, EuclideanSpace.equiv] using
            (EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1 : ℝ)
              (gradient h (xs n)))
        _ = (fderiv ℝ h (xs n)) vi := inner_gradient_left (hdiff (xs n))
    · apply congrArg nhds
      calc
        e (gradient h x) i = inner ℝ (gradient h x) vi := by
          symm
          simpa [e, vi, EuclideanSpace.equiv] using
            (EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1 : ℝ)
              (gradient h x))
        _ = (fderiv ℝ h x) vi := inner_gradient_left (hdiff x)
  have hback := e.symm.continuous.tendsto (e (gradient h x)) |>.comp hc
  simpa [e] using hback

theorem liminf_nonneg_add_tendsto_zero {α : Type*} {l : Filter α}
    (q : α → EReal) (r : α → ℝ)
    (hq : 0 ≤ Filter.liminf q l)
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

theorem smooth_remainder_quotient_tendsto_zero {m : ℕ}
    {h : EuclideanSpace m → ℝ} (hh : ContDiff ℝ 1 h)
    (x : EuclideanSpace m) :
    Tendsto
      (fun y : EuclideanSpace m ↦
        ((h y - h x - inner ℝ (gradient h x) (y - x)) / norm (y - x) : ℝ))
      (nhdsWithin x {y | y ≠ x})
      (nhds 0) := by
  have hdiff : DifferentiableAt ℝ h x :=
    (hh.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) x
  have hgrad : HasGradientAt h (gradient h x) x := hdiff.hasGradientAt
  have ho :
      (fun y ↦ h y - h x - inner ℝ (gradient h x) (y - x)) =o[nhds x]
        (fun y ↦ y - x) :=
    hasGradientAt_iff_isLittleO.mp hgrad
  have hoNorm :
      (fun y ↦ h y - h x - inner ℝ (gradient h x) (y - x)) =o[nhds x]
        (fun y ↦ norm (y - x)) :=
    ho.norm_right
  exact (Asymptotics.IsLittleO.tendsto_div_nhds_zero hoNorm).mono_left
    nhdsWithin_le_nhds

theorem frechetSubdifferential_objective_forward {m : ℕ}
    {f : EuclideanSpace m → EReal} {h : EuclideanSpace m → ℝ}
    {x u : EuclideanSpace m} (hh : ContDiff ℝ 1 h)
    (hu : u ∈ frechetSubdifferential (objectiveSum f h) x) :
    u - gradient h x ∈ frechetSubdifferential f x := by
  have hx : x ∈ ERealFunction.effectiveDom f :=
    (objectiveSum_effectiveDom_iff f h x).1 hu.1
  constructor
  · exact hx
  · let S : Set (EuclideanSpace m) :=
      {y | y ≠ x} ∩ ERealFunction.effectiveDom f
    let rem : EuclideanSpace m → ℝ := fun y ↦
      (h y - h x - inner ℝ (gradient h x) (y - x)) / norm (y - x)
    have hset :
        ({y : EuclideanSpace m | y ≠ x} ∩
            ERealFunction.effectiveDom (objectiveSum f h)) = S := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1, (objectiveSum_effectiveDom_iff f h y).1 hy.2⟩
      · intro hy
        exact ⟨hy.1, (objectiveSum_effectiveDom_iff f h y).2 hy.2⟩
    have hu_liminf :
        0 ≤ Filter.liminf
          (fun y : EuclideanSpace m ↦ frechetQuotient (objectiveSum f h) x u y)
          (nhdsWithin x S) := by
      simpa [S, hset] using hu.2
    have hrem :
        Tendsto rem (nhdsWithin x S) (nhds 0) := by
      exact (smooth_remainder_quotient_tendsto_zero hh x).mono_left
        (nhdsWithin_mono x (by intro y hy; exact hy.1))
    have hpert :
        0 ≤ Filter.liminf
          (fun y : EuclideanSpace m ↦
            frechetQuotient (objectiveSum f h) x u y + ((-rem y : ℝ) : EReal))
          (nhdsWithin x S) :=
      liminf_nonneg_add_tendsto_zero
        (fun y : EuclideanSpace m ↦ frechetQuotient (objectiveSum f h) x u y)
        (fun y : EuclideanSpace m ↦ -rem y)
        hu_liminf (by simpa using hrem.neg)
    have hquot :
        ∀ᶠ y in nhdsWithin x S,
          frechetQuotient f x (u - gradient h x) y =
            frechetQuotient (objectiveSum f h) x u y + ((-rem y : ℝ) : EReal) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro y hy
      have hy_eff : y ∈ ERealFunction.effectiveDom f := hy.2
      change frechetQuotient f x (u - gradient h x) y =
        frechetQuotient (objectiveSum f h) x u y + ((-rem y : ℝ) : EReal)
      unfold ERealFunction.frechetQuotient rem
      rw [objectiveSum_toReal_of_effective hy_eff, objectiveSum_toReal_of_effective hx]
      exact_mod_cast (by
        rw [inner_sub_left]
        ring_nf)
    have hlim := Filter.liminf_congr hquot
    simpa [S, hlim] using hpert

theorem frechetSubdifferential_objective_reverse {m : ℕ}
    {f : EuclideanSpace m → EReal} {h : EuclideanSpace m → ℝ}
    {x w : EuclideanSpace m} (hh : ContDiff ℝ 1 h)
    (hw : w ∈ frechetSubdifferential f x) :
    w + gradient h x ∈ frechetSubdifferential (objectiveSum f h) x := by
  constructor
  · exact (objectiveSum_effectiveDom_iff f h x).2 hw.1
  · let S : Set (EuclideanSpace m) :=
      {y | y ≠ x} ∩ ERealFunction.effectiveDom f
    let rem : EuclideanSpace m → ℝ := fun y ↦
      (h y - h x - inner ℝ (gradient h x) (y - x)) / norm (y - x)
    have hset :
        ({y : EuclideanSpace m | y ≠ x} ∩
            ERealFunction.effectiveDom (objectiveSum f h)) = S := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1, (objectiveSum_effectiveDom_iff f h y).1 hy.2⟩
      · intro hy
        exact ⟨hy.1, (objectiveSum_effectiveDom_iff f h y).2 hy.2⟩
    have hw_liminf :
        0 ≤ Filter.liminf
          (fun y : EuclideanSpace m ↦ frechetQuotient f x w y)
          (nhdsWithin x S) := by
      simpa [S] using hw.2
    have hrem :
        Tendsto rem (nhdsWithin x S) (nhds 0) := by
      exact (smooth_remainder_quotient_tendsto_zero hh x).mono_left
        (nhdsWithin_mono x (by intro y hy; exact hy.1))
    have hpert :
        0 ≤ Filter.liminf
          (fun y : EuclideanSpace m ↦
            frechetQuotient f x w y + ((rem y : ℝ) : EReal))
          (nhdsWithin x S) :=
      liminf_nonneg_add_tendsto_zero
        (fun y : EuclideanSpace m ↦ frechetQuotient f x w y)
        rem hw_liminf hrem
    have hquot :
        ∀ᶠ y in nhdsWithin x S,
          frechetQuotient (objectiveSum f h) x (w + gradient h x) y =
            frechetQuotient f x w y + ((rem y : ℝ) : EReal) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro y hy
      have hy_eff : y ∈ ERealFunction.effectiveDom f := hy.2
      change frechetQuotient (objectiveSum f h) x (w + gradient h x) y =
        frechetQuotient f x w y + ((rem y : ℝ) : EReal)
      unfold ERealFunction.frechetQuotient rem
      rw [objectiveSum_toReal_of_effective hy_eff, objectiveSum_toReal_of_effective hw.1]
      exact_mod_cast (by
        rw [inner_add_left]
        ring_nf)
    have hlim := Filter.liminf_congr hquot
    have hgoalS :
        0 ≤ Filter.liminf
          (fun y : EuclideanSpace m ↦
            frechetQuotient (objectiveSum f h) x (w + gradient h x) y)
          (nhdsWithin x S) := by
      simpa [hlim] using hpert
    simpa [S, hset] using hgoalS

/-- Smooth perturbation rule for the limiting subdifferential. -/
theorem limitingSubdifferential_smooth_sum_rule {m : ℕ}
    (f : EuclideanSpace m → EReal) (h : EuclideanSpace m → ℝ)
    (x : EuclideanSpace m) (hf : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f) (hh : ContDiff ℝ 1 h) :
    limitingSubdifferential (objectiveSum f h) x =
      {v | ∃ w ∈ limitingSubdifferential f x, v = w + gradient h x} := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨hobj_eff, zs, us, hzs, hobjVal, husFrechet, hus⟩
    have hx_eff : x ∈ ERealFunction.effectiveDom f :=
      (objectiveSum_effectiveDom_iff f h x).1 hobj_eff
    have hzs_eff : ∀ n, zs n ∈ ERealFunction.effectiveDom f := by
      intro n
      exact (objectiveSum_effectiveDom_iff f h (zs n)).1 (husFrechet n).1
    have hh_tendsto : Tendsto (fun n ↦ h (zs n)) atTop (nhds (h x)) :=
      (hh.continuous.tendsto x).comp hzs
    have hfVal : Tendsto (fun n ↦ f (zs n)) atTop (nhds (f x)) :=
      (objectiveSum_value_tendsto_iff hzs_eff hx_eff hh_tendsto).1 hobjVal
    have hfrechet :
        ∀ n, us n - gradient h (zs n) ∈ frechetSubdifferential f (zs n) := by
      intro n
      exact frechetSubdifferential_objective_forward hh (husFrechet n)
    have hgrad : Tendsto (fun n ↦ gradient h (zs n)) atTop
        (nhds (gradient h x)) :=
      gradient_tendsto_of_contDiff_one hh hzs
    have hsubgrad : Tendsto (fun n ↦ us n - gradient h (zs n)) atTop
        (nhds (v - gradient h x)) :=
      hus.sub hgrad
    refine ⟨v - gradient h x, ?_, by simp⟩
    exact ⟨hx_eff, zs, fun n ↦ us n - gradient h (zs n), hzs, hfVal,
      hfrechet, hsubgrad⟩
  · intro hv
    rcases hv with ⟨w, hw, rfl⟩
    rcases hw with ⟨hx_eff, zs, ws, hzs, hfVal, hwsFrechet, hws⟩
    have hobj_eff : x ∈ ERealFunction.effectiveDom (objectiveSum f h) :=
      (objectiveSum_effectiveDom_iff f h x).2 hx_eff
    have hzs_eff : ∀ n, zs n ∈ ERealFunction.effectiveDom f := by
      intro n
      exact (hwsFrechet n).1
    have hh_tendsto : Tendsto (fun n ↦ h (zs n)) atTop (nhds (h x)) :=
      (hh.continuous.tendsto x).comp hzs
    have hobjVal :
        Tendsto (fun n ↦ objectiveSum f h (zs n)) atTop
          (nhds (objectiveSum f h x)) :=
      (objectiveSum_value_tendsto_iff hzs_eff hx_eff hh_tendsto).2 hfVal
    have hfrechet :
        ∀ n, ws n + gradient h (zs n) ∈
          frechetSubdifferential (objectiveSum f h) (zs n) := by
      intro n
      exact frechetSubdifferential_objective_reverse hh (hwsFrechet n)
    have hgrad : Tendsto (fun n ↦ gradient h (zs n)) atTop
        (nhds (gradient h x)) :=
      gradient_tendsto_of_contDiff_one hh hzs
    have hsubgrad : Tendsto (fun n ↦ ws n + gradient h (zs n)) atTop
        (nhds (w + gradient h x)) :=
      hws.add hgrad
    exact ⟨hobj_eff, zs, fun n ↦ ws n + gradient h (zs n), hzs, hobjVal,
      hfrechet, hsubgrad⟩

end BotCsetnek2015
