import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_def_2

namespace Alvarez2002

open Filter

set_option maxHeartbeats 800000

private theorem omegaLimit_eq_iInter_nat_tailClosure
    {H : Type*} [MetricSpace H] (x : Set.Ici (0 : ℝ) → H) :
    omegaLimit x = ⋂ n : ℕ, closure (x '' Set.Ici
      (⟨(n : ℝ), by change (0 : ℝ) ≤ (n : ℝ); positivity⟩ : Set.Ici (0 : ℝ))) := by
  ext z
  constructor
  · rintro ⟨t, ht, hxt⟩
    refine Set.mem_iInter.2 fun n => ?_
    apply mem_closure_of_tendsto hxt
    filter_upwards [ht.eventually (eventually_ge_atTop (n : ℝ))] with j hj
    exact ⟨t j, hj, rfl⟩
  · intro hz
    have hmem : ∀ n : ℕ,
        z ∈ closure (x '' Set.Ici
          (⟨(n : ℝ), by change (0 : ℝ) ≤ (n : ℝ); positivity⟩ : Set.Ici (0 : ℝ))) :=
      fun n => Set.mem_iInter.1 hz n
    choose y hymem hyclose using fun n : ℕ =>
      Metric.mem_closure_iff.1 (hmem n) (1 / ((n : ℝ) + 1)) (by positivity)
    have htime : ∀ n : ℕ, ∃ r : Set.Ici (0 : ℝ), (n : ℝ) ≤ (r : ℝ) ∧ x r = y n :=
      fun n => hymem n
    choose t htge htx using htime
    have htclose' (n : ℕ) : dist (x (t n)) z < 1 / ((n : ℝ) + 1) := by
      simpa [htx n, dist_comm] using hyclose n
    refine ⟨t, ?_, ?_⟩
    · refine tendsto_atTop.2 fun R => ?_
      obtain ⟨N, hN⟩ := exists_nat_ge R
      filter_upwards [eventually_ge_atTop N] with n hn
      exact le_trans hN (le_trans (by exact_mod_cast hn) (htge n))
    · rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      calc
        dist (x (t n)) z < 1 / ((n : ℝ) + 1) := htclose' n
        _ ≤ 1 / ((N : ℝ) + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast (Nat.add_le_add_right hn 1)
        _ < ε := by simpa using hN

private theorem nested_isPreconnected_iInter {X : Type*} [TopologicalSpace X] [T2Space X]
    [NormalSpace X] (K : ℕ → Set X) (hstep : ∀ n, K (n + 1) ⊆ K n)
    (hcompact : ∀ n, IsCompact (K n)) (hclosed : ∀ n, IsClosed (K n))
    (_hnonempty : ∀ n, (K n).Nonempty) (hpre : ∀ n, IsPreconnected (K n)) :
    IsPreconnected (⋂ n : ℕ, K n) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hcover hinter
  by_contra h
  have hnotU : ¬ (⋂ n : ℕ, K n) ⊆ u := fun hs => h (Or.inl hs)
  have hnotV : ¬ (⋂ n : ℕ, K n) ⊆ v := fun hs => h (Or.inr hs)
  rcases Set.not_subset.mp hnotU with ⟨zu, hzu, hzuu⟩
  rcases Set.not_subset.mp hnotV with ⟨zv, hzv, hzvv⟩
  have hzuV : zu ∈ v := (hcover hzu).resolve_left hzuu
  have hzvU : zv ∈ u := (hcover hzv).resolve_right hzvv
  let A : Set X := ⋂ n : ℕ, K n
  let P : Set X := A ∩ u
  let Q : Set X := A ∩ v
  have hAclosed : IsClosed A := isClosed_iInter hclosed
  have hPclosed : IsClosed P := hAclosed.inter hu
  have hQclosed : IsClosed Q := hAclosed.inter hv
  have hPQ : Disjoint P Q := by
    rw [Set.disjoint_left]
    intro y hyP hyQ
    have hy : y ∈ (⋂ n : ℕ, K n) ∩ (u ∩ v) := ⟨hyP.1, ⟨hyP.2, hyQ.2⟩⟩
    rw [hinter] at hy
    exact hy.elim
  obtain ⟨U, V, hUopen, hVopen, hPU, hQV, hUV⟩ := normal_separation hPclosed hQclosed hPQ
  have hcover_tail : ∃ N, K N ⊆ U ∪ V := by
    by_contra hn
    have hn' : ∀ n, ¬ K n ⊆ U ∪ V := fun n hsub => hn ⟨n, hsub⟩
    have hn'' : ∀ n, ∃ y, y ∈ K n ∧ y ∉ U ∪ V := fun n => Set.not_subset.mp (hn' n)
    choose q hqK hq using hn''
    let R : ℕ → Set X := fun n => K n ∩ (U ∪ V)ᶜ
    have hRnonempty : ∀ n, (R n).Nonempty := fun n => ⟨q n, hqK n, hq n⟩
    have hRstep : ∀ n, R (n + 1) ⊆ R n := by
      intro n y hy
      exact ⟨hstep n hy.1, hy.2⟩
    have hRclosed : ∀ n, IsClosed (R n) := fun n =>
      (hclosed n).inter (hUopen.union hVopen).isClosed_compl
    have hRcompact : IsCompact (R 0) :=
      (hcompact 0).of_isClosed_subset (hRclosed 0) Set.inter_subset_left
    obtain ⟨r, hr⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed R hRstep
      hRnonempty hRcompact hRclosed
    have hrA : r ∈ A := Set.mem_iInter.2 fun n => (Set.mem_iInter.1 hr n).1
    have hrUV : r ∈ U ∪ V := by
      rcases hcover hrA with hru | hrv
      · exact Or.inl (hPU ⟨hrA, hru⟩)
      · exact Or.inr (hQV ⟨hrA, hrv⟩)
    exact (Set.mem_compl_iff (U ∪ V) r).mp (Set.mem_iInter.1 hr 0).2 hrUV
  rcases hcover_tail with ⟨N, hN⟩
  have hPmem : zv ∈ P := ⟨hzv, hzvU⟩
  have hQmem : zu ∈ Q := ⟨hzu, hzuV⟩
  have hKN_U : K N ⊆ U := (hpre N).subset_left_of_subset_union hUopen hVopen hUV hN
    ⟨zv, Set.mem_iInter.1 hzv N, hPU hPmem⟩
  exact hUV.le_bot ⟨hKN_U (Set.mem_iInter.1 hzu N), hQV hQmem⟩

private theorem tendsto_infDist_omegaLimit_of_compact_closure {H : Type*} [MetricSpace H]
    (x : Set.Ici (0 : ℝ) → H) (hcompact : IsCompact (closure (Set.range x))) :
    Tendsto (fun t => Metric.infDist (x t) (omegaLimit x)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra h
  push Not at h
  choose t ht hbad using fun n : ℕ => h
    (⟨(n : ℝ), by change (0 : ℝ) ≤ (n : ℝ); positivity⟩ : Set.Ici (0 : ℝ))
  have hbad' (n : ℕ) : ε ≤ Metric.infDist (x (t n)) (omegaLimit x) := by
    simpa [Real.dist_eq, abs_of_nonneg Metric.infDist_nonneg] using hbad n
  have htop : Tendsto (fun n => (t n : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun R => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge R
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact hN.trans (hcast.trans (ht n))
  have hx : ∀ n, x (t n) ∈ closure (Set.range x) := fun n => subset_closure ⟨t n, rfl⟩
  obtain ⟨z, hz, φ, hφ, hconv⟩ := hcompact.tendsto_subseq hx
  have htime : Tendsto (fun n => (t (φ n) : ℝ)) atTop atTop := htop.comp hφ.tendsto_atTop
  have hzomega : z ∈ omegaLimit x := ⟨fun n => t (φ n), htime, by
    simpa [Function.comp_def] using hconv⟩
  have hdist : Tendsto (fun n => Metric.infDist (x (t (φ n))) (omegaLimit x)) atTop (nhds 0) := by
    simpa [Function.comp_def, Metric.infDist_zero_of_mem hzomega] using
      ((Metric.continuous_infDist_pt (omegaLimit x)).tendsto z).comp hconv
  have hle : ε ≤ 0 := ge_of_tendsto hdist (Eventually.of_forall fun n => hbad' (φ n))
  linarith

/-- Standard finite-dimensional properties of the omega-limit set. -/
theorem omega_limit_properties {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [CompleteSpace N] [FiniteDimensional ℝ N] [ProperSpace N]
    (Φ : N → ℝ) (gradΦ : N → N)
    (_hΦ : ContDiff ℝ 1 Φ) (_hgradΦ : ∀ u, HasFDerivAt Φ (innerSL ℝ (gradΦ u)) u)
    (hgrad_cont : Continuous gradΦ)
    (x : Set.Ici (0 : ℝ) → N)
    (hcontinuous_flow : ∃ φ : ℝ → N → N, Continuous (Function.uncurry φ) ∧ ∃ x₀ : N,
      ∀ t : Set.Ici (0 : ℝ), x t = φ (t : ℝ) x₀)
    (hbounded : Bornology.IsBounded (Set.range x))
    (velocity : Set.Ici (0 : ℝ) → N)
    (_hvelocity : Tendsto velocity atTop (nhds 0))
    (hgradient : Tendsto (fun t : Set.Ici (0 : ℝ) => gradΦ (x t)) atTop (nhds 0)) :
    (omegaLimit x).Nonempty ∧ IsCompact (omegaLimit x) ∧ IsConnected (omegaLimit x) ∧
    Tendsto (fun t : Set.Ici (0 : ℝ) => Metric.infDist (x t) (omegaLimit x)) atTop (nhds 0) ∧
      ∀ z ∈ omegaLimit x, gradΦ z = 0 := by
  rcases hcontinuous_flow with ⟨φ, hφcont, x₀, hx⟩
  have hxcont : Continuous x := by
    have hi : Continuous (fun t : Set.Ici (0 : ℝ) => ((t : ℝ), x₀)) :=
      continuous_subtype_val.prodMk continuous_const
    rw [show x = fun t : Set.Ici (0 : ℝ) => φ (t : ℝ) x₀ from funext hx]
    exact hφcont.comp hi
  let τ : ℕ → Set.Ici (0 : ℝ) := fun n =>
    ⟨(n : ℝ), by change (0 : ℝ) ≤ (n : ℝ); positivity⟩
  let K : ℕ → Set N := fun n => closure (x '' Set.Ici (τ n))
  have hKn : ∀ n : ℕ, (K n).Nonempty := by
    intro n
    refine ⟨x (τ n), ?_⟩
    apply subset_closure
    refine ⟨τ n, ?_, rfl⟩
    change τ n ≤ τ n
    exact le_rfl
  have hKsub : ∀ n : ℕ, K n ⊆ closure (Set.range x) := by
    intro n
    apply closure_mono
    rintro y ⟨t, ht, hxy⟩
    exact ⟨t, hxy⟩
  have hKcompact : ∀ n : ℕ, IsCompact (K n) := by
    intro n
    exact (hbounded.isCompact_closure).of_isClosed_subset isClosed_closure (hKsub n)
  have hKstep : ∀ n : ℕ, K (n + 1) ⊆ K n := by
    intro n
    apply closure_mono
    rintro y ⟨t, ht, hxy⟩
    refine ⟨t, ?_, hxy⟩
    change (τ n : ℝ) ≤ (t : ℝ)
    calc
      (τ n : ℝ) = (n : ℝ) := rfl
      _ ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
      _ = (τ (n + 1) : ℝ) := rfl
      _ ≤ (t : ℝ) := ht
  have hKpre : ∀ n : ℕ, IsPreconnected (K n) := by
    intro n
    change IsPreconnected (closure (x '' Set.Ici (τ n)))
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    let g : ℝ → N := fun r =>
      x ⟨max r n, by change (0 : ℝ) ≤ max r n; exact hn0.trans (le_max_right _ _)⟩
    have hgcont : Continuous g := by
      apply hxcont.comp
      exact (continuous_id.max continuous_const).subtype_mk _
    have himage : x '' Set.Ici (τ n) = Set.range g := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(t : ℝ), ?_⟩
        dsimp [g]
        congr 2
        apply max_eq_left
        simpa [τ] using ht
      · rintro ⟨r, rfl⟩
        refine ⟨⟨max r n, by change (0 : ℝ) ≤ max r n; exact hn0.trans (le_max_right _ _)⟩, ?_, rfl⟩
        change (τ n : ℝ) ≤ max r n
        change (n : ℝ) ≤ max r n
        exact le_max_right _ _
    rw [himage, ← Set.image_univ]
    exact (isPreconnected_univ.image g hgcont.continuousOn).closure
  have homega : omegaLimit x = ⋂ n : ℕ, K n := by
    simpa [K, τ] using omegaLimit_eq_iInter_nat_tailClosure x
  have hOmegaNonempty : (omegaLimit x).Nonempty := by
    rw [homega]
    exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKstep hKn
      (hKcompact 0) fun n => (hKcompact n).isClosed
  have hOmegaCompact : IsCompact (omegaLimit x) := by
    rw [homega]
    apply (hKcompact 0).of_isClosed_subset
    · exact isClosed_iInter fun n => (hKcompact n).isClosed
    · exact Set.iInter_subset _ 0
  have hOmegaPreconnected : IsPreconnected (omegaLimit x) := by
    rw [homega]
    exact nested_isPreconnected_iInter K hKstep hKcompact
      (fun n => (hKcompact n).isClosed) hKn hKpre
  have hDistOmega : Tendsto (fun t => Metric.infDist (x t) (omegaLimit x)) atTop (nhds 0) :=
    tendsto_infDist_omegaLimit_of_compact_closure x hbounded.isCompact_closure
  have hCritical : ∀ z ∈ omegaLimit x, gradΦ z = 0 := by
    rintro z ⟨t, ht, hxt⟩
    have ht' : Tendsto t atTop atTop := by
      refine tendsto_atTop.2 fun s => ?_
      filter_upwards [ht.eventually (eventually_ge_atTop (s : ℝ))] with n hn
      exact hn
    have h1 : Tendsto (fun n : ℕ => gradΦ (x (t n))) atTop (nhds 0) := by
      simpa [Function.comp_def] using hgradient.comp ht'
    have h2 : Tendsto (fun n : ℕ => gradΦ (x (t n))) atTop (nhds (gradΦ z)) := by
      simpa [Function.comp_def] using (hgrad_cont.tendsto z).comp hxt
    exact tendsto_nhds_unique h2 h1
  exact ⟨hOmegaNonempty, hOmegaCompact, ⟨hOmegaNonempty, hOmegaPreconnected⟩,
    hDistOmega, hCritical⟩

end Alvarez2002
