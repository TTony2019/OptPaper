import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_4

open scoped InnerProductSpace

open ERealFunction
open Pointwise

private theorem quadratic_increment_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →L[ℝ] H) (b p y : H) :
    (1 / 2 : ℝ) * ‖A y - b‖ ^ 2 =
      (1 / 2 : ℝ) * ‖A p - b‖ ^ 2 +
        @inner ℝ H _ (A.adjoint (A p - b)) (y - p) + (1 / 2 : ℝ) * ‖A (y - p)‖ ^ 2 := by
  have hdecomp : A y - b = (A p - b) + A (y - p) := by
    rw [map_sub]
    abel
  rw [hdecomp, norm_add_sq_real]
  rw [A.adjoint_inner_left]
  ring

private theorem ereal_convex_chord_toReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (g : H → EReal)
    (hconvex : Convex ℝ (ERealFunction.epigraph g)) (hproper : ERealFunction.IsProper g)
    {p y : H} (hp_top : g p ≠ ⊤) (hy_top : g y ≠ ⊤) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (g (p + t • (y - p))).toReal ≤ (1 - t) * (g p).toReal + t * (g y).toReal := by
  have hp_epi : (p, (g p).toReal) ∈ ERealFunction.epigraph g := EReal.le_coe_toReal hp_top
  have hy_epi : (y, (g y).toReal) ∈ ERealFunction.epigraph g := EReal.le_coe_toReal hy_top
  have hcomb := hconvex hp_epi hy_epi (sub_nonneg.mpr ht1) ht0 (by ring)
  rw [ERealFunction.mem_epigraph_iff] at hcomb
  have hsegment : (1 - t) • p + t • y = p + t • (y - p) := by module
  have hcomb' : g (p + t • (y - p)) ≤
      ↑((1 - t) * (g p).toReal + t * (g y).toReal) := by
    simpa [Prod.smul_mk, hsegment] using hcomb
  exact EReal.toReal_le_toReal hcomb' (hproper.1 _) (EReal.coe_ne_top _)

private theorem ereal_convex_segment_ne_top {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (g : H → EReal)
    (hconvex : Convex ℝ (ERealFunction.epigraph g)) {p y : H}
    (hp_top : g p ≠ ⊤) (hy_top : g y ≠ ⊤) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g (p + t • (y - p)) ≠ ⊤ := by
  have hp_epi : (p, (g p).toReal) ∈ ERealFunction.epigraph g := EReal.le_coe_toReal hp_top
  have hy_epi : (y, (g y).toReal) ∈ ERealFunction.epigraph g := EReal.le_coe_toReal hy_top
  have hcomb := hconvex hp_epi hy_epi (sub_nonneg.mpr ht1) ht0 (by ring)
  rw [ERealFunction.mem_epigraph_iff] at hcomb
  have hsegment : (1 - t) • p + t • y = p + t • (y - p) := by module
  apply ne_top_of_le_ne_top (EReal.coe_ne_top _) 
  simpa [Prod.smul_mk, hsegment] using hcomb

set_option linter.unusedVariables false in
/-- `]-∞,+∞]`-valued objectives that are proper, convex (with convex epigraph) and lower
semicontinuous lie in `Γ₀(H)`, so Foundation's proximity operator is available for them. -/
private theorem properIoi_mem_gammaZero_of_epigraph_convex_lsc {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {g : H → EReal} (hproper : ERealFunction.IsProper g)
    (hconvex : Convex ℝ (ERealFunction.epigraph g)) (hlsc : LowerSemicontinuous g) :
    ERealFunction.properIoi g hproper ∈ Γ₀(H) :=
  ERealFunction.properIoi_mem_gammaZero_of_mem_gamma hproper (by
    rw [ERealFunction.mem_gamma_iff]
    exact ⟨ERealFunction.isConvex_of_convex_epigraph hproper hconvex, hlsc⟩)

/-- Proximal points of a `Γ₀` objective are unique at a positive index; this is Foundation's
`HasUniqueProxPoint` in its primal `IsProxPoint` form. -/
theorem isProxPoint_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {g : H → EReal} (hproper : ERealFunction.IsProper g)
    (hΓ : ERealFunction.properIoi g hproper ∈ Γ₀(H))
    (lam : ℝ) (hlam : 0 < lam) (w p q : H)
    (hp : IsProxPoint ((⟨lam, hlam⟩ : PosReal) • ERealFunction.properIoi g hproper) w p)
    (hq : IsProxPoint ((⟨lam, hlam⟩ : PosReal) • ERealFunction.properIoi g hproper) w q) :
    p = q :=
  ExistsUnique.unique
    (hasUniqueProxPoint_of_mem_gammaZero
      (smul_mem_gammaZero (ERealFunction.properIoi g hproper) hΓ ⟨lam, hlam⟩) w) hp hq

/-- Removing the smooth quadratic part from an extended-real subgradient. -/
private theorem subgradientEReal_quadratic_add {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →L[ℝ] H) (b p u : H)
    (g f : H → EReal) (hconvex : Convex ℝ (ERealFunction.epigraph g))
    (hproper : ERealFunction.IsProper g)
    (hf : ∀ z, f z = (((1 / 2 : ℝ) * ‖A z - b‖ ^ 2 : ℝ) : EReal) + g z)
    (hp : f p ≠ ⊤) (hu : u ∈ subdifferential f p) :
    u - A.adjoint (A p - b) ∈ subdifferential g p := by
  rw [subdifferential]
  intro y
  by_cases hy : g y = ⊤
  · rw [hy]
    exact le_top
  · have hpG : g p ≠ ⊤ := by
      intro htop
      apply hp
      rw [hf p, htop]
      exact EReal.coe_add_top _
    have hpGbot : g p ≠ ⊥ := hproper.1 p
    have hyGbot : g y ≠ ⊥ := hproper.1 y
    have herror : ∀ t : ℝ, 0 < t → t ≤ 1 →
        (g p).toReal + @inner ℝ H _ (u - A.adjoint (A p - b)) (y - p) ≤
          (g y).toReal + t * ((1 / 2 : ℝ) * ‖A (y - p)‖ ^ 2) := by
      intro t ht ht1
      have ht0 : 0 ≤ t := ht.le
      have hytop : g (p + t • (y - p)) ≠ ⊤ :=
        ereal_convex_segment_ne_top g hconvex hpG hy t ht0 ht1
      have hytbot : g (p + t • (y - p)) ≠ ⊥ := hproper.1 _
      have hsub := hu (p + t • (y - p))
      change (⟪p + t • (y - p) - p, u⟫_ℝ : EReal) + (f p : EReal) ≤
        (f (p + t • (y - p)) : EReal) at hsub
      rw [real_inner_comm, add_comm] at hsub
      rw [hf (p + t • (y - p)), hf p] at hsub
      have hlefttop : ((↑((1 / 2 : ℝ) * ‖A p - b‖ ^ 2) : EReal) + g p) ≠ ⊤ :=
        EReal.add_ne_top (EReal.coe_ne_top _) hpG
      have hleftbot : ((↑((1 / 2 : ℝ) * ‖A p - b‖ ^ 2) : EReal) + g p) ≠ ⊥ :=
        EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hpGbot⟩
      have hrighttop : ((↑((1 / 2 : ℝ) * ‖A (p + t • (y - p)) - b‖ ^ 2) : EReal) +
          g (p + t • (y - p))) ≠ ⊤ := EReal.add_ne_top (EReal.coe_ne_top _) hytop
      have hsub_real := EReal.toReal_le_toReal hsub
        (EReal.add_ne_bot_iff.mpr ⟨hleftbot, EReal.coe_ne_bot _⟩) hrighttop
      rw [EReal.toReal_add hlefttop hleftbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hpG hpGbot,
        EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hytop hytbot] at hsub_real
      simp only [EReal.toReal_coe] at hsub_real
      have hchord := ereal_convex_chord_toReal g hconvex hproper hpG hy t ht0 ht1
      rw [quadratic_increment_adjoint A b p (p + t • (y - p))] at hsub_real
      have hseg_sub : p + t • (y - p) - p = t • (y - p) := by abel
      rw [hseg_sub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hsub_real
      simp only [inner_smul_right] at hsub_real
      rw [inner_sub_left]
      nlinarith
    have hreal : (g p).toReal + @inner ℝ H _
        (u - A.adjoint (A p - b)) (y - p) ≤ (g y).toReal := by
      apply le_of_forall_pos_le_add
      intro ε hε
      let R : ℝ := (1 / 2 : ℝ) * ‖A (y - p)‖ ^ 2
      let t : ℝ := ε / (R + ε + 1)
      have hR : 0 ≤ R := by dsimp [R]; positivity
      have hden : 0 < R + ε + 1 := by linarith
      have ht : 0 < t := by dsimp [t]; positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_one₀ hden).2
        linarith
      have htR : t * R ≤ ε := by
        dsimp [t]
        calc
          ε / (R + ε + 1) * R = (ε * R) / (R + ε + 1) := by ring
          _ ≤ ε := (div_le_iff₀ hden).2 (by nlinarith)
      have := herror t ht ht1
      dsimp [R] at htR
      linarith
    change (⟪y - p, u - A.adjoint (A p - b)⟫_ℝ : EReal) + (g p : EReal) ≤
      (g y : EReal)
    rw [← EReal.coe_toReal hpG hpGbot, ← EReal.coe_toReal hy hyGbot]
    norm_cast
    rw [real_inner_comm, add_comm]
    exact hreal

/-- External result: the variable-metric proximal map of a Lasso objective splits forward-backward. -/
theorem variableMetric_composite_proximal_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f g : H → EReal) (A : H →L[ℝ] H) (b : H)
    (M : H →L[ℝ] H) (lam : ℝ) (hlam : 0 < lam)
    (hconvex : Convex ℝ (ERealFunction.epigraph g))
    (hlsc : LowerSemicontinuous g) (hproper : ERealFunction.IsProper g)
    (hf : ∀ x, f x = (((1 / 2 : ℝ) * ‖A x - b‖ ^ 2 : ℝ) : EReal) + g x)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (_hM_positive : ∀ v, v ≠ 0 → 0 < @inner ℝ H _ (M v) v) (proxF : H → H)
    (hproxF : ∀ x, ∃ (_hp : f (proxF x) ≠ ⊤),
      M (x - proxF x) ∈ (fun u ↦ lam • u) '' subdifferential f (proxF x)) (x : H) :
    proxF x = ERealFunction.scaledProximityOperator (ERealFunction.properIoi g hproper)
      (properIoi_mem_gammaZero_of_epigraph_convex_lsc hproper hconvex hlsc) ⟨lam, hlam⟩
      (x - lam • A.adjoint (A x - b)) := by
  rcases hproxF x with ⟨hp, u, hu, hMu⟩
  have hres : x - lam • A.adjoint (A x - b) - proxF x =
      lam • (u - A.adjoint (A (proxF x) - b)) := by
    have hMu' : x - proxF x - lam • A.adjoint (A (x - proxF x)) = lam • u := by
      rw [hM] at hMu
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at hMu
      exact hMu.symm
    calc
      x - lam • A.adjoint (A x - b) - proxF x =
          x - proxF x - lam • A.adjoint (A (x - proxF x)) -
            lam • A.adjoint (A (proxF x) - b) := by
              simp [map_sub]
              module
      _ = lam • u - lam • A.adjoint (A (proxF x) - b) := by rw [hMu']
      _ = lam • (u - A.adjoint (A (proxF x) - b)) := by module
  have hg : u - A.adjoint (A (proxF x) - b) ∈ subdifferential g (proxF x) :=
    subgradientEReal_quadratic_add A b (proxF x) u g f hconvex hproper hf hp hu
  have hΓ : ERealFunction.properIoi g hproper ∈ Γ₀(H) :=
    properIoi_mem_gammaZero_of_epigraph_convex_lsc hproper hconvex hlsc
  rw [ERealFunction.scaledProximityOperator]
  refine (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
    (f := (⟨lam, hlam⟩ : PosReal) • ERealFunction.properIoi g hproper)
    (ERealFunction.smul_mem_gammaZero _ hΓ ⟨lam, hlam⟩)
    (x - lam • A.adjoint (A x - b)) (proxF x)).2 ?_
  rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
  change x - lam • A.adjoint (A x - b) - proxF x ∈
    (lam : ℝ) • (subdifferential (ERealFunction.properIoi g hproper) (proxF x))
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
  rw [hres, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  simpa [ERealFunction.properIoi, ERealFunction.subdifferential] using hg
