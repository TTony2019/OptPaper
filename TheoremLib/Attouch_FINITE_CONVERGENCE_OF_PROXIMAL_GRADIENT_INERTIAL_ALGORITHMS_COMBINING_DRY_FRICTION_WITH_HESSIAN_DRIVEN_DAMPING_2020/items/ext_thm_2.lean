import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_4

open scoped InnerProductSpace

open ERealFunction

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

/-- Inclusion-based extended-real proximal points are unique at a positive index. -/
theorem proximalPointEReal_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (g : H → EReal) (lam : ℝ) (hlam : 0 < lam)
    (hproper : ERealFunction.IsProper g) (w p q : H) :
    IsProximalPointEReal g lam w p → IsProximalPointEReal g lam w q → p = q := by
  rintro ⟨hp, v, hv, hwp⟩ ⟨hq, z, hz, hwq⟩
  have hpbot : g p ≠ ⊥ := hproper.1 p
  have hqbot : g q ≠ ⊥ := hproper.1 q
  have hpq : (g p).toReal + @inner ℝ H _ v (q - p) ≤ (g q).toReal := by
    have h := hv q
    change (⟪q - p, v⟫_ℝ : EReal) + (g p : EReal) ≤ (g q : EReal) at h
    rw [real_inner_comm, add_comm] at h
    have h := EReal.toReal_le_toReal h
      (EReal.add_ne_bot_iff.mpr ⟨hpbot, EReal.coe_ne_bot _⟩) hq
    simpa [EReal.toReal_add hp hpbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] using h
  have hqp : (g q).toReal + @inner ℝ H _ z (p - q) ≤ (g p).toReal := by
    have h := hz p
    change (⟪p - q, z⟫_ℝ : EReal) + (g q : EReal) ≤ (g p : EReal) at h
    rw [real_inner_comm, add_comm] at h
    have h := EReal.toReal_le_toReal h
      (EReal.add_ne_bot_iff.mpr ⟨hqbot, EReal.coe_ne_bot _⟩) hp
    simpa [EReal.toReal_add hq hqbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] using h
  have hmono : @inner ℝ H _ (v - z) (q - p) ≤ 0 := by
    rw [← neg_sub, inner_neg_right] at hqp
    rw [inner_sub_left]
    linarith [add_le_add hpq hqp]
  have hdiff : q - p = lam • (v - z) := by
    calc
      q - p = (w - p) - (w - q) := by abel
      _ = lam • v - lam • z := by rw [← hwp, ← hwq]
      _ = lam • (v - z) := by module
  have hsq : lam * ‖v - z‖ ^ 2 ≤ 0 := by
    calc
      lam * ‖v - z‖ ^ 2 = @inner ℝ H _ (v - z) (q - p) := by
        rw [hdiff, inner_smul_right, real_inner_self_eq_norm_sq]
      _ ≤ 0 := hmono
  have hvz : v = z := by
    have : ‖v - z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v - z‖]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this |> norm_eq_zero.mp)
  exact (sub_eq_zero.mp (by simpa [hvz] using hdiff)).symm

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
    (_hlsc : LowerSemicontinuous g) (hproper : ERealFunction.IsProper g)
    (hf : ∀ x, f x = (((1 / 2 : ℝ) * ‖A x - b‖ ^ 2 : ℝ) : EReal) + g x)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (_hM_positive : ∀ v, v ≠ 0 → 0 < @inner ℝ H _ (M v) v) (proxF proxG : H → H)
    (hproxF : ∀ x, ∃ (_hp : f (proxF x) ≠ ⊤),
      M (x - proxF x) ∈ (fun u ↦ lam • u) '' subdifferential f (proxF x))
    (hproxG : ∀ x, IsProximalPointEReal g lam x (proxG x)) (x : H) :
    proxF x = proxG (x - lam • A.adjoint (A x - b)) := by
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
  have hP : IsProximalPointEReal g lam (x - lam • A.adjoint (A x - b)) (proxF x) := by
    refine ⟨?_, ?_⟩
    · intro htop
      apply hp
      rw [hf (proxF x), htop]
      exact EReal.coe_add_top _
    · refine ⟨u - A.adjoint (A (proxF x) - b), ?_, hres.symm⟩
      exact subgradientEReal_quadratic_add A b (proxF x) u g f hconvex hproper hf hp hu
  exact proximalPointEReal_unique g lam hlam hproper _ _ _ hP (hproxG _)
