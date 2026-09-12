## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/thm_3.lean`

## Lean statement
```lean
theorem thm_5_1 (C : Set H) (hC_closed : IsClosed C) (hC_conv : Convex ℝ C)
    (hC_polyhedron : ConvexPolyhedron C) (hC_bounded : Bornology.IsBounded C)
    (hC_int : (0 : H) ∈ interior C) (A0 : H → H) (hA0_C2 : ContDiff ℝ 2 A0)
    (hA0_mono : IsMaximalMonotone
      (SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1)))
    (hA0_zero : A0 (0 : H) = 0)
    (m : ℝ) (hm : m > 0) (hA0_coercive : ∀ (x : H), inner ℝ (fderiv ℝ A0 (0 : H) x) x ≥ m * ‖x‖^2)
    (A : SetValuedOperator H H) (hA : A = subderivative (supportFunction C) +
      SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1))
    (f : H → ℝ) (hf_conv : ConvexOn ℝ Set.univ f) (hf_C1 : ContDiff ℝ 1 f) (hinf : ∃ m, ∀ x, f x ≥ m)
    (M : ℝ) (hf_strongConv : IsStronglyConvex f M)
    (B : SetValuedOperator H H) (hB_eq_grad : B =
      SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H) (hxInf : Tendsto x atTop (𝓝 xInf)) :
    ∃ (n0 : ℕ) (K : ℝ) (q : ℝ), K > 0 ∧ q > 0 ∧ q < 1 ∧
      ∀ n ≥ n0, ‖x (n+1) - x n‖ ≤ K * q ^ n
```

## Statement explanation
The declaration `thm_5_1` states a geometric-decay result for the successive differences of an inertial proximal algorithm with dry friction, in an ambient real inner product space $H$.

The data are as follows. $C \subseteq H$ is closed, convex, a convex polyhedron, bounded, and contains $0$ in its interior:

$$
0 \in \mathrm{int} C.
$$

The map $A_0 : H \to H$ is $C^2$, its singleton-valued operator $`x \mapsto \{A_0(x)\}`$on all of$H$is maximal monotone, and$A_0(0)=0$. There is$m>0$such that the derivative$L = DA_0(0)$ is coercive:

```math
\langle Lx,x\rangle \ge m\|x\|^2 \qquad \text{for all } x\in H.
```

The set-valued operator $A$ is

$$
A = \partial \sigma_C + A_0,
$$

where $A_0$ is again regarded as the singleton-valued operator, and

$$
\sigma_C(y) = \sup_{z\in C} \langle z,y\rangle
$$

is the extended-real support function of $C$. The function $f : H \to \mathbb R$ is convex on all of $H$, $C^1$, bounded below, and strongly convex with parameter $M$. The operator $B$ is the singleton-valued gradient operator:

```math
B(x) = \{\nabla f(x)\}.
```

Finally, $\lambda\gt 0$, the sequence $\lambda_n$ is constantly equal to $\lambda$, $x : \mathbb N \to H$ is an `AlgorithmA` sequence for $A,B,\lambda$, and $x_n$ converges to some $x_\infty \in H$.

The conclusion is that there exist $n_0 \in \mathbb N$, $K\gt 0$, and $q\gt 0$ with $q\lt 1$ such that for every $n\ge n_0$,

```math
\|x_{n+1}-x_n\| \le K q^n.
```

Thus the successive differences of the algorithm decay at a geometric, or linear, rate.

## Lean proof
```lean
by
  classical
  let Fop : SetValuedOperator H H :=
    SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1)
  have hA0_tendsto : Filter.Tendsto A0 (𝓝 (0 : H)) (𝓝 (0 : H)) := by
    have hcont : ContinuousAt A0 (0 : H) := hA0_C2.continuous.continuousAt
    simpa [ContinuousAt, hA0_zero] using hcont
  have hlam_pos : ∀ n, lam_seq n > 0 := by
    intro n
    simpa [hlam_seq n] using hlam
  have hlam_nondec : ∀ n, lam_seq n ≤ lam_seq (n + 1) := by
    intro n
    rw [hlam_seq n, hlam_seq (n + 1)]
  have hA_pointwise : ∀ z, A z = {v | ∃ u ∈ subderivative (supportFunction C) z,
      ∃ w ∈ Fop z, v = u + w} := by
    intro z
    rw [hA]
    ext v
    constructor
    · intro hv
      change v ∈ subderivative (supportFunction C) z + Fop z at hv
      rw [Set.mem_add] at hv
      rcases hv with ⟨u, hu, w, hw, hsum⟩
      exact ⟨u, hu, w, hw, hsum.symm⟩
    · intro hv
      change v ∈ subderivative (supportFunction C) z + Fop z
      rw [Set.mem_add]
      rcases hv with ⟨u, hu, w, hw, hsum⟩
      exact ⟨u, hu, w, hw, hsum.symm⟩
  have hcor51_from_bridges
      (hAmax : IsMaximalMonotone A) (hAdom : A.dom = Set.univ) :
      ∃ n_star, ∀ n ≥ n_star, x (n+1) - x n ∈ normalCone C (-gradient f xInf) := by
    exact cor_5_1 C hC_closed hC_conv hC_polyhedron hC_bounded hC_int A0
      hA0_mono hA0_tendsto A hA_pointwise hAmax hAdom f hf_conv hf_C1 hinf B
      hB_eq_grad lam_seq hlam_pos hlam_nondec x halg xInf hxInf
  have hF_dom : Fop.dom = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rw [SetValuedOperator.mem_dom_iff]
      refine ⟨A0 z, ?_⟩
      simp [Fop, SetValuedOperator.ofFunction_apply_of_mem]
  have hF_max : IsMaximalMonotone Fop := by
    simpa [Fop] using hA0_mono
  let S : SetValuedOperator H H := subderivative (supportFunction C)
  haveI : FiniteDimensional ℝ H :=
    thm51_finiteDimensional_of_bounded_polyhedron_interior hC_polyhedron hC_bounded hC_int
  have hS_dom : S.dom = Set.univ := by
    have hC0 : (0 : H) ∈ C := interior_subset hC_int
    have hC_nonempty : C.Nonempty := ⟨0, hC0⟩
    have hC_compact : IsCompact C :=
      Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rw [SetValuedOperator.mem_dom_iff]
      rcases hC_compact.exists_isMaxOn hC_nonempty
          ((continuous_id.inner continuous_const).continuousOn :
            ContinuousOn (fun q : H => inner ℝ q z) C) with
        ⟨c, hc, hcmax⟩
      refine ⟨c, ?_⟩
      have hmax_le : ∀ q ∈ C, inner ℝ q z ≤ inner ℝ c z :=
        (isMaxOn_iff.mp hcmax)
      have hσz_le : supportFunction C z ≤ (inner ℝ c z : EReal) := by
        unfold supportFunction
        refine sSup_le ?_
        rintro _ ⟨q, hq, rfl⟩
        exact EReal.coe_le_coe_iff.mpr (hmax_le q hq)
      have hσz_ge : (inner ℝ c z : EReal) ≤ supportFunction C z :=
        thm51_inner_le_supportFunction hc
      have hσz_eq : supportFunction C z = (inner ℝ c z : EReal) :=
        le_antisymm hσz_le hσz_ge
      intro y
      have hy_ge : (inner ℝ c y : EReal) ≤ supportFunction C y :=
        thm51_inner_le_supportFunction hc
      have hleft_eq :
          (inner ℝ c z : EReal) + (inner ℝ c (y - z) : EReal) =
            (inner ℝ c y : EReal) := by
        rw [show inner ℝ c (y - z) = inner ℝ c y - inner ℝ c z by
          simp [inner_sub_right]]
        norm_num [← EReal.coe_sub, ← EReal.coe_add]
      change supportFunction C y ≥ supportFunction C z +
        (inner ℝ c (y - z) : EReal)
      rw [hσz_eq, hleft_eq]
      exact hy_ge
  have hS_max : IsMaximalMonotone S := by
    have hC0 : (0 : H) ∈ C := interior_subset hC_int
    have hC_nonempty : C.Nonempty := ⟨0, hC0⟩
    have hS_mono : IsMonotone S := by
      intro x y u hu v hv
      have hx_top : supportFunction C x ≠ ⊤ :=
        thm51_supportFunction_ne_top_of_bounded C hC_bounded x
      have hx_bot : supportFunction C x ≠ ⊥ :=
        thm51_supportFunction_ne_bot_of_nonempty hC_nonempty x
      have hy_top : supportFunction C y ≠ ⊤ :=
        thm51_supportFunction_ne_top_of_bounded C hC_bounded y
      have hy_bot : supportFunction C y ≠ ⊥ :=
        thm51_supportFunction_ne_bot_of_nonempty hC_nonempty y
      have hu_sub : ∀ z,
          supportFunction C z ≥ supportFunction C x +
            (inner ℝ u (z - x) : EReal) := by
        simpa [S, subderivative] using hu
      have hv_sub : ∀ z,
          supportFunction C z ≥ supportFunction C y +
            (inner ℝ v (z - y) : EReal) := by
        simpa [S, subderivative] using hv
      have hyx := hu_sub y
      have hxy := hv_sub x
      have hyx_bot : supportFunction C x + (inner ℝ u (y - x) : EReal) ≠ ⊥ :=
        EReal.add_ne_bot_iff.2 ⟨hx_bot, EReal.coe_ne_bot _⟩
      have hxy_bot : supportFunction C y + (inner ℝ v (x - y) : EReal) ≠ ⊥ :=
        EReal.add_ne_bot_iff.2 ⟨hy_bot, EReal.coe_ne_bot _⟩
      have hyx_real := EReal.toReal_le_toReal hyx hyx_bot hy_top
      have hxy_real := EReal.toReal_le_toReal hxy hxy_bot hx_top
      have hyx_add :
          (supportFunction C x + (inner ℝ u (y - x) : EReal)).toReal =
            (supportFunction C x).toReal + inner ℝ u (y - x) := by
        exact EReal.toReal_add hx_top hx_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      have hxy_add :
          (supportFunction C y + (inner ℝ v (x - y) : EReal)).toReal =
            (supportFunction C y).toReal + inner ℝ v (x - y) := by
        exact EReal.toReal_add hy_top hy_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      have h1 : (supportFunction C x).toReal + inner ℝ u (y - x) ≤
          (supportFunction C y).toReal := by
        simpa [hyx_add] using hyx_real
      have h2 : (supportFunction C y).toReal + inner ℝ v (x - y) ≤
          (supportFunction C x).toReal := by
        simpa [hxy_add] using hxy_real
      have hsum : inner ℝ (v - u) (x - y) ≤ 0 := by
        have hrewrite : inner ℝ v (x - y) + inner ℝ u (y - x) =
            inner ℝ (v - u) (x - y) := by
          rw [show y - x = -(x - y) by abel, inner_neg_right, inner_sub_left]
          ring
        nlinarith [h1, h2, hrewrite]
      have hneg : inner ℝ (v - u) (x - y) = - inner ℝ (u - v) (x - y) := by
        rw [show v - u = -(u - v) by abel, inner_neg_left]
      nlinarith
    have hres : ∀ z : H, ∃ p q : H, q ∈ S p ∧ z = p + q := by
      intro z
      let hCheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_conv
      let q : H := projectionPoint C hCheb z
      let p : H := z - q
      have hqC : q ∈ C := by
        simpa [q] using projectionPoint_mem C hCheb z
      refine ⟨p, q, ?_, ?_⟩
      · have hproj :
            q ∈ C ∧ ∀ r ∈ C, inner ℝ (r - q) (z - q) ≤ 0 := by
          simpa [q] using
            (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
              hC_nonempty hC_closed hC_conv (x := z) (p := q)).mp rfl
        have hmax_le : ∀ r ∈ C, inner ℝ r p ≤ inner ℝ q p := by
          intro r hr
          have h := hproj.2 r hr
          have hdiff : inner ℝ (r - q) p = inner ℝ r p - inner ℝ q p := by
            simp [inner_sub_left]
          dsimp [p] at hdiff
          have h' : inner ℝ r p - inner ℝ q p ≤ 0 := by
            simpa [p, hdiff] using h
          nlinarith
        have hσp_le : supportFunction C p ≤ (inner ℝ q p : EReal) := by
          unfold supportFunction
          refine sSup_le ?_
          rintro _ ⟨r, hr, rfl⟩
          exact EReal.coe_le_coe_iff.mpr (hmax_le r hr)
        have hσp_ge : (inner ℝ q p : EReal) ≤ supportFunction C p :=
          thm51_inner_le_supportFunction hqC
        have hσp_eq : supportFunction C p = (inner ℝ q p : EReal) :=
          le_antisymm hσp_le hσp_ge
        intro y
        have hy_ge : (inner ℝ q y : EReal) ≤ supportFunction C y :=
          thm51_inner_le_supportFunction hqC
        have hleft_eq :
            (inner ℝ q p : EReal) + (inner ℝ q (y - p) : EReal) =
              (inner ℝ q y : EReal) := by
          rw [show inner ℝ q (y - p) = inner ℝ q y - inner ℝ q p by
            simp [inner_sub_right]]
          norm_num [← EReal.coe_sub, ← EReal.coe_add]
        change supportFunction C y ≥ supportFunction C p +
          (inner ℝ q (y - p) : EReal)
        rw [hσp_eq, hleft_eq]
        exact hy_ge
      · simp [p]
    exact thm51_maximal_of_monotone_and_resolvent_surjective S hS_mono hres
  have hAmax : IsMaximalMonotone A := by
    have hdom : (interior S.dom ∩ Fop.dom).Nonempty := by
      refine ⟨0, ?_⟩
      simp [hS_dom, hF_dom]
    have hSFmax : IsMaximalMonotone (S + Fop) :=
      sum_maximal_monotone S Fop hS_max hF_max hdom
    simpa [S, Fop] using hA ▸ hSFmax
  have hAdom : A.dom = Set.univ := by
    rw [hA]
    change (S + Fop).dom = Set.univ
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rw [SetValuedOperator.mem_dom_iff]
      have hzS : z ∈ S.dom := by simpa [hS_dom]
      rcases (SetValuedOperator.mem_dom_iff S z).mp hzS with ⟨s, hs⟩
      refine ⟨s + A0 z, ?_⟩
      change s + A0 z ∈ S z + Fop z
      rw [Set.mem_add]
      refine ⟨s, hs, A0 z, ?_, rfl⟩
      simp [Fop, SetValuedOperator.ofFunction_apply_of_mem]
  rcases hcor51_from_bridges hAmax hAdom with ⟨nStar, hNC⟩
  have hStepSel := thm51_algorithm_step_selection A B lam_seq x halg
  let L : H →L[ℝ] H := fderiv ℝ A0 (0 : H)
  let xi : H := -gradient f xInf
  let v : ℕ → H := fun n => x (n + 2) - x (n + 1)
  let acc : ℕ → H := fun n => x (n + 2) - 2 • x (n + 1) + x n
  let z : ℕ → H := fun n => lam⁻¹ • v n
  have hxi_mem : xi ∈ C := by
    have hbase := hNC nStar le_rfl
    rw [mem_normalCone_iff_forall] at hbase
    exact hbase.1
  have hAlgSubgrad : ∀ n,
      -((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2))) ∈
        subderivative (supportFunction C) (z n) := by
    intro n
    rcases hStepSel n with ⟨a, b, ha, hb, heq⟩
    have hb_eq : b = gradient f (x (n + 2)) := by
      rw [hB_eq_grad] at hb
      simpa [SetValuedOperator.ofFunction_apply_of_mem] using hb
    have ha' := ha
    rw [hA_pointwise ((lam_seq n)⁻¹ • (x (n + 2) - x (n + 1)))] at ha'
    rcases ha' with ⟨s, hs, w, hw, ha_eq⟩
    have hw_eq : w = A0 ((lam_seq n)⁻¹ • (x (n + 2) - x (n + 1))) := by
      simpa [Fop, SetValuedOperator.ofFunction_apply_of_mem] using hw
    have heq' : ((lam^2)⁻¹ • acc n) + (s + A0 (z n)) +
        gradient f (x (n + 2)) = 0 := by
      simpa [acc, v, z, hlam_seq n, ha_eq, hw_eq, hb_eq] using heq
    have hs_eq :
        s = -((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2))) := by
      rw [eq_neg_iff_add_eq_zero]
      abel_nf at heq' ⊢
      exact heq'
    simpa [z, v, hlam_seq n, hs_eq] using hs
  have hAlgSupport : ∀ n,
      let p : H := -((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2)))
      p ∈ C ∧ z n ∈ normalCone C p := by
    intro n
    exact thm51_support_subgradient_mem_and_normal hC_polyhedron
      (interior_subset hC_int) (hAlgSubgrad n)
  have hNC39 : ∀ n,
      inner ℝ (((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2))) -
        gradient f xInf) (v n) ≤ 0 := by
    intro n
    let p : H := -((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2)))
    have hp := hAlgSupport n
    have hzNC : z n ∈ normalCone C p := hp.2
    rw [mem_normalCone_iff_forall] at hzNC
    have hineq : inner ℝ (z n) (xi - p) ≤ 0 := by
      simpa [real_inner_comm] using hzNC.2 xi hxi_mem
    have hzv : v n = lam • z n := by
      simp [z, v]
      rw [smul_smul]
      have hmul : lam * lam⁻¹ = 1 := by field_simp [ne_of_gt hlam]
      simp [hmul]
    have hterm : ((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2))) -
        gradient f xInf = xi - p := by
      simp [p, xi]
      abel
    rw [hterm, hzv]
    rw [inner_smul_right]
    have hcomm : inner ℝ (xi - p) (z n) = inner ℝ (z n) (xi - p) :=
      real_inner_comm _ _
    rw [hcomm]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlam) hineq
  have hNCTail : ∀ n ≥ nStar, xInf - x (n + 2) ∈ normalCone C xi := by
    intro n hn
    rw [mem_normalCone_iff_forall]
    constructor
    · exact hxi_mem
    · intro y hy
      let d : H := y - xi
      have hpartial : ∀ K : ℕ, inner ℝ (x (n + 2 + K) - x (n + 2)) d ≤ 0 := by
        intro K
        induction K with
        | zero => simp
        | succ K ih =>
            have hinc : x (n + 2 + (K + 1)) - x (n + 2) =
                (x (n + 2 + K) - x (n + 2)) +
                  (x (n + 2 + (K + 1)) - x (n + 2 + K)) := by
              abel
            have hstep_mem :
                x (n + 2 + K + 1) - x (n + 2 + K) ∈ normalCone C xi := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hNC (n + 2 + K) (by omega : nStar ≤ n + 2 + K)
            have hstep_ineq :
                inner ℝ (x (n + 2 + (K + 1)) - x (n + 2 + K)) d ≤ 0 := by
              rw [mem_normalCone_iff_forall] at hstep_mem
              have hstep_fun :
                  ∀ y ∈ C, inner ℝ (x (n + 2 + (K + 1)) - x (n + 2 + K))
                    (y - xi) ≤ 0 := by
                intro y' hy'
                simpa [real_inner_comm] using hstep_mem.2 y' hy'
              simpa [d] using hstep_fun y hy
            rw [hinc, inner_add_left]
            exact add_nonpos ih hstep_ineq
      have hshift : Tendsto (fun K : ℕ => n + 2 + K) atTop atTop :=
        Filter.tendsto_atTop_mono (fun K => Nat.le_add_left K (n + 2)) tendsto_id
      have hxshift : Tendsto (fun K : ℕ => x (n + 2 + K)) atTop (𝓝 xInf) :=
        hxInf.comp hshift
      have hlimH : Tendsto (fun K : ℕ => x (n + 2 + K) - x (n + 2)) atTop
          (𝓝 (xInf - x (n + 2))) := hxshift.sub tendsto_const_nhds
      have hlimR :
          Tendsto (fun K : ℕ => inner ℝ (x (n + 2 + K) - x (n + 2)) d) atTop
            (𝓝 (inner ℝ (xInf - x (n + 2)) d)) := by
        have hcont : Continuous (fun w : H => inner ℝ w d) :=
          continuous_id.inner continuous_const
        exact hcont.tendsto _ |>.comp hlimH
      rw [real_inner_comm]
      exact isClosed_Iic.mem_of_tendsto hlimR (Eventually.of_forall hpartial)
  have hNC31 : ∀ n ≥ nStar,
      inner ℝ (((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2))) -
        gradient f xInf) (x (n + 2) - xInf) ≤ 0 := by
    intro n hn
    let p : H := -((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2)))
    have hp := hAlgSupport n
    have htail : xInf - x (n + 2) ∈ normalCone C xi := hNCTail n hn
    have htail_ineq : inner ℝ (xInf - x (n + 2)) (p - xi) ≤ 0 := by
      rw [mem_normalCone_iff_forall] at htail
      have htail_fun : ∀ y ∈ C, inner ℝ (xInf - x (n + 2)) (y - xi) ≤ 0 := by
        intro y' hy'
        simpa [real_inner_comm] using htail.2 y' hy'
      exact htail_fun p hp.1
    have hterm : ((lam^2)⁻¹ • acc n + A0 (z n) + gradient f (x (n + 2))) -
        gradient f xInf = xi - p := by
      dsimp [p, xi]
      abel
    have hpair : inner ℝ (xi - p) (x (n + 2) - xInf) =
        inner ℝ (xInf - x (n + 2)) (p - xi) := by
      rw [show xi - p = -(p - xi) by abel]
      rw [show x (n + 2) - xInf = -(xInf - x (n + 2)) by abel]
      rw [inner_neg_left, inner_neg_right, neg_neg]
      exact real_inner_comm _ _
    rw [hterm, hpair]
    exact htail_ineq
  have hshift1 : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have hshift2 : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 2) tendsto_id
  have hx_shift1 : Tendsto (fun n : ℕ => x (n + 1)) atTop (𝓝 xInf) :=
    hxInf.comp hshift1
  have hx_shift2 : Tendsto (fun n : ℕ => x (n + 2)) atTop (𝓝 xInf) :=
    hxInf.comp hshift2
  have hv_tendsto : Tendsto v atTop (𝓝 (0 : H)) := by
    simpa [v] using hx_shift2.sub hx_shift1
  have hz_tendsto : Tendsto z atTop (𝓝 (0 : H)) := by
    have hc : Tendsto (fun _ : ℕ => lam⁻¹) atTop (𝓝 lam⁻¹) := tendsto_const_nhds
    simpa [z] using hc.smul hv_tendsto
  have he_tendsto : Tendsto (fun n : ℕ => x (n + 1) - xInf) atTop (𝓝 (0 : H)) := by
    have hcInf : Tendsto (fun _ : ℕ => xInf) atTop (𝓝 xInf) := tendsto_const_nhds
    simpa using hx_shift1.sub hcInf
  rcases thm51_A0_quadratic_remainder_eventually A0 hA0_C2 hA0_zero with
    ⟨C0, hC0_pos, hA0_rem_nhds⟩
  have hA0_rem_z : ∀ᶠ n in atTop,
      ‖A0 (z n) - L (z n)‖ ≤ C0 * ‖z n‖^2 := by
    simpa [L] using hz_tendsto hA0_rem_nhds
  have he2_tendsto : Tendsto (fun n : ℕ => x (n + 2) - xInf) atTop (𝓝 (0 : H)) := by
    have hcInf : Tendsto (fun _ : ℕ => xInf) atTop (𝓝 xInf) := tendsto_const_nhds
    simpa using hx_shift2.sub hcInf
  have hnorm_small_e2 : ∀ {eps : ℝ}, 0 < eps →
      ∀ᶠ n in atTop, ‖x (n + 2) - xInf‖ ≤ eps := by
    intro eps heps
    have hnorm : Tendsto (fun n : ℕ => ‖x (n + 2) - xInf‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.tendsto (0 : H)).comp he2_tendsto
    have hev := hnorm (Metric.ball_mem_nhds (0 : ℝ) heps)
    filter_upwards [hev] with n hn
    have hlt : ‖x (n + 2) - xInf‖ < eps := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hn
    exact le_of_lt hlt
  have hnorm_small_v : ∀ {eps : ℝ}, 0 < eps →
      ∀ᶠ n in atTop, ‖v n‖ ≤ eps := by
    intro eps heps
    have hnorm : Tendsto (fun n : ℕ => ‖v n‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.tendsto (0 : H)).comp hv_tendsto
    have hev := hnorm (Metric.ball_mem_nhds (0 : ℝ) heps)
    filter_upwards [hev] with n hn
    have hlt : ‖v n‖ < eps := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hn
    exact le_of_lt hlt
  have hz_norm_sq : ∀ n : ℕ, ‖z n‖ ^ 2 = lam⁻¹ ^ 2 * ‖v n‖ ^ 2 := by
    intro n
    have hz_norm : ‖z n‖ = lam⁻¹ * ‖v n‖ := by
      dsimp [z]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    rw [hz_norm]
    ring
  have hA0_pair_eventual : ∀ η > 0, ∀ᶠ n in atTop,
      |inner ℝ (A0 (z n) - L (z n)) (x (n + 2) - xInf)|
        ≤ η / lam^2 * ‖v n‖^2 ∧
      |inner ℝ (A0 (z n) - L (z n)) (v n)| ≤ η / lam * ‖v n‖^2 := by
    intro η hη
    have heps1 : 0 < η / C0 := div_pos hη hC0_pos
    have heps2 : 0 < η * lam / C0 := div_pos (mul_pos hη hlam) hC0_pos
    filter_upwards [hA0_rem_z, hnorm_small_e2 heps1, hnorm_small_v heps2] with
      n hremn he2small hvsmall
    constructor
    · have hcs := abs_real_inner_le_norm (A0 (z n) - L (z n)) (x (n + 2) - xInf)
      have hmul1 : ‖A0 (z n) - L (z n)‖ * ‖x (n + 2) - xInf‖ ≤
          (C0 * ‖z n‖ ^ 2) * ‖x (n + 2) - xInf‖ := by
        exact mul_le_mul_of_nonneg_right hremn (norm_nonneg _)
      have hC0e : C0 * ‖x (n + 2) - xInf‖ ≤ η := by
        calc
          C0 * ‖x (n + 2) - xInf‖ ≤ C0 * (η / C0) :=
            mul_le_mul_of_nonneg_left he2small (le_of_lt hC0_pos)
          _ = η := by field_simp [ne_of_gt hC0_pos]
      have hnon : 0 ≤ lam⁻¹ ^ 2 * ‖v n‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hmul2 := mul_le_mul_of_nonneg_right hC0e hnon
      have htarget : (C0 * ‖z n‖ ^ 2) * ‖x (n + 2) - xInf‖ ≤
          η / lam^2 * ‖v n‖^2 := by
        rw [hz_norm_sq n]
        convert hmul2 using 1
        · ring
        · field_simp [pow_two, ne_of_gt hlam]
      exact le_trans hcs (le_trans hmul1 htarget)
    · have hcs := abs_real_inner_le_norm (A0 (z n) - L (z n)) (v n)
      have hmul1 : ‖A0 (z n) - L (z n)‖ * ‖v n‖ ≤
          (C0 * ‖z n‖ ^ 2) * ‖v n‖ := by
        exact mul_le_mul_of_nonneg_right hremn (norm_nonneg _)
      have hC0v : C0 * ‖v n‖ ≤ η * lam := by
        calc
          C0 * ‖v n‖ ≤ C0 * (η * lam / C0) :=
            mul_le_mul_of_nonneg_left hvsmall (le_of_lt hC0_pos)
          _ = η * lam := by field_simp [ne_of_gt hC0_pos]
      have hnon : 0 ≤ lam⁻¹ ^ 2 * ‖v n‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hmul2 := mul_le_mul_of_nonneg_right hC0v hnon
      have htarget : (C0 * ‖z n‖ ^ 2) * ‖v n‖ ≤ η / lam * ‖v n‖^2 := by
        rw [hz_norm_sq n]
        convert hmul2 using 1
        · ring
        · field_simp [pow_two, ne_of_gt hlam]
      exact le_trans hcs (le_trans hmul1 htarget)
  sorry
```

## Proof explanation
The supplied proof is not complete: it ends with `sorry` after establishing several auxiliary facts. In particular, the final geometric bound $`\|x_{n+1}-x_n\|\le Kq^n`$ is not proved in the provided source. The visible proof prepares the main estimates and normal-cone inequalities that one would expect to use in the missing final argument.

The proof begins with `classical` and introduces the singleton-valued operator

$$
F_{\mathrm{op}} = \mathrm{ofFunction}(\mathrm{univ}, x \mapsto A_0(x)).
$$

For every $z\in H$, this satisfies

```math
F_{\mathrm{op}}(z) = \{A_0(z)\}.
```

The lemma `SetValuedOperator.ofFunction_apply_of_mem` is the reason: on the full domain, the set-valued operator associated to a function has the singleton value of that function at the point.

Next the proof shows that $A_0$ tends to $0$ at $0$. Since $A_0$ is $C^2$, it is continuous, hence continuous at $0$, and $A_0(0)=0$, so

$$
A_0(y) \to 0 \quad \text{as } y\to 0.
$$

This is the continuity hypothesis needed for `cor_5_1`.

The proof also records that the constant step sequence is positive and nondecreasing:

$$
\lambda_n = \lambda >0, \qquad \lambda_n \le \lambda_{n+1}.
$$

Then it rewrites the definition of $A$,

$$
A = \partial \sigma_C + F_{\mathrm{op}},
$$

into the pointwise membership form

$$
v \in A(z)
\iff
\exists u \in \partial \sigma_C(z),\ \exists w \in F_{\mathrm{op}}(z),\ v = u+w.
$$

This uses the set-addition membership lemma `Set.mem_add` and is exactly the form required by the cited corollary `cor_5_1`.

The local lemma `hcor51_from_bridges` then calls `cor_5_1`. Specialized to the present variables, `cor_5_1` says the following. Under the closed convex polyhedron assumptions on $C$, the boundedness and interior condition, the maximal monotonicity and continuity of $A_0$, the representation of $A$ as $\partial\sigma_C + A_0$, maximal monotonicity of $A$, full domain of $A$, the convex $C^1$ lower-bounded function $f$, the identification $B=\nabla f$, positive nondecreasing step sizes, the `AlgorithmA` relation, and convergence $x_n\to x_\infty$, there is an index $n_\star$ such that for all $n\ge n_\star$,

$$
x_{n+1}-x_n \in N_C(-\nabla f(x_\infty)).
$$

Here $N_C$ is the normal cone to $C$. This is the key asymptotic normal-cone condition.

The proof then supplies the two missing hypotheses needed for `cor_5_1`: maximal monotonicity of $A$ and $A.\mathrm{dom}=H$.

First it treats $F_{\mathrm{op}}$. Its domain is all of $H$, because for every $z$,

$$
A_0(z)\in F_{\mathrm{op}}(z),
$$

so $F_{\mathrm{op}}(z)$ is nonempty. The lemma `SetValuedOperator.mem_dom_iff` says $z\in F_{\mathrm{op}}.\mathrm{dom}$ exactly when $F_{\mathrm{op}}(z)$ is nonempty. Also, $F_{\mathrm{op}}$ is maximal monotone by the hypothesis `hA0_mono`, since $F_{\mathrm{op}}$ is precisely the singleton-valued operator associated to $A_0$.

Next the proof defines

$$
S = \partial \sigma_C.
$$

It proves that $S$ is maximal monotone. The first step is finite-dimensionality. The theorem `thm51_finiteDimensional_of_bounded_polyhedron_interior` says that if $C$ is a bounded convex polyhedron and $0\in \mathrm{int} C$, then $H$ is finite-dimensional. This is used so that the closed bounded set $C$ is compact.

The proof then shows that $S$ has full domain. Since $0\in C$, the set $C$ is nonempty. Since $C$ is closed and bounded in finite dimension, $C$ is compact. For any fixed $z\in H$, the continuous function

$$
q \mapsto \langle q,z\rangle
$$

attains a maximum on $C$ at some $c\in C$. Hence

$$
\sigma_C(z) = \langle c,z\rangle.
$$

The lemma `thm51_inner_le_supportFunction` says that if $c\in C$, then

$$
\langle c,y\rangle \le \sigma_C(y)
$$

for every $y$. Therefore

$$
\sigma_C(y) \ge \langle c,z\rangle + \langle c,y-z\rangle
= \langle c,y\rangle,
$$

which says exactly that $c\in \partial\sigma_C(z)=S(z)$. Thus every $S(z)$ is nonempty, so $S.\mathrm{dom}=H$.

The proof next establishes monotonicity of $S$. Suppose $u\in S(x)$ and $v\in S(y)$. By definition of subgradient,

$$
\sigma_C(y) \ge \sigma_C(x)+\langle u,y-x\rangle,
$$

and

$$
\sigma_C(x) \ge \sigma_C(y)+\langle v,x-y\rangle.
$$

The support function is finite here: `thm51_supportFunction_ne_top_of_bounded` gives $\sigma_C(\cdot)\ne +\infty$, and `thm51_supportFunction_ne_bot_of_nonempty` gives $\sigma_C(\cdot)\ne -\infty$. Hence the extended-real inequalities can be converted to real inequalities by applying `toReal`. Adding them yields

$$
\langle u,y-x\rangle+\langle v,x-y\rangle \le 0.
$$

Equivalently,

$$
\langle v-u,x-y\rangle \le 0,
$$

and therefore

$$
\langle u-v,x-y\rangle \ge 0.
$$

This is exactly the set-valued monotonicity of $S$.

The proof then proves the resolvent-surjectivity condition for $S$:

$$
\forall z\in H,\ \exists p,q\in H,\ q\in S(p) \text{ and } z=p+q.
$$

It uses the projection onto the closed convex set $C$. Since $C$ is nonempty, closed, and convex, the theorem `isChebyshev_of_nonempty_isClosed_convex` says $C$ is Chebyshev, i.e. every point has a unique nearest point in $C$. Let

$$
q = P_C(z), \qquad p = z-q.
$$

The projection point satisfies $q\in C$, and the variational characterization of projection,

$$
\langle r-q,z-q\rangle \le 0 \qquad \text{for all } r\in C,
$$

is supplied by
`eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex`.
Since $p=z-q$, this says

$$
\langle r,p\rangle \le \langle q,p\rangle \qquad \text{for all } r\in C,
$$

so $q$ maximizes $r\mapsto \langle r,p\rangle$ on $C$. Hence

$$
\sigma_C(p)=\langle q,p\rangle.
$$

Using `thm51_inner_le_supportFunction` again, $\langle q,y\rangle\le \sigma_C(y)$ for all $y$, so

$$
\sigma_C(y) \ge \sigma_C(p)+\langle q,y-p\rangle.
$$

Thus $q\in S(p)$, and by construction $z=p+q$. The theorem
`thm51_maximal_of_monotone_and_resolvent_surjective` then gives that $S$, being monotone and resolvent-surjective, is maximal monotone.

With $S$ and $F_{\mathrm{op}}$ both maximal monotone, the proof uses `sum_maximal_monotone`. That theorem says that if $A$ and $B$ are maximal monotone and

$$
(\mathrm{int} A.\mathrm{dom}\cap B.\mathrm{dom})\ne\varnothing,
$$

then $A+B$ is maximal monotone. Here both $S.\mathrm{dom}$ and $F_{\mathrm{op}}.\mathrm{dom}$ are all of $H$, so the intersection condition is witnessed by $0$. Therefore $S+F_{\mathrm{op}}$ is maximal monotone, and since $A=S+F_{\mathrm{op}}$, $A$ is maximal monotone.

The proof also proves $A.\mathrm{dom}=H$. For every $z$, $S(z)$ is nonempty, and $A_0(z)\in F_{\mathrm{op}}(z)$, so $S(z)+F_{\mathrm{op}}(z)=A(z)$ is nonempty. Thus $A.\mathrm{dom}=H$.

Now the hypotheses of `hcor51_from_bridges` are available, so the proof obtains an index $n_\star$ such that for all $n\ge n_\star$,

$$
x_{n+1}-x_n \in N_C(-\nabla f(x_\infty)).
$$

The proof then turns to the algorithm step. It defines

$$
L = DA_0(0), \qquad \xi = -\nabla f(x_\infty),
$$

$$
v_n = x_{n+2}-x_{n+1}, \qquad
acc_n = x_{n+2}-2x_{n+1}+x_n, \qquad
z_n = \lambda^{-1}v_n.
$$

The theorem `thm51_algorithm_step_selection` says that for each $n$ there exist $a\in A(z_n)$ and $b\in B(x_{n+2})$ such that

$$
(\lambda^2)^{-1}acc_n + a + b = 0.
$$

Since $B=\nabla f$, one has

$$
b = \nabla f(x_{n+2}).
$$

Since $a\in A(z_n)=\partial\sigma_C(z_n)+F_{\mathrm{op}}(z_n)$, one can write

$$
a = s + A_0(z_n)
$$

with $s\in \partial\sigma_C(z_n)$. The equation above becomes

$$
(\lambda^2)^{-1}acc_n + s + A_0(z_n)+\nabla f(x_{n+2})=0,
$$

so

$$
s = -\bigl((\lambda^2)^{-1}acc_n + A_0(z_n)+\nabla f(x_{n+2})\bigr).
$$

Thus the vector

$$
p_n = -\bigl((\lambda^2)^{-1}acc_n + A_0(z_n)+\nabla f(x_{n+2})\bigr)
$$

belongs to $\partial\sigma_C(z_n)=S(z_n)$.

The proof then applies `thm51_support_subgradient_mem_and_normal`. This lemma says that if $C$ is a convex polyhedron, $0\in C$, and $\xi_0\in \partial\sigma_C(v)$, then

$$
\xi_0\in C \quad\text{and}\quad v\in N_C(\xi_0).
$$

Specializing to $p_n\in \partial\sigma_C(z_n)$, the proof obtains

$$
p_n\in C \quad\text{and}\quad z_n\in N_C(p_n).
$$

From $z_n\in N_C(p_n)$ and $\xi\in C$, the normal-cone inequality gives

$$
\langle \xi-p_n,z_n\rangle\le 0.
$$

Since $v_n=\lambda z_n$ and $\xi-p_n$ equals

$$
((\lambda^2)^{-1}acc_n + A_0(z_n)+\nabla f(x_{n+2}))-\nabla f(x_\infty),
$$

this becomes

```math
\left\langle
((\lambda^2)^{-1}acc_n + A_0(z_n)+\nabla f(x_{n+2}))
-\nabla f(x_\infty),\, v_n
\right\rangle \le 0.
```

This is one of the two central discrete variational inequalities.

The proof next derives a second normal-cone fact for the tail:

$$
x_\infty - x_{n+2} \in N_C(\xi) \qquad \text{for all } n\ge n_\star.
$$

For any $y\in C$, set $d=y-\xi$. For each $k\ge n_\star$, the corollary gives

$$
x_{k+1}-x_k \in N_C(\xi),
$$

hence

$$
\langle x_{k+1}-x_k,d\rangle \le 0.
$$

Summing these inequalities from $k=n+2$ to $n+2+K-1$ yields

$$
\langle x_{n+2+K}-x_{n+2},d\rangle \le 0.
$$

Letting $K\to\infty$ and using $x_{n+2+K}\to x_\infty$, the limit preserves the inequality because $(-\infty,0]$ is closed. Therefore

$$
\langle x_\infty-x_{n+2},d\rangle \le 0
$$

for every $y\in C$, which is exactly $x_\infty-x_{n+2}\in N_C(\xi)$.

Using this tail normal vector and the fact that $p_n\in C$, the proof obtains

$$
\langle p_n-\xi,x_\infty-x_{n+2}\rangle \le 0.
$$

After rearranging inner products, this gives the second discrete variational inequality:

```math
\left\langle
((\lambda^2)^{-1}acc_n + A_0(z_n)+\nabla f(x_{n+2}))
-\nabla f(x_\infty),\, x_{n+2}-x_\infty
\right\rangle \le 0.
```

The proof then records several convergence consequences. Since $x_n\to x_\infty$,

$$
x_{n+1}\to x_\infty, \qquad x_{n+2}\to x_\infty,
$$

so

$$
v_n = x_{n+2}-x_{n+1}\to 0, \qquad
z_n = \lambda^{-1}v_n\to 0.
$$

Also

$$
x_{n+1}-x_\infty\to 0, \qquad
x_{n+2}-x_\infty\to 0.
$$

Consequently, for every $\varepsilon\gt 0$, eventually

```math
\|x_{n+2}-x_\infty\|\le \varepsilon, \qquad
\|v_n\|\le \varepsilon.
```

The proof then uses the quadratic Taylor remainder for $A_0$. The theorem
`thm51_A0_quadratic_remainder_eventually` says that if $A_0$ is $C^2$ and $A_0(0)=0$, then there exists $C_0\gt 0$ such that eventually near $0$,

```math
\|A_0(y)-L y\| \le C_0\|y\|^2,
```

where $L=DA_0(0)$. Since $z_n\to 0$, this becomes eventually

```math
\|A_0(z_n)-L z_n\| \le C_0\|z_n\|^2.
```

Moreover, because $z_n=\lambda^{-1}v_n$ and $\lambda\gt 0$,

```math
\|z_n\|^2 = \lambda^{-2}\|v_n\|^2.
```

Combining this quadratic remainder with Cauchy-Schwarz,

```math
|\langle A_0(z_n)-L z_n,w\rangle|
\le \|A_0(z_n)-L z_n\|\,\|w\|,
```

and the smallness of $x_{n+2}-x_\infty$ and $v_n$, the proof establishes the eventual estimates

```math
|\langle A_0(z_n)-L z_n, x_{n+2}-x_\infty\rangle|
\le \frac{\eta}{\lambda^2}\|v_n\|^2
```

and

```math
|\langle A_0(z_n)-L z_n, v_n\rangle|
\le \frac{\eta}{\lambda}\|v_n\|^2
```

for every $\eta\gt 0$, eventually in $n$. These estimates say that the nonlinear remainder $A_0(z_n)-L z_n$ is quadratically small in the increment $v_n$.

At this point the provided proof ends with `sorry`. The final step, which would combine the two normal-cone inequalities, the strong convexity of $f$, the coercivity of $L=DA_0(0)$, and the quadratic remainder estimates to deduce

```math
\|x_{n+1}-x_n\|\le K q^n
```

for some $K\gt 0$, $0\lt q\lt 1$, and all large $n$, is not present in the supplied source. In particular, the hypotheses $m\gt 0$, `hA0_coercive`, and `hf_strongConv` are not used in the visible part of the proof. Thus the statement of `thm_5_1` is a geometric-decay theorem, but the provided Lean proof leaves its final conclusion unproved.

