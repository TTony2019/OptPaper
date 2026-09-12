## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/cor_2.lean`

## Lean statement
```lean
theorem cor_4_1 [FiniteDimensional ℝ H] (C : Set H) (hC_closed : IsClosed C) (hC_conv : Convex ℝ C)
    (hC_bounded : Bornology.IsBounded C) (hC_int : (0 : H) ∈ interior C)
    (A0 : H → H) (hA0_mono : IsMaximalMonotone
      (SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1)))
    (η : ℝ) (hη : η > 0) (α : ℝ) (hα : α ≥ 0)
    (h_A0_growth : ∀ x, ‖x‖ ≤ η → ‖A0 x‖ ≤ α * ‖x‖)
    (A : SetValuedOperator H H) (hA : A = subderivative (supportFunction C) +
      SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1))
    (f : H → ℝ) (hf_C11 : IsC11 f) (hinf : ∃ m, ∀ x, f x ≥ m)
    (M : ℝ) (hf_strongConv : IsStronglyConvex f M)
    (B : SetValuedOperator H H) (hB_eq_grad : B =
      SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => gradient f x.1))
    (lam : ℝ) (hlam : lam > 0) (lam_seq : ℕ → ℝ) (hlam_seq : ∀ n, lam_seq n = lam)
    (x : ℕ → H) (halg : AlgorithmA A B x lam_seq) (xInf : H) (hxInf : Tendsto x atTop (𝓝 xInf))
    (h_smooth : IsSmoothAt C (-gradient f xInf)) :
    (((∃ N, ∀ n ≥ N, x n = x (N)) ∨
      (∃ (n0 : ℕ),
        (∀ q1, 0 < q1 → q1 < 1 → q1 < 1 / (α * lam + 1) →
          ∃ (C1 : ℝ), C1 > 0 ∧ ∀ n ≥ n0, ‖x n - xInf‖ ≥ C1 * q1 ^ n) ∧
        (∀ q2, 0 < q2 → q2 < 1 → q2 > α / (α + M * lam) →
          ∃ (C2 : ℝ), C2 > 0 ∧ ∀ n ≥ n0, ∑' (k : ℕ), ‖x (n+k) - xInf‖ ≤ C2 * q2 ^ n))) ∧
    (α ^ 2 < M → (∃ N, ∀ n ≥ N, x n = x (N))))
```

## Statement explanation
The theorem `cor_4_1` is a convergence result for an inertial proximal algorithm with dry friction, stated in a finite-dimensional real inner product space $H$. It combines a finite-termination alternative with geometric lower and upper tail estimates.

The data and hypotheses are as follows. The set $C\subseteq H$ is closed, convex, bounded, and contains $0$ in its interior. The map $A0:H\to H$ is single-valued, but it is regarded as the set-valued operator

```math
F(x)=\{A0(x)\}
```

on all of $H$, and this $F$ is assumed maximal monotone. The constants satisfy $\eta\gt 0$, $\alpha\ge 0$, and the local linear-growth condition

```math
\|A0(x)\|\le \alpha\|x\|\qquad\text{whenever }\|x\|\le \eta .
```

The set-valued operator $A$ is assumed to be

$$
A=\partial\sigma_C+F,
$$

where $\sigma_C$ is the support function of $C$,

$$
\sigma_C(y)=\sup_{z\in C}\langle z,y\rangle,
$$

and $\partial\sigma_C$ is the subderivative of this extended-real-valued support function. Thus

```math
A(x)=\partial\sigma_C(x)+\{A0(x)\}.
```

The function $f:H\to\mathbb R$ is $C^{1,1}$, bounded below, and $M$-strongly convex. Here $M$-strong convexity includes $M\gt 0$, $C^1$-regularity, and the gradient inequality

```math
\langle \nabla f(x)-\nabla f(y),x-y\rangle\ge M\|x-y\|^2 .
```

The operator $B$ is the gradient operator

```math
B(x)=\{\nabla f(x)\}.
```

The positive number $\lambda\gt 0$ is the constant step size, since $\lambda_n=\lambda$ for every $n$. The sequence $x:\mathbb N\to H$ is assumed to satisfy the algorithm relation `AlgorithmA A B x lam_seq`, and it converges to $x_\infty\in H$. Finally, the smoothness hypothesis is

$$
\mathrm{IsSmoothAt}\bigl(C,-\nabla f(x_\infty)\bigr),
$$

meaning that $-\nabla f(x_\infty)\in C$ and the normal cone of $C$ at that point is a single ray.

The conclusion is the conjunction

$$
\Bigl(
(\exists N,\ \forall n\ge N,\ x_n=x_N)
\ \lor
\exists n_0,\ \text{two geometric estimates}
\Bigr)
\ \land
\Bigl(\alpha^2<M\ \Longrightarrow\ \exists N,\ \forall n\ge N,\ x_n=x_N\Bigr).
$$

The second estimate is described explicitly as follows. For every $q_1$ with

$$
0<q_1<1,\qquad q_1<\frac{1}{\alpha\lambda+1},
$$

there is $C_1\gt 0$ such that

```math
\|x_n-x_\infty\|\ge C_1 q_1^n
```

for all sufficiently large $n$. This is a lower bound, so convergence cannot be faster than the geometric rate $1/(\alpha\lambda+1)$. Likewise, for every $q_2$ with

$$
0<q_2<1,\qquad q_2>\frac{\alpha}{\alpha+M\lambda},
$$

there is $C_2\gt 0$ such that

```math
\sum_{k\ge 0}\|x_{n+k}-x_\infty\|\le C_2 q_2^n
```

for all sufficiently large $n$. This bounds the tail sum from above, giving an upper geometric decay rate. Finally, if $\alpha^2\lt M$, the sequence is eventually constant.

## Lean proof
```lean
by
  classical
  let S : SetValuedOperator H H := subderivative (supportFunction C)
  let F : SetValuedOperator H H :=
    SetValuedOperator.ofFunction Set.univ (fun x : (Set.univ : Set H) => A0 x.1)
  let fE : H → EReal := fun y => (f y : EReal)
  have hA0_zero : A0 (0 : H) = 0 := by
    have h := h_A0_growth (0 : H) (by simpa using le_of_lt hη)
    have hle : ‖A0 (0 : H)‖ ≤ 0 := by
      simpa using h
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  have hS0 : S (0 : H) = C := by
    have hC0 : (0 : H) ∈ C := interior_subset hC_int
    have hC_nonempty : C.Nonempty := ⟨0, hC0⟩
    ext v
    constructor
    · intro hv
      by_contra hvC
      rcases exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
          hC_nonempty hC_closed hC_conv hvC with ⟨u, _hu_ne, hsep⟩
      have hv_sub : ∀ y,
          supportFunction C y ≥ supportFunction C (0 : H) +
            (inner ℝ v (y - (0 : H)) : EReal) := by
        simpa [S, subderivative] using hv
      have hge : (inner ℝ v u : EReal) ≤ supportFunction C u := by
        have h := hv_sub u
        simpa [cor41_supportFunction_zero C hC0] using h
      have hlt : supportFunction C u < (inner ℝ v u : EReal) := by
        simpa [supportFunction, innerSupremumOn] using hsep
      exact not_lt_of_ge hge hlt
    · intro hvC
      intro y
      have hC0' : supportFunction C (0 : H) = 0 := cor41_supportFunction_zero C hC0
      have hle : (inner ℝ v y : EReal) ≤ supportFunction C y :=
        cor41_inner_le_supportFunction hvC
      simpa [S, subderivative, hC0'] using hle
  have hS_subset : ∀ z, S z ⊆ C := by
    have hC0 : (0 : H) ∈ C := interior_subset hC_int
    have hC_nonempty : C.Nonempty := ⟨0, hC0⟩
    intro z v hv
    have hz_top : supportFunction C z ≠ ⊤ :=
      cor41_supportFunction_ne_top_of_bounded C hC_bounded z
    have hz_bot : supportFunction C z ≠ ⊥ :=
      cor41_supportFunction_ne_bot_of_nonempty hC_nonempty z
    have hv_sub : ∀ y,
        supportFunction C y ≥ supportFunction C z +
          (inner ℝ v (y - z) : EReal) := by
      simpa [S, subderivative] using hv
    have hv_zero : v ∈ S (0 : H) := by
      intro y
      have hy_top : supportFunction C y ≠ ⊤ :=
        cor41_supportFunction_ne_top_of_bounded C hC_bounded y
      have hy_bot : supportFunction C y ≠ ⊥ :=
        cor41_supportFunction_ne_bot_of_nonempty hC_nonempty y
      have hleft_le : supportFunction C z + (inner ℝ v y : EReal) ≤
          supportFunction C (z + y) := by
        have h := hv_sub (z + y)
        simpa [add_sub_cancel_left] using h
      have hright_le : supportFunction C (z + y) ≤
          supportFunction C z + supportFunction C y := by
        simpa [add_comm] using cor41_supportFunction_add_le C z y
      have hsum_le : supportFunction C z + (inner ℝ v y : EReal) ≤
          supportFunction C z + supportFunction C y :=
        le_trans hleft_le hright_le
      have hleft_bot : supportFunction C z + (inner ℝ v y : EReal) ≠ ⊥ :=
        EReal.add_ne_bot_iff.2 ⟨hz_bot, EReal.coe_ne_bot _⟩
      have hright_top : supportFunction C z + supportFunction C y ≠ ⊤ :=
        EReal.add_ne_top hz_top hy_top
      have hreal_le := EReal.toReal_le_toReal hsum_le hleft_bot hright_top
      have hleft_toReal :
          (supportFunction C z + (inner ℝ v y : EReal)).toReal =
            (supportFunction C z).toReal + inner ℝ v y := by
        exact EReal.toReal_add hz_top hz_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      have hright_toReal :
          (supportFunction C z + supportFunction C y).toReal =
            (supportFunction C z).toReal + (supportFunction C y).toReal := by
        exact EReal.toReal_add hz_top hz_bot hy_top hy_bot
      have hreal : inner ℝ v y ≤ (supportFunction C y).toReal := by
        nlinarith [by simpa [hleft_toReal, hright_toReal] using hreal_le]
      have hE : (inner ℝ v y : EReal) ≤ ((supportFunction C y).toReal : EReal) :=
        EReal.coe_le_coe_iff.mpr hreal
      simpa [S, subderivative, cor41_supportFunction_zero C hC0,
        EReal.coe_toReal hy_top hy_bot] using hE
    simpa [hS0] using hv_zero
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
          ((continuous_id.inner continuous_const).continuousOn : ContinuousOn (fun q : H => inner ℝ q z) C) with
        ⟨c, hc, hcmax⟩
      refine ⟨c, ?_⟩
      have hmax_le : ∀ q ∈ C, inner ℝ q z ≤ inner ℝ c z := by
        exact (isMaxOn_iff.mp hcmax)
      have hσz_le : supportFunction C z ≤ (inner ℝ c z : EReal) := by
        unfold supportFunction
        refine sSup_le ?_
        rintro _ ⟨q, hq, rfl⟩
        exact EReal.coe_le_coe_iff.mpr (hmax_le q hq)
      have hσz_ge : (inner ℝ c z : EReal) ≤ supportFunction C z :=
        cor41_inner_le_supportFunction hc
      have hσz_eq : supportFunction C z = (inner ℝ c z : EReal) :=
        le_antisymm hσz_le hσz_ge
      intro y
      have hy_ge : (inner ℝ c y : EReal) ≤ supportFunction C y :=
        cor41_inner_le_supportFunction hc
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
        cor41_supportFunction_ne_top_of_bounded C hC_bounded x
      have hx_bot : supportFunction C x ≠ ⊥ :=
        cor41_supportFunction_ne_bot_of_nonempty hC_nonempty x
      have hy_top : supportFunction C y ≠ ⊤ :=
        cor41_supportFunction_ne_top_of_bounded C hC_bounded y
      have hy_bot : supportFunction C y ≠ ⊥ :=
        cor41_supportFunction_ne_bot_of_nonempty hC_nonempty y
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
          cor41_inner_le_supportFunction hqC
        have hσp_eq : supportFunction C p = (inner ℝ q p : EReal) :=
          le_antisymm hσp_le hσp_ge
        intro y
        have hy_ge : (inner ℝ q y : EReal) ≤ supportFunction C y :=
          cor41_inner_le_supportFunction hqC
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
    exact cor41_maximal_of_monotone_and_resolvent_surjective S hS_mono hres
  have hF_dom : F.dom = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rw [SetValuedOperator.mem_dom_iff]
      refine ⟨A0 z, ?_⟩
      simp [F, SetValuedOperator.ofFunction_apply_of_mem]
  have hF_max : IsMaximalMonotone F := by
    simpa [F] using hA0_mono
  have hAmax : IsMaximalMonotone A := by
    have hdom : (interior S.dom ∩ F.dom).Nonempty := by
      refine ⟨0, ?_⟩
      simp [hS_dom, hF_dom]
    have hSFmax : IsMaximalMonotone (S + F) :=
      sum_maximal_monotone S F hS_max hF_max hdom
    simpa [S, F] using hA ▸ hSFmax
  have hAdom : A.dom = Set.univ := by
    rw [hA]
    change (S + F).dom = Set.univ
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rw [SetValuedOperator.mem_dom_iff]
      have hzS : z ∈ S.dom := by simpa [hS_dom]
      rcases (SetValuedOperator.mem_dom_iff S z).mp hzS with ⟨s, hs⟩
      refine ⟨s + A0 z, ?_⟩
      change s + A0 z ∈ S z + F z
      rw [Set.mem_add]
      refine ⟨s, hs, A0 z, ?_, rfl⟩
      simp [F, SetValuedOperator.ofFunction_apply_of_mem]
  have hA0set : A (0 : H) = C := by
    rw [hA]
    change (S + F) (0 : H) = C
    ext w
    constructor
    · intro hw
      change w ∈ S (0 : H) + F (0 : H) at hw
      rw [Set.mem_add] at hw
      rcases hw with ⟨s, hs, t, ht, rfl⟩
      have ht : t ∈ ({A0 (0 : H)} : Set H) := by
        simpa [F, SetValuedOperator.ofFunction_apply_of_mem] using ht
      have ht0 : t = 0 := by simpa [hA0_zero] using ht
      simpa [ht0] using (by
        have : s ∈ S (0 : H) := hs
        simpa [hS0] using this)
    · intro hw
      change w ∈ S (0 : H) + F (0 : H)
      rw [Set.mem_add]
      refine ⟨w, ?_, 0, ?_, by simp⟩
      · simpa [hS0] using hw
      · simp [F, SetValuedOperator.ofFunction_apply_of_mem, hA0_zero]
  have hAzero_int : (0 : H) ∈ interior (A (0 : H)) := by
    simpa [hA0set] using hC_int
  have h_linear_growth : ∀ z, ‖z‖ ≤ η → excess (A z) (A (0 : H)) ≤ α * ‖z‖ := by
    intro z hz
    have hexcess_norm : excess (A z) (A (0 : H)) ≤ ‖A0 z‖ := by
      let G : A z → ℝ := fun w => Metric.infDist (w : H) (A (0 : H))
      have hpoint : ∀ w : A z, G w ≤ ‖A0 z‖ := by
        intro w
        have hw : (w : H) ∈ A z := w.property
        have hwSF : (w : H) ∈ S z + F z := by
          have hAz_eq : A z = (S + F) z := by
            simpa [S, F] using congrFun hA z
          simpa [hAz_eq] using hw
        rw [Set.mem_add] at hwSF
        rcases hwSF with ⟨s, hs, t, ht, hst⟩
        have htA0 : t = A0 z := by
          have ht' : t ∈ ({A0 z} : Set H) := by
            simpa [F, SetValuedOperator.ofFunction_apply_of_mem] using ht
          simpa using ht'
        have hsA0 : s ∈ A (0 : H) := by
          simpa [hA0set] using hS_subset z hs
        calc
          G w = Metric.infDist (w : H) (A (0 : H)) := rfl
          _ ≤ dist (w : H) s := Metric.infDist_le_dist_of_mem hsA0
          _ = dist (s + t) s := by rw [hst]
          _ = ‖A0 z‖ := by
            rw [htA0, dist_eq_norm]
            have hsub : s + A0 z - s = A0 z := by abel
            rw [hsub]
      have hAznonempty : (A z).Nonempty := by
        have hzdom : z ∈ A.dom := by simpa [hAdom]
        exact (SetValuedOperator.mem_dom_iff A z).mp hzdom
      rcases hAznonempty with ⟨a, ha⟩
      haveI : Nonempty (A z) := ⟨⟨a, ha⟩⟩
      have hbdd : BddAbove (Set.range G) := by
        refine ⟨‖A0 z‖, ?_⟩
        rintro r ⟨w, rfl⟩
        exact hpoint w
      have hbot : sSup (∅ : Set ℝ) ≤ ⨆ w : A z, G w := by
        simp only [Real.sSup_empty]
        exact le_trans Metric.infDist_nonneg (le_ciSup hbdd ⟨a, ha⟩)
      have hexcess_eq : excess (A z) (A (0 : H)) = ⨆ w : A z, G w := by
        unfold excess
        exact (ciSup_subtype (p := fun w : H => w ∈ A z) (f := G) hbdd hbot).symm
      rw [hexcess_eq]
      exact ciSup_le hpoint
    exact le_trans hexcess_norm (h_A0_growth z hz)
  have hfiniteE : ∀ y, fE y ≠ ⊤ ∧ fE y ≠ ⊥ := by
    intro y
    simp [fE]
  have hf_C11E : IsC11 (fun y => (fE y).toReal) := by
    simpa [fE] using hf_C11
  have hinfE : ∃ m : ℝ, ∀ y, (m : EReal) ≤ fE y := by
    rcases hinf with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro y
    have hreal : m ≤ f y := hm y
    have hE : (m : EReal) ≤ (f y : EReal) := by
      exact_mod_cast hreal
    simpa [fE] using hE
  have hf_strongE : IsStronglyConvex (fun y => (fE y).toReal) M := by
    simpa [fE] using hf_strongConv
  have hBgradE : B =
      SetValuedOperator.ofFunction Set.univ
        (fun x : (Set.univ : Set H) => gradient (fun y => (fE y).toReal) x.1) := by
    simpa [fE] using hB_eq_grad
  have hsmoothE : IsSmoothAt (A (0 : H)) (-gradient (fun y => (fE y).toReal) xInf) := by
    simpa [fE, hA0set] using h_smooth
  have hfinite_of_alpha :
      α ^ 2 < M → ∃ N, ∀ n ≥ N, x n = x N :=
    thm_4_1_finite_of_alpha_sq_lt A B hAmax hAdom hAzero_int η hη α hα
      h_linear_growth fE hfiniteE hf_C11E hinfE M hf_strongE hBgradE lam hlam
      lam_seq hlam_seq x halg xInf hxInf hsmoothE
  by_cases hfinite : ∃ N, ∀ n ≥ N, x n = x N
  · exact ⟨Or.inl hfinite, fun _ => hfinite⟩
  · have hlower :=
      thm_4_1_lower_rate_of_not_finite A B hAmax hAdom hAzero_int η hη α hα
        h_linear_growth fE hfiniteE hf_C11E hinfE M hf_strongE hBgradE lam hlam
        lam_seq hlam_seq x halg xInf hxInf hsmoothE hfinite
    have htail :=
      thm_4_1_tail_rate_of_not_finite A B hAmax hAdom hAzero_int η hη α hα
        h_linear_growth fE hfiniteE hf_C11E hinfE M hf_strongE hBgradE lam hlam
        lam_seq hlam_seq x halg xInf hxInf hsmoothE hfinite
    rcases hlower with ⟨nLower, hLower⟩
    rcases htail with ⟨nTail, hTail⟩
    refine ⟨Or.inr ?_, hfinite_of_alpha⟩
    refine ⟨max nLower nTail, ?_, ?_⟩
    · intro q1 hq1pos hq1lt hq1bound
      rcases hLower q1 hq1pos hq1lt hq1bound with ⟨C1, hC1pos, hC1⟩
      exact ⟨C1, hC1pos, fun n hn => hC1 n (le_trans (Nat.le_max_left _ _) hn)⟩
    · intro q2 hq2pos hq2lt hq2bound
      rcases hTail q2 hq2pos hq2lt hq2bound with ⟨C2, hC2pos, hC2⟩
      exact ⟨C2, hC2pos, fun n hn => hC2 n (le_trans (Nat.le_max_right _ _) hn)⟩
```

## Proof explanation
The proof begins with `classical`, allowing classical logic, and then introduces three abbreviations. First,

$$
S=\partial\sigma_C
$$

is the subderivative of the support function of $C$. Second,

```math
F(x)=\{A0(x)\}
```

is the single-valued operator $A0$ viewed as a set-valued operator. Third,

```math
f_E(x)=(f(x):\mathbb R\cup\{\pm\infty\})
```

is the extended-real-valued version of $f$. The hypothesis `hA` says precisely that $A=S+F$.

The first auxiliary fact is $A0(0)=0$. Since $0\le \eta$, the local growth hypothesis applies at $x=0$ and gives

```math
\|A0(0)\|\le \alpha\|0\|=0.
```

Because norms are nonnegative, $`\|A0(0)\|=0`$, hence$A0(0)=0$.

Next the proof establishes

$$
S(0)=C.
$$

The point $0\in C$ comes from `hC_int`, since an interior point belongs to the set. The cited lemma `cor41_supportFunction_zero` gives

$$
\sigma_C(0)=0
$$

because $0\in C$. For the inclusion $S(0)\subseteq C$, suppose $v\in S(0)$ but $v\notin C$. The separation theorem

```math
\texttt{exists\_nonzero\_innerSupremumOn\_lt\_inner\_of\_nonempty\_isClosed\_convex\_of\_not\_mem}
```

applies to the nonempty closed convex set $C$ and the point $v\notin C$. It provides a nonzero $u$ with

$$
\mathrm{innerSupremumOn}_C(u)<\langle v,u\rangle.
$$

Since $\mathrm{innerSupremumOn}_C(u)=\sigma_C(u)$, this is a strict separation inequality. On the other hand, $v\in S(0)$ means that for every $y$,

$$
\sigma_C(y)\ge \sigma_C(0)+\langle v,y\rangle.
$$

Using $\sigma_C(0)=0$ and taking $y=u$, this gives

$$
\langle v,u\rangle\le \sigma_C(u),
$$

contradicting the strict separation. Thus $S(0)\subseteq C$. For the reverse inclusion, if $v\in C$, then for every $y$ the cited lemma `cor41_inner_le_supportFunction` gives

$$
\langle v,y\rangle\le \sigma_C(y).
$$

Again $\sigma_C(0)=0$, so

$$
\sigma_C(y)\ge \sigma_C(0)+\langle v,y\rangle,
$$

which is exactly the condition $v\in S(0)$. Hence $S(0)=C$.

The proof next shows

$$
S(z)\subseteq C\qquad\text{for every }z.
$$

Take $v\in S(z)$. The subgradient inequality at $z$ gives, for every $y$,

$$
\sigma_C(z)+\langle v,y\rangle
\le \sigma_C(z+y).
$$

The cited lemma `cor41_supportFunction_add_le` gives the subadditivity

$$
\sigma_C(z+y)\le \sigma_C(z)+\sigma_C(y).
$$

The support-function values are finite here: `cor41_supportFunction_ne_top_of_bounded` gives $\sigma_C(y)\neq \top$, and `cor41_supportFunction_ne_bot_of_nonempty` gives $\sigma_C(y)\neq \bot$. Therefore the extended-real inequality can be converted to an ordinary real inequality and $\sigma_C(z)$ can be canceled, yielding

$$
\langle v,y\rangle\le \sigma_C(y).
$$

This says $v\in S(0)$, and since $S(0)=C$, we get $v\in C$. Thus $S(z)\subseteq C$.

The domain of $S$ is then shown to be all of $H$. Since $C$ is closed and bounded in finite dimension, it is compact. For fixed $z$, the continuous function

$$
q\mapsto \langle q,z\rangle
$$

attains a maximum on $C$ at some point $c\in C$. Hence

$$
\sigma_C(z)=\langle c,z\rangle.
$$

For any $y$, the definition of the support function and $c\in C$ give

$$
\sigma_C(y)\ge \langle c,y\rangle
=\langle c,z\rangle+\langle c,y-z\rangle
=\sigma_C(z)+\langle c,y-z\rangle.
$$

Therefore $c\in S(z)$, so every $z$ belongs to the domain of $S$. Thus $S.\mathrm{dom}=H$.

The proof then proves that $S$ is maximal monotone. First it proves monotonicity. If $u\in S(x)$ and $v\in S(y)$, the subgradient inequalities are

$$
\sigma_C(y)\ge \sigma_C(x)+\langle u,y-x\rangle,
$$

$$
\sigma_C(x)\ge \sigma_C(y)+\langle v,x-y\rangle.
$$

After converting to real inequalities and canceling the finite support-function values, adding these gives

$$
\langle u,y-x\rangle+\langle v,x-y\rangle\le 0.
$$

Since $y-x=-(x-y)$, this is

$$
\langle v-u,x-y\rangle\le 0,
$$

equivalently

$$
0\le \langle u-v,x-y\rangle.
$$

So $S$ is monotone.

Second, the proof establishes the resolvent-surjectivity condition

$$
\forall z,\ \exists p,q,\quad q\in S(p)\ \land\ z=p+q.
$$

For a given $z$, let

$$
q=\mathrm{proj}_C(z)
$$

be the projection of $z$ onto $C$. The existence and uniqueness of this projection come from `isChebyshev_of_nonempty_isClosed_convex`, applied to the nonempty closed convex set $C$. The projection characterization

$$
q\in C\quad\text{and}\quad
\forall r\in C,\ \langle r-q,z-q\rangle\le 0
$$

comes from

```math
\texttt{eq\_projectionPoint\_iff\_mem\_and\_inner\_sub\_right\_nonpos\_of\_nonempty\_isClosed\_convex}.
```

Set $p=z-q$. The projection inequality says

$$
\langle r-q,p\rangle\le 0
$$

for every $r\in C$, hence

$$
\langle r,p\rangle\le \langle q,p\rangle.
$$

Thus $q$ maximizes the linear functional $r\mapsto \langle r,p\rangle$ over $C$, so

$$
\sigma_C(p)=\langle q,p\rangle.
$$

For any $y$, `cor41_inner_le_supportFunction` gives

$$
\langle q,y\rangle\le \sigma_C(y).
$$

But

$$
\langle q,y\rangle
=\langle q,p\rangle+\langle q,y-p\rangle
=\sigma_C(p)+\langle q,y-p\rangle.
$$

Therefore

$$
\sigma_C(y)\ge \sigma_C(p)+\langle q,y-p\rangle,
$$

which is precisely $q\in S(p)$. Since $z=p+q$, the resolvent-surjectivity condition holds. The cited theorem

```math
\texttt{cor41\_maximal\_of\_monotone\_and\_resolvent\_surjective}
```

says that a monotone operator $B$ for which every $z$ can be written as $z=p+q$ with $q\in B(p)$ is maximal monotone. Hence $S$ is maximal monotone.

The operator $F$ has domain all of $H$, because $`F(x)=\{A0(x)\}`$is nonempty for every$x$. Its maximal monotonicity is exactly the hypothesis `hA0_mono`.

Now the proof shows that $A$ is maximal monotone. Since $A=S+F$, the cited theorem

```math
\texttt{sum\_maximal\_monotone}
```

applies to $S$ and $F$. Its hypotheses are that both operators are maximal monotone and that

$$
\mathrm{int}(\mathrm{dom}S)\cap \mathrm{dom}F\neq\emptyset.
$$

Here both domains are all of $H$, so this intersection is nonempty. Therefore $S+F$ is maximal monotone, and by `hA`, so is $A$.

The proof also records that $A.\mathrm{dom}=H$, that

```math
A(0)=S(0)+F(0)=C+\{0\}=C,
```

and that therefore

$$
0\in \mathrm{interior}(A(0)).
$$

The equality $A(0)=C$ uses $S(0)=C$ and $A0(0)=0$.

Next the proof verifies the linear-growth condition needed by the main theorems. For $`\|z\|\le\eta`$, it proves

```math
\mathrm{excess}(A(z),A(0))\le \alpha\|z\|.
```

If $w\in A(z)$, then $w=s+A0(z)$ with $s\in S(z)$. Since $S(z)\subseteq C=A(0)$, the distance from $w$ to $A(0)$ is at most the distance from $w$ to $s$, and

```math
\mathrm{dist}(w,s)=\|A0(z)\|.
```

Thus

```math
\mathrm{infDist}(w,A(0))\le \|A0(z)\|.
```

Taking the supremum over all $w\in A(z)$, and using the definition

$$
\mathrm{excess}(A(z),A(0))
=\sup_{w\in A(z)}\mathrm{infDist}(w,A(0)),
$$

gives

```math
\mathrm{excess}(A(z),A(0))\le \|A0(z)\|.
```

The local growth hypothesis `h_A0_growth` then gives $`\|A0(z)\|\le\alpha\|z\|`$, so the required excess bound follows.

The proof then passes from the real-valued $f$ to the extended-real-valued $f_E$. Since $f$ takes values in $\mathbb R$, the values of $f_E$ are finite, never $\top$ or $\bot$. The hypotheses `hf_C11`, `hinf`, `hf_strongConv`, and `hB_eq_grad` are transferred unchanged to $f_E$ and its real-valued version $(f_E).\mathrm{toReal}$. The smoothness hypothesis is also transferred: since $A(0)=C$, the statement `IsSmoothAt C (-gradient f xInf)` becomes

$$
\mathrm{IsSmoothAt}(A(0),-\nabla f_E(x_\infty)).
$$

These transfers are needed because the cited Baji-Cabot theorems are stated for extended-real functions.

The finite-convergence theorem `thm_4_1_finite_of_alpha_sq_lt` is then applied to $A,B,f_E$ and the sequence $x$. It says that under exactly the assembled hypotheses, if

$$
\alpha^2<M,
$$

then there exists $N$ such that for every $n\ge N$,

$$
x_n=x_N.
$$

This gives the implication `hfinite_of_alpha`.

The proof now splits by cases on whether the sequence is eventually constant.

If

$$
\exists N,\ \forall n\ge N,\ x_n=x_N,
$$

then the first conjunct of the conclusion is immediate, using the left disjunct. The second conjunct is also satisfied by the same eventual constancy, because $\alpha^2\lt M$ implies it trivially once eventual constancy is already known.

If the sequence is not eventually constant, the proof applies two more cited theorems:

```math
\texttt{thm\_4\_1\_lower\_rate\_of\_not\_finite}
```

and

```math
\texttt{thm\_4\_1\_tail\_rate\_of\_not\_finite}.
```

The first gives an $n_{\text{lower}}$ such that for every $q_1$ with $0\lt q_1\lt 1$ and

$$
q_1<\frac{1}{\alpha\lambda+1},
$$

there exists $C_1\gt 0$ such that for all $n\ge n_{\text{lower}}$,

```math
\|x_n-x_\infty\|\ge C_1 q_1^n.
```

The second gives an $n_{\text{tail}}$ such that for every $q_2$ with $0\lt q_2\lt 1$ and

$$
q_2>\frac{\alpha}{\alpha+M\lambda},
$$

there exists $C_2\gt 0$ such that for all $n\ge n_{\text{tail}}$,

```math
\sum_{k\ge 0}\|x_{n+k}-x_\infty\|\le C_2 q_2^n.
```

The proof sets

$$
n_0=\max(n_{\text{lower}},n_{\text{tail}}).
$$

Then any index $n\ge n_0$ also satisfies $n\ge n_{\text{lower}}$, so the lower estimate from the first theorem applies, and similarly $n\ge n_{\text{tail}}$, so the tail estimate from the second theorem applies. Thus the right-hand disjunct is established with this common $n_0$. Combining this with the previously proved implication `hfinite_of_alpha` gives the full conclusion.

The Lean commands reflect these steps. `intro` introduces hypotheses and variables; `let` creates local abbreviations; `have` records intermediate mathematical facts; `ext` proves set equalities by extensionality; `constructor` splits conjunctions and iff-statements; `by_contra` proves the missing inclusion $S(0)\subseteq C$ by contradiction using the separation theorem; `rcases` destructs existential and conjunctive hypotheses; `refine` supplies witnesses such as the projection point or the common $n_0=\max(n_{\text{lower}},n_{\text{tail}})$; `rw`, `simp`, `simpa`, and `unfold` rewrite definitions and cited lemmas; `change` replaces a goal by its definitional unfolding; `linarith` and `nlinarith` close the real and nonlinear numeric inequalities obtained after canceling finite extended-real terms; and `by_cases` performs the case split on eventual constancy. The extended-real lemmas such as `EReal.toReal_add`, `EReal.toReal_le_toReal`, and the finiteness lemmas for support functions are used only to justify that the relevant support-function inequalities are finite and may be treated as ordinary real inequalities.

