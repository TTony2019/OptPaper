## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/prop_2.lean`

## Lean statement
```lean
theorem prop_2_2 (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hdomA : A.dom = Set.univ)
    (hAzero : (0 : H) ∈ A (0 : H)) (f : H → EReal)
    (hf_conv : ∀ x y : H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y)
    (hf_lsc : LowerSemicontinuous f)
    (hB_eq_subderiv : ∀ x, B x = {v | ∀ y, f y ≥ f x + (inner ℝ v (y - x) : EReal)})
    (hdom_subderiv : (SetValuedOperator.dom B).Nonempty) (hinf : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f x)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, lam n > 0) (hlam_nondec : ∀ n, lam n ≤ lam (n+1))
    (x : ℕ → H) (halg : AlgorithmA A B x lam)
    (hx1_dom : x 1 ∈ ERealFunction.dom f) :
    (∀ n, energySeq x lam f (n+1) - energySeq x lam f n ≤
      (-(lam n) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1))) : EReal)) ∧
    (∃ (S : ℝ), Tendsto (fun (N : ℕ) => (Finset.range (N+1)).sum (fun n => (lam n) *
      PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1))))) atTop (𝓝 S))
```

## Statement explanation
This theorem is stated for a real inner-product space $H$ (in the surrounding file this is treated as a Hilbert-space setting) and two set-valued operators $A,B:H\rightrightarrows H$. The notation $\overline{\mathbb R}$ denotes the extended real line. The theorem also involves an extended-real function $f:H\to\overline{\mathbb R}$, a sequence of positive step sizes $\lambda:\mathbb N\to\mathbb R$, and a sequence $x:\mathbb N\to H$.

The hypotheses are as follows.

- $A$ is maximal monotone. The proof uses only the monotonicity part of this hypothesis: if $u\in A x$ and $v\in A y$, then

$$
0\le \langle u-v,x-y\rangle .
$$

- The domain of $A$ is all of $H$: $\mathrm{dom}A=H$, where $z\in\mathrm{dom}A$ means $A z\ne\varnothing$.
- $0\in A(0)$.
- $f$ is convex in the extended-real sense: for all $x,y\in H$ and all real $a,b\ge0$ with $a+b=1$,

$$
f(a x+b y)\le a f(x)+b f(y),
$$

with the right-hand side interpreted in $\overline{\mathbb R}$.
- $f$ is lower semicontinuous.
- $B$ is the subdifferential of $f$ in the sense that for every $x$,

```math
B x=\{v:\forall y,\ f(y)\ge f(x)+\langle v,y-x\rangle\}.
```

- The domain of $B$ is nonempty. This assumption appears in the statement but is not explicitly used in the displayed proof.
- $f$ is bounded below by a real number: there is $m\in\mathbb R$ such that $(m:\overline{\mathbb R})\le f(x)$ for all $x\in H$.
- $\lambda_n\gt 0$ for every $n$, and $\lambda_n\le \lambda_{n+1}$.
- $x$ satisfies the algorithm relation `AlgorithmA A B x lam`. The only consequence of this relation used in the proof is that, for each $n$, if

$$
d_2=x_{n+2}-x_{n+1},\qquad
v=\lambda_n^{-1}d_2,\qquad
\mathrm{acc}=\lambda_n^{-2}(x_{n+2}-2x_{n+1}+x_n),
$$

then

```math
0\in \{\mathrm{acc}\}+A v+B(x_{n+2}).
```

- $x_1\in \mathrm{dom}f$, meaning $f(x_1)\lt \top$, where $\top=+\infty$ in $\overline{\mathbb R}$.

The energy sequence is defined by

```math
E_n=\frac{1}{2\lambda_n^2}\|x_{n+1}-x_n\|^2+f(x_{n+1}),
```

with values in $\overline{\mathbb R}$. The set-valued quantity $\Phi_A$ is defined by

$$
\Phi_A(z)=\inf_{y\in A z}\langle y,z\rangle,
$$

where the infimum is taken in $\overline{\mathbb R}$ and the real inner product is coerced to $\overline{\mathbb R}$.

The theorem concludes two things. First, for every $n$,

```math
E_{n+1}-E_n
\le
-\lambda_n\,\Phi_A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right).
```

Thus the energy decreases at least by the friction term. Second, there exists a real number $S$ such that

```math
\sum_{n=0}^{N}
\lambda_n\,\Phi_A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right)
\longrightarrow S
```

as $N\to\infty$, in $\overline{\mathbb R}$. Equivalently, the friction terms

```math
\lambda_n\,\Phi_A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right)
```

form a summable series.

## Lean proof
```lean
by
  classical
  have hmono : IsMonotone A := hA.1
  rcases hinf with ⟨m, hm⟩
  let energyR : ℕ → ℝ := fun n =>
    ((2 * (lam n)^2)⁻¹) * ‖x (n+1) - x n‖^2 + (f (x (n+1))).toReal
  have hf_iter_ne_bot : ∀ n, f (x n) ≠ ⊥ := by
    intro n hbot
    have hle := hm (x n)
    rw [hbot] at hle
    simp at hle
  have hx1_ne_top : f (x 1) ≠ ⊤ := by
    have hx1_lt : f (x 1) < ⊤ := by
      simpa [ERealFunction.dom] using hx1_dom
    exact ne_of_lt hx1_lt
  have hf_iter_ne_top : ∀ n, f (x (n+1)) ≠ ⊤ := by
    intro n
    cases n with
    | zero =>
        simpa using hx1_ne_top
    | succ k =>
        let d₂ : H := x (k+2) - x (k+1)
        let v : H := (lam k)⁻¹ • d₂
        let acc : H := ((lam k)^2)⁻¹ • (x (k+2) - 2 • x (k+1) + x k)
        have hstep : (0 : H) ∈ ({acc} : Set H) + A v + B (x (k+2)) := by
          simpa [AlgorithmA, acc, v, d₂] using halg.step k
        rw [Set.mem_add] at hstep
        rcases hstep with ⟨p, hp, b, hb, hpbeq⟩
        have hbsub : ∀ t : H, f t ≥ f (x (k+2)) + inner ℝ b (t - x (k+2)) := by
          have hb' :
              b ∈ {v | ∀ t : H, f t ≥ f (x (k+2)) + inner ℝ v (t - x (k+2))} := by
            simpa [hB_eq_subderiv] using hb
          simpa using hb'
        intro hx_top
        have h := hbsub (x 1)
        have htop_le : (⊤ : EReal) ≤ f (x 1) := by
          simpa [hx_top] using h
        exact hx1_ne_top (top_le_iff.mp htop_le)
  have henergySeq_eq : ∀ n, energySeq x lam f n = (energyR n : EReal) := by
    intro n
    dsimp [energySeq, energyR]
    rw [← EReal.coe_toReal (hf_iter_ne_top n) (hf_iter_ne_bot (n+1))]
    simp
  have hPhi_nonneg :
      ∀ z : H, 0 ≤ PhiA A z := by
    intro z
    have hAz : (A z).Nonempty := by
      have hzdom : z ∈ A.dom := by simp [hdomA]
      simpa [SetValuedOperator.mem_dom_iff] using hzdom
    rw [PhiA]
    apply le_sInf
    rintro _ ⟨y, hy, rfl⟩
    have h := hmono y hy (0 : H) hAzero
    have hreal : 0 ≤ inner ℝ y z := by
      simpa using h
    exact (EReal.coe_nonneg).2 hreal
  have hPhi_ne_bot : ∀ z : H, PhiA A z ≠ ⊥ := by
    intro z hbot
    have hnonneg := hPhi_nonneg z
    rw [hbot] at hnonneg
    simp at hnonneg
  have hPhi_ne_top : ∀ z : H, PhiA A z ≠ ⊤ := by
    intro z htop
    have hAz : (A z).Nonempty := by
      have hzdom : z ∈ A.dom := by simp [hdomA]
      simpa [SetValuedOperator.mem_dom_iff] using hzdom
    rcases hAz with ⟨y, hy⟩
    have hle : PhiA A z ≤ (inner ℝ y z : EReal) := by
      rw [PhiA]
      exact sInf_le ⟨y, hy, rfl⟩
    rw [htop] at hle
    exact EReal.coe_ne_top _ (top_le_iff.mp hle)
  let termE : ℕ → EReal := fun n =>
    (lam n : EReal) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1)))
  have hmainR :
      ∀ n, ((energyR (n+1) - energyR n : ℝ) : EReal) ≤ -termE n ∧
        (termE n).toReal ≤ energyR n - energyR (n+1) := by
    intro n
    let d₁ : H := x (n+1) - x n
    let d₂ : H := x (n+2) - x (n+1)
    let v : H := (lam n)⁻¹ • d₂
    let acc : H := ((lam n)^2)⁻¹ • (x (n+2) - 2 • x (n+1) + x n)
    have hstep : (0 : H) ∈ ({acc} : Set H) + A v + B (x (n+2)) := by
      simpa [AlgorithmA, acc, v, d₂] using halg.step n
    rw [Set.mem_add] at hstep
    rcases hstep with ⟨p, hp, b, hb, hpbeq⟩
    rw [Set.mem_add] at hp
    rcases hp with ⟨a, ha, y, hyA, hp_eq⟩
    rw [Set.mem_singleton_iff] at ha
    subst a
    have hsum_zero : acc + y + b = 0 := by simpa [hp_eq] using hpbeq
    have hbsub : ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ b (t - x (n+2)) := by
      have hb' : b ∈ {v | ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ v (t - x (n+2))} := by
        simpa [hB_eq_subderiv] using hb
      simpa using hb'
    have hf_diff :
        (f (x (n+2))).toReal - (f (x (n+1))).toReal ≤ inner ℝ b d₂ := by
      have h := hbsub (x (n+1))
      have hinner : inner ℝ b (x (n+1) - x (n+2)) = - inner ℝ b d₂ := by
        rw [show x (n+1) - x (n+2) = -(x (n+2) - x (n+1)) by abel]
        rw [inner_neg_right]
      have hx2_top : f (x (n+2)) ≠ ⊤ := hf_iter_ne_top (n+1)
      have hx1_top : f (x (n+1)) ≠ ⊤ := hf_iter_ne_top n
      have hx2_bot : f (x (n+2)) ≠ ⊥ := by
        intro hbot
        have hle := hm (x (n+2))
        rw [hbot] at hle
        simp at hle
      have h_add_bot : f (x (n+2)) + (inner ℝ b (x (n+1) - x (n+2)) : EReal) ≠ ⊥ := by
        rw [← EReal.coe_toReal hx2_top hx2_bot]
        simp
      have hle_real := EReal.toReal_le_toReal h h_add_bot hx1_top
      have hadd_toReal :
          (f (x (n+2)) + (inner ℝ b (x (n+1) - x (n+2)) : EReal)).toReal =
            (f (x (n+2))).toReal + inner ℝ b (x (n+1) - x (n+2)) := by
        exact EReal.toReal_add hx2_top hx2_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      have hle_real' :
          (f (x (n+2))).toReal + inner ℝ b (x (n+1) - x (n+2)) ≤
            (f (x (n+1))).toReal := by
        simpa [hadd_toReal] using hle_real
      linarith
    have hcoeff :
        (2 * (lam (n+1))^2)⁻¹ * ‖d₂‖^2 ≤
          (2 * (lam n)^2)⁻¹ * ‖d₂‖^2 := by
      have hln : 0 < lam n := hlam_pos n
      have hln1 : 0 < lam (n+1) := lt_of_lt_of_le hln (hlam_nondec n)
      have habs : |lam n| ≤ |lam (n+1)| := by
        simpa [abs_of_pos hln, abs_of_pos hln1] using hlam_nondec n
      have hden : 2 * (lam n)^2 ≤ 2 * (lam (n+1))^2 := by
        nlinarith [sq_le_sq.mpr habs]
      have hdenpos : 0 < 2 * (lam n)^2 := by positivity
      have hinv : (2 * (lam (n+1))^2)⁻¹ ≤ (2 * (lam n)^2)⁻¹ := by
        exact inv_anti₀ hdenpos hden
      exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    have henergy_le :
        energyR (n+1) - energyR n ≤
          (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := by
      dsimp [energyR, d₁, d₂]
      linarith
    have hnorm :
        ‖d₂‖^2 - ‖d₁‖^2 ≤ 2 * inner ℝ (d₂ - d₁) d₂ := by
      have hnon : 0 ≤ ‖d₂ - d₁‖^2 := sq_nonneg _
      rw [norm_sub_sq_real] at hnon
      rw [real_inner_comm d₁ d₂] at hnon
      rw [inner_sub_left]
      rw [real_inner_self_eq_norm_sq]
      nlinarith [hnon]
    have hnorm_scaled :
        (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) ≤
          ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
      have hscale_nonneg : 0 ≤ (2 * (lam n)^2)⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_left hnorm hscale_nonneg
      have hscale_eq :
          (2 * (lam n)^2)⁻¹ * (2 * inner ℝ (d₂ - d₁) d₂) =
            ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
        field_simp [ne_of_gt (hlam_pos n)]
      calc
        (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2)
            ≤ (2 * (lam n)^2)⁻¹ * (2 * inner ℝ (d₂ - d₁) d₂) := hmul
        _ = ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := hscale_eq
    have hacc_eq : acc = ((lam n)^2)⁻¹ • (d₂ - d₁) := by
      dsimp [acc, d₁, d₂]
      congr 1
      abel
    have hacc_inner :
        inner ℝ acc d₂ = ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
      rw [hacc_eq, inner_smul_left]
      rfl
    have henergy_acc :
        energyR (n+1) - energyR n ≤ inner ℝ (acc + b) d₂ := by
      calc
        energyR (n+1) - energyR n
            ≤ (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := henergy_le
        _ ≤ ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ + inner ℝ b d₂ :=
            by linarith
        _ = inner ℝ (acc + b) d₂ := by
            rw [← hacc_inner, inner_add_left]
    have haccb : acc + b = -y := by
      calc
        acc + b = (acc + y + b) - y := by abel
        _ = 0 - y := by rw [hsum_zero]
        _ = -y := by simp
    have henergy_y :
        energyR (n+1) - energyR n ≤ - inner ℝ y d₂ := by
      calc
        energyR (n+1) - energyR n ≤ inner ℝ (acc + b) d₂ := henergy_acc
        _ = inner ℝ (-y) d₂ := by rw [haccb]
        _ = - inner ℝ y d₂ := by rw [inner_neg_left]
    have hd₂_eq : d₂ = (lam n) • v := by
      dsimp [v]
      rw [smul_smul]
      field_simp [ne_of_gt (hlam_pos n)]
      simp
    have hinner_d₂ : inner ℝ y d₂ = (lam n) * inner ℝ y v := by
      rw [hd₂_eq, inner_smul_right]
    have hPhi_le_y : PhiA A v ≤ (inner ℝ y v : EReal) := by
      rw [PhiA]
      exact sInf_le ⟨y, hyA, rfl⟩
    have hPhi_toReal_le : (PhiA A v).toReal ≤ inner ℝ y v := by
      have h := EReal.toReal_le_toReal hPhi_le_y (hPhi_ne_bot v) (EReal.coe_ne_top _)
      simpa using h
    have hmainRreal :
        energyR (n+1) - energyR n ≤ -(lam n) * (PhiA A v).toReal := by
      calc
        energyR (n+1) - energyR n ≤ - inner ℝ y d₂ := henergy_y
        _ = -(lam n) * inner ℝ y v := by
            rw [hinner_d₂]
            ring
        _ ≤ -(lam n) * (PhiA A v).toReal := by
            have hnonneg : 0 ≤ lam n := le_of_lt (hlam_pos n)
            nlinarith
    have hPhi_coe : (((PhiA A v).toReal : ℝ) : EReal) = PhiA A v :=
      EReal.coe_toReal (hPhi_ne_top v) (hPhi_ne_bot v)
    have hmainE :
        ((energyR (n+1) - energyR n : ℝ) : EReal) ≤
          ((-(lam n) * (PhiA A v).toReal : ℝ) : EReal) :=
      EReal.coe_le_coe hmainRreal
    have hterm_bound : (termE n).toReal ≤ energyR n - energyR (n+1) := by
      have hterm_toReal :
          (termE n).toReal = lam n * (PhiA A v).toReal := by
        simp [termE, v, d₂, EReal.toReal_mul]
      rw [hterm_toReal]
      linarith
    constructor
    · simpa [termE, v, hPhi_coe] using hmainE
    · exact hterm_bound
  have hmain :
      ∀ n, energySeq x lam f (n+1) - energySeq x lam f n ≤
        (-(lam n) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1))) : EReal) := by
    intro n
    rw [henergySeq_eq (n+1), henergySeq_eq n]
    simpa [termE, sub_eq_add_neg] using (hmainR n).1
  refine ⟨hmain, ?_⟩
  let termR : ℕ → ℝ := fun n => (termE n).toReal
  have hterm_nonnegE : ∀ n, 0 ≤ termE n := by
    intro n
    dsimp [termE]
    exact mul_nonneg ((EReal.coe_nonneg).2 (le_of_lt (hlam_pos n))) (hPhi_nonneg _)
  have hterm_ne_bot : ∀ n, termE n ≠ ⊥ := by
    intro n hbot
    have hnonneg := hterm_nonnegE n
    rw [hbot] at hnonneg
    simp at hnonneg
  have hterm_ne_top : ∀ n, termE n ≠ ⊤ := by
    intro n htop
    let v : H := (lam n)⁻¹ • (x (n+2) - x (n+1))
    have hPhi_coe : (((PhiA A v).toReal : ℝ) : EReal) = PhiA A v :=
      EReal.coe_toReal (hPhi_ne_top v) (hPhi_ne_bot v)
    have hterm_coe' :
        termE n = ((lam n * (PhiA A v).toReal : ℝ) : EReal) := by
      simp [termE, v, hPhi_coe]
    rw [hterm_coe'] at htop
    exact EReal.coe_ne_top _ htop
  have hterm_coe : ∀ n, ((termR n : ℝ) : EReal) = termE n := by
    intro n
    exact EReal.coe_toReal (hterm_ne_top n) (hterm_ne_bot n)
  have hterm_nonneg : ∀ n, 0 ≤ termR n := by
    intro n
    have h := EReal.toReal_le_toReal (hterm_nonnegE n) (by simp) (hterm_ne_top n)
    simpa [termR, termE] using h
  have hterm_le_energy :
      ∀ n, termR n ≤ energyR n - energyR (n+1) := by
    intro n
    exact (hmainR n).2
  have henergy_lower : ∀ N, m ≤ energyR N := by
    intro N
    have hf_lower : m ≤ (f (x (N+1))).toReal := by
      have h := EReal.toReal_le_toReal (hm (x (N+1))) (EReal.coe_ne_bot m)
        (hf_iter_ne_top N)
      simpa using h
    have hcoeff_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ := by positivity
    have hnorm_nonneg : 0 ≤ ‖x (N+1) - x N‖^2 := sq_nonneg _
    have hprod_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ * ‖x (N+1) - x N‖^2 :=
      mul_nonneg hcoeff_nonneg hnorm_nonneg
    dsimp [energyR]
    nlinarith
  have hsum_bound :
      ∀ N, (Finset.range N).sum termR ≤
        energyR 0 - m := by
    intro N
    have hsum_le_energy :
        (Finset.range N).sum termR ≤
          (Finset.range N).sum (fun n => energyR n - energyR (n+1)) := by
      exact Finset.sum_le_sum (fun n _ => hterm_le_energy n)
    have htel :
        (Finset.range N).sum (fun n => energyR n - energyR (n+1)) =
          energyR 0 - energyR N := by
      exact Finset.sum_range_sub' energyR N
    calc
      (Finset.range N).sum termR
          ≤ (Finset.range N).sum (fun n => energyR n - energyR (n+1)) :=
            hsum_le_energy
      _ = energyR 0 - energyR N := htel
      _ ≤ energyR 0 - m := by
        linarith [henergy_lower N]
  have hsummable : Summable termR := summable_of_sum_range_le hterm_nonneg hsum_bound
  refine ⟨∑' n, termR n, ?_⟩
  have ht := hsummable.hasSum.tendsto_sum_nat
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id
  have htR :
      Tendsto (fun N : ℕ => (Finset.range (N+1)).sum termR) atTop
        (𝓝 (∑' n, termR n)) :=
    ht.comp hshift
  have htE :
      Tendsto (fun N : ℕ => (((Finset.range (N+1)).sum termR : ℝ) : EReal)) atTop
        (𝓝 (((∑' n, termR n : ℝ) : ℝ) : EReal)) :=
    (EReal.tendsto_coe).2 htR
  have hsum_coe :
      ∀ N : ℕ,
        (((Finset.range (N+1)).sum termR : ℝ) : EReal) =
          (Finset.range (N+1)).sum (fun n =>
            (lam n : EReal) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1)))) := by
    intro N
    calc
      (((Finset.range (N+1)).sum termR : ℝ) : EReal)
          = (Finset.range (N+1)).sum (fun n => ((termR n : ℝ) : EReal)) := by
              have hcoe_sum_finset :
                  ∀ s : Finset ℕ,
                    (((s.sum termR : ℝ) : EReal) =
                      s.sum (fun n => ((termR n : ℝ) : EReal))) := by
                intro s
                refine Finset.induction_on s ?_ ?_
                · simp
                · intro a s ha ih
                  simp [Finset.sum_insert, ha, ih]
              exact hcoe_sum_finset (Finset.range (N+1))
      _ = (Finset.range (N+1)).sum (fun n =>
            (lam n : EReal) * PhiA A ((lam n)⁻¹ • (x (n+2) - x (n+1)))) := by
              exact Finset.sum_congr rfl (fun n _ => by
                simpa [termE] using hterm_coe n)
  convert htE using 1
  · ext N
    exact (hsum_coe N).symm
```

## Proof explanation
The proof begins with `classical`, which allows classical reasoning but does not change the mathematical content. It then extracts the monotonicity of $A$ from the maximal-monotonicity hypothesis by writing `have hmono : IsMonotone A := hA.1`. The declaration `IsMonotone` says precisely that for all $u\in A x$ and $v\in A y$,

$$
0\le \langle u-v,x-y\rangle .
$$

The proof also removes the existential lower bound from `hinf` via `rcases hinf with ⟨m, hm⟩`, so $m\in\mathbb R$ satisfies $(m:\overline{\mathbb R})\le f(x)$ for all $x$.

The first technical goal is to replace the extended-real energy by a real energy. The proof defines

```math
R_n=\frac{1}{2\lambda_n^2}\|x_{n+1}-x_n\|^2+(f(x_{n+1}))_{\mathbb R},
```

where $a_{\mathbb R}$ denotes the real part `toReal` of an extended real $a$. This is useful only if the extended-real values involved are finite.

It first proves that no $f(x_n)$ is $-\infty$. If $f(x_n)=\bot$, then the lower bound $(m:\overline{\mathbb R})\le f(x_n)$ would give $(m:\overline{\mathbb R})\le\bot$, which is impossible for a real $m$. This is the argument behind `hf_iter_ne_bot`.

Next it proves $f(x_1)\ne\top$. The hypothesis $x_1\in\mathrm{dom}f$ means $f(x_1)\lt \top$, using the definition of `ERealFunction.dom`. Hence $f(x_1)$ is not $+\infty$. This is `hx1_ne_top`.

Then it proves by induction that $f(x_{n+1})\ne\top$ for all $n$. The base case is $f(x_1)\ne\top$. For the step, suppose the claim is known up to a certain point and consider the algorithm relation at index $k$. The proof sets

$$
d_2=x_{k+2}-x_{k+1},\qquad
v=\lambda_k^{-1}d_2,\qquad
\mathrm{acc}=\lambda_k^{-2}(x_{k+2}-2x_{k+1}+x_k).
$$

The visible consequence of `halg.step k` is

```math
0\in \{\mathrm{acc}\}+A v+B(x_{k+2}).
```

Decomposing this membership gives in particular an element $b\in B(x_{k+2})$. Since $B$ is the subdifferential of $f$, the defining property of $B(x_{k+2})$ gives, for every $t\in H$,

$$
f(t)\ge f(x_{k+2})+\langle b,t-x_{k+2}\rangle .
$$

If $f(x_{k+2})=\top$, then taking $t=x_1$ gives

$$
f(x_1)\ge \top,
$$

because adding a finite real number to $\top$ still gives $\top$. Hence $f(x_1)=\top$, contradicting $f(x_1)\ne\top$. Thus $f(x_{k+2})\ne\top$. This completes the induction `hf_iter_ne_top`.

With all relevant values of $f$ known to be neither $\top$ nor $\bot$, the proof establishes

$$
E_n=(R_n:\overline{\mathbb R})
$$

for every $n$. This is `henergySeq_eq`. It uses the fact that for a finite extended real $a$, coercing its real part back to $\overline{\mathbb R}$ recovers $a$, i.e.

$$
((a)_{\mathbb R}:\overline{\mathbb R})=a.
$$

This is the role of `EReal.coe_toReal`.

Next the proof studies $\Phi_A$. First it proves $\Phi_A(z)\ge0$ for every $z$. Since $\mathrm{dom}A=H$, every $z$ lies in the domain of $A$, so by the definition of the domain of a set-valued operator, $A z\ne\varnothing$. Choose $y\in A z$. Monotonicity applied to $y\in A z$ and $0\in A(0)$ gives

$$
0\le \langle y-0,z-0\rangle=\langle y,z\rangle.
$$

Thus every element $\langle y,z\rangle$ appearing in the defining set for $\Phi_A(z)$ is nonnegative. Since $\Phi_A(z)$ is the infimum of that set, $\Phi_A(z)\ge0$. This is `hPhi_nonneg`. It also implies $\Phi_A(z)\ne\bot$, because $0\le\bot$ is impossible in $\overline{\mathbb R}$.

Then the proof shows $\Phi_A(z)\ne\top$. Again choose $y\in A z$. By the definition of an infimum, $\Phi_A(z)\le\langle y,z\rangle$. If $\Phi_A(z)=\top$, then $\top\le\langle y,z\rangle$, forcing $\langle y,z\rangle=\top$, impossible because $\langle y,z\rangle$ is a real number coerced to $\overline{\mathbb R}$. Hence $\Phi_A(z)$ is finite and nonnegative for every $z$.

The core energy estimate is now proved. For fixed $n$, define

$$
d_1=x_{n+1}-x_n,\qquad
d_2=x_{n+2}-x_{n+1},\qquad
v=\lambda_n^{-1}d_2,
$$

and

$$
\mathrm{acc}=\lambda_n^{-2}(x_{n+2}-2x_{n+1}+x_n).
$$

The algorithm step gives

```math
0\in \{\mathrm{acc}\}+A v+B(x_{n+2}).
```

Using `Set.mem_add` twice decomposes this as

$$
a+y+b=0
$$

with $a=\mathrm{acc}$, $y\in A v$, and $b\in B(x_{n+2})$. In particular,

$$
\mathrm{acc}+y+b=0,
$$

so

$$
\mathrm{acc}+b=-y.
$$

Because $b\in B(x_{n+2})$, the subdifferential inequality gives for every $t$,

$$
f(t)\ge f(x_{n+2})+\langle b,t-x_{n+2}\rangle.
$$

Taking $t=x_{n+1}$ and using $x_{n+1}-x_{n+2}=-d_2$, this becomes

$$
f(x_{n+1})\ge f(x_{n+2})-\langle b,d_2\rangle.
$$

Converting the finite extended-real inequality to real parts yields

$$
(f(x_{n+2}))_{\mathbb R}-(f(x_{n+1}))_{\mathbb R}\le \langle b,d_2\rangle.
$$

This is `hf_diff`.

Next, the proof compares the coefficients in the two energy terms. Since $0\lt \lambda_n\le\lambda_{n+1}$, we have

$$
(2\lambda_{n+1}^2)^{-1}\le (2\lambda_n^2)^{-1},
$$

so multiplying by $`\|d_2\|^2\ge0`$ gives

```math
(2\lambda_{n+1}^2)^{-1}\|d_2\|^2
\le
(2\lambda_n^2)^{-1}\|d_2\|^2.
```

This is `hcoeff`.

Combining this coefficient comparison with the inequality for the $f$-values gives

```math
R_{n+1}-R_n
\le
(2\lambda_n^2)^{-1}\bigl(\|d_2\|^2-\|d_1\|^2\bigr)
+\langle b,d_2\rangle.
```

This is `henergy_le`.

The proof then uses the elementary Hilbert-space inequality

```math
\|d_2\|^2-\|d_1\|^2
\le
2\langle d_2-d_1,d_2\rangle.
```

It follows from

```math
0\le \|d_2-d_1\|^2
=\|d_2\|^2-2\langle d_2,d_1\rangle+\|d_1\|^2
```

and the symmetry of the real inner product. This is `hnorm`. Multiplying by the nonnegative number $(2\lambda_n^2)^{-1}$ gives

```math
(2\lambda_n^2)^{-1}\bigl(\|d_2\|^2-\|d_1\|^2\bigr)
\le
\lambda_n^{-2}\langle d_2-d_1,d_2\rangle.
```

This is `hnorm_scaled`.

Since

$$
\mathrm{acc}=\lambda_n^{-2}(d_2-d_1),
$$

we have

$$
\langle \mathrm{acc},d_2\rangle
=\lambda_n^{-2}\langle d_2-d_1,d_2\rangle.
$$

Therefore the previous two inequalities combine to

$$
R_{n+1}-R_n\le \langle \mathrm{acc}+b,d_2\rangle.
$$

Using $\mathrm{acc}+b=-y$, this becomes

$$
R_{n+1}-R_n\le -\langle y,d_2\rangle.
$$

This is `henergy_y`.

Now $d_2=\lambda_n v$, so

$$
\langle y,d_2\rangle=\lambda_n\langle y,v\rangle.
$$

Also $y\in A v$, and $\Phi_A(v)$ is the infimum of the set of numbers $\langle z,v\rangle$ with $z\in A v$, so

$$
\Phi_A(v)\le \langle y,v\rangle.
$$

Converting to real parts gives

$$
(\Phi_A(v))_{\mathbb R}\le \langle y,v\rangle.
$$

Since $\lambda_n\ge0$, multiplication by $-\lambda_n$ reverses the inequality:

$$
-\lambda_n\langle y,v\rangle
\le
-\lambda_n(\Phi_A(v))_{\mathbb R}.
$$

Hence

$$
R_{n+1}-R_n\le -\lambda_n(\Phi_A(v))_{\mathbb R}.
$$

This is `hmainRreal`.

Because $\Phi_A(v)$ is finite, coercing this real inequality back to $\overline{\mathbb R}$ gives

$$
(R_{n+1}-R_n:\overline{\mathbb R})
\le
\bigl(-\lambda_n(\Phi_A(v))_{\mathbb R}:\overline{\mathbb R}\bigr)
=-\lambda_n\Phi_A(v).
$$

This is the first half of `hmainR`. Rearranging the same real inequality also gives

$$
(\lambda_n\Phi_A(v))_{\mathbb R}\le R_n-R_{n+1},
$$

which is the second half of `hmainR`.

Using `henergySeq_eq` to replace $E_n$ with $R_n$, the proof obtains the first conclusion:

```math
E_{n+1}-E_n
\le
-\lambda_n\Phi_A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right).
```

This is `hmain`.

It remains to prove summability. Define

```math
T_n=\lambda_n\Phi_A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right),
\qquad
t_n=(T_n)_{\mathbb R}.
```

The proof shows $T_n\ge0$. Indeed, $\lambda_n\gt 0$ and $\Phi_A\ge0$, so their product in $\overline{\mathbb R}$ is nonnegative. Therefore $T_n\ne\bot$, and $T_n$ is also finite because $\lambda_n$ and $\Phi_A$ are finite. Hence $t_n\ge0$ is a nonnegative real number.

From the second half of `hmainR`, the proof has

$$
t_n\le R_n-R_{n+1}.
$$

It also proves the lower bound

$$
m\le R_N
$$

for every $N$. This follows because

$$
m\le (f(x_{N+1}))_{\mathbb R}
$$

and

```math
R_N=(2\lambda_N^2)^{-1}\|x_{N+1}-x_N\|^2+(f(x_{N+1}))_{\mathbb R},
```

where the kinetic term is nonnegative.

Summing $t_n\le R_n-R_{n+1}$ for $n\lt N$ gives

$$
\sum_{n=0}^{N-1}t_n
\le
\sum_{n=0}^{N-1}(R_n-R_{n+1})
=R_0-R_N
\le
R_0-m.
$$

The telescoping identity is `Finset.sum_range_sub'`. Thus the partial sums of the nonnegative sequence $t_n$ are bounded above by the fixed real number $R_0-m$. The lemma `summable_of_sum_range_le` then yields that $t_n$ is summable. Let

$$
S=\sum_{n=0}^{\infty}t_n\in\mathbb R.
$$

The remaining argument converts this real summability into convergence in $\overline{\mathbb R}$. The partial sums

$$
\sum_{n=0}^{N}t_n
$$

tend to $S$. Shifting $N$ to $N+1$ still tends to $S$. Since the coercion $\mathbb R\to\overline{\mathbb R}$ preserves limits, the extended-real partial sums

$$
\left(\sum_{n=0}^{N+1}t_n:\overline{\mathbb R}\right)
$$

tend to $(S:\overline{\mathbb R})$. For each $n$, because $T_n$ is finite, we have

$$
(t_n:\overline{\mathbb R})=T_n.
$$

Finite sums of coercions are the coercion of the finite sum, so

$$
\left(\sum_{n=0}^{N+1}t_n:\overline{\mathbb R}\right)
=\sum_{n=0}^{N+1}T_n.
$$

Therefore

```math
\sum_{n=0}^{N+1}
\lambda_n\Phi_A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right)
\longrightarrow
(S:\overline{\mathbb R}),
```

which is exactly the second conclusion.

Tactically, `intro` introduces a variable or hypothesis into the goal, `rw` rewrites with definitions or known equalities, `simp` simplifies using definitions and basic lemmas, and `exact` closes a goal by supplying a proof term. The commands `linarith` and `nlinarith` discharge linear and nonlinear arithmetic inequalities over the real numbers. `field_simp` clears denominators involving powers of $\lambda_n$, and `abel` normalizes additive expressions such as $x_{n+2}-2x_{n+1}+x_n=(x_{n+2}-x_{n+1})-(x_{n+1}-x_n)$. Finally, `convert` and `ext` are used at the end to match the proved limit statement with the exact form required by the theorem.

