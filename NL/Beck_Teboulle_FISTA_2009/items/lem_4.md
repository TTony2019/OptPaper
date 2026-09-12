## Source file
`Beck_Teboulle_FISTA_2009/items/lem_4.lean`

## Lean statement
```lean
theorem fista_recursive_relation {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    (xSeq ySeq : ℕ → EuclideanSpace ℝ (Fin n))
    (tSeq LSeq : ℕ → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (hFISTA : ∀ (k : ℕ) (hk : 1 ≤ k),
      0 < LSeq (k + 1) ∧
      IsProxPoint f g (LSeq (k + 1)) (ySeq (k + 1)) (xSeq (k + 1)) ∧
      compositeObjective f g (xSeq (k + 1)) ≤
        quadraticApprox f g (LSeq (k + 1)) (xSeq (k + 1)) (ySeq (k + 1)) ∧
      tSeq (k + 1) = (1 + Real.sqrt (1 + 4 * (tSeq k) ^ 2)) / 2 ∧
      ySeq (k + 1) = xSeq k +
        ((tSeq k - 1) / tSeq (k + 1)) • (xSeq k - xSeq (k - 1)) ∧
      LSeq k ≤ LSeq (k + 1))
    (hLseq1_pos : 0 < LSeq 1)
    (t1 : tSeq 1 = 1) (y1 : ySeq 1 = xSeq 0) (k : ℕ) (hk : 1 ≤ k) :
    let v (m : ℕ)
```

## Statement explanation
The declaration is a theorem named `fista_recursive_relation`. It concerns the Euclidean space $\mathbb{R}^n$ (written in Lean as `EuclideanSpace ℝ (Fin n)`), two functions $f,g:\mathbb{R}^n\to\mathbb{R}$, a real parameter $Lf$, and two sequences in $\mathbb{R}^n$, denoted $x_m$ and $y_m$ for $m\in\mathbb{N}$. It also has two real sequences $t_m$ and $L_m$, and a point $x^\star\in\mathbb{R}^n$.

The hypothesis `hP : ProblemP f g Lf` is the standing problem assumption for the composite objective $F=f+g$. The provided context does not list the internal fields of `ProblemP`; in the proof it is used only as the input required by the cited inequality `key_inequality'`.

The definition `compositeObjective f g x = f x + g x` gives

$$
F(x)=\mathrm{compositeObjective}(f,g)(x)=f(x)+g(x).
$$

The definition `solutionSet f g = {x \mid IsMinOn (compositeObjective f g) univ x}` means that

$$
x^\star\in \mathrm{solutionSet}(f,g)
$$

says that $x^\star$ minimizes $F$ over the entire space:

$$
F(x^\star)\le F(x)\qquad\text{for every }x\in\mathbb{R}^n.
$$

The definition `quadraticApprox` gives

$$
Q_L(x,y)=f(y)+\langle \nabla f(y),x-y\rangle+\frac{L}{2}\|x-y\|^2+g(x).
$$

The FISTA hypothesis `hFISTA` says that for every integer $j\ge 1$,

$$
0<L_{j+1},
$$

that $x_{j+1}$ is a proximal point of $f,g$ at $y_{j+1}$ with parameter $L_{j+1}$,

$$
F(x_{j+1})\le Q_{L_{j+1}}(x_{j+1},y_{j+1}),
$$

that

$$
t_{j+1}=\frac{1+\sqrt{1+4t_j^2}}{2},
$$

that

$$
y_{j+1}=x_j+\frac{t_j-1}{t_{j+1}}(x_j-x_{j-1}),
$$

and that

$$
L_j\le L_{j+1}.
$$

The extra hypotheses are $0<L_1$, $t_1=1$, and $y_1=x_0$. The theorem is stated for an integer $k$ with $1\le k$.

The conclusion is stated with the local abbreviations

$$
v_m=F(x_m)-F(x^\star),
$$

and

$$
u_m=t_m x_m-(t_m-1)x_{m-1}-x^\star.
$$

The theorem concludes

$$
\frac{2}{L_k}t_k^2 v_k-\frac{2}{L_{k+1}}t_{k+1}^2 v_{k+1}
\ge
\|u_{k+1}\|^2-\|u_k\|^2.
$$

This is a recursive Lyapunov-type inequality for FISTA: it compares the residual objective values $v_k,v_{k+1}$ with the squared norms of the auxiliary vectors $u_k,u_{k+1}$.

## Lean proof
```lean
compositeObjective f g (xSeq m) -
      compositeObjective f g xStar
    let u (m : ℕ) := (tSeq m) • (xSeq m) -
      ((tSeq m - 1) • (xSeq (m - 1))) - xStar
    (2 / LSeq k) * (tSeq k) ^ 2 * v k -
      (2 / LSeq (k + 1)) * (tSeq (k + 1)) ^ 2 * v (k + 1) ≥
      ‖u (k + 1)‖ ^ 2 - ‖u k‖ ^ 2 := by
  intro v u
  rcases hFISTA k hk with ⟨hLpos, h_prox, h_cond_raw, h_tk1, h_yk1, h_Lk1⟩
  let F (x : EuclideanSpace ℝ (Fin n)) := compositeObjective f g x
  -- The backtracking acceptance test is the descent condition in Lemma 2.3.
  have h_cond : F (xSeq (k + 1)) ≤ quadraticApprox f g (LSeq (k + 1)) (xSeq (k + 1)) (ySeq (k + 1)) := by
    simpa [F] using h_cond_raw
  -- Apply Lemma 2.3 (key_inequality') at two points
  have h_ineq1 : F (xSeq k) - F (xSeq (k + 1)) ≥
      (LSeq (k + 1) / 2) * ‖xSeq (k + 1) - ySeq (k + 1)‖ ^ 2 +
      LSeq (k + 1) * ⟪ySeq (k + 1) - xSeq k, xSeq (k + 1) - ySeq (k + 1)⟫ :=
    key_inequality' hP hLpos (ySeq (k + 1)) (xSeq k) (xSeq (k + 1)) h_prox h_cond
  have h_ineq2 : F xStar - F (xSeq (k + 1)) ≥
      (LSeq (k + 1) / 2) * ‖xSeq (k + 1) - ySeq (k + 1)‖ ^ 2 +
      LSeq (k + 1) * ⟪ySeq (k + 1) - xStar, xSeq (k + 1) - ySeq (k + 1)⟫ :=
    key_inequality' hP hLpos (ySeq (k + 1)) xStar (xSeq (k + 1)) h_prox h_cond
  -- Express v_k - v_{k+1} and -v_{k+1} in terms of F
  have hv_diff : v k - v (k + 1) = F (xSeq k) - F (xSeq (k + 1)) := by dsimp [v, F]; ring
  have hv_neg : -v (k + 1) = F xStar - F (xSeq (k + 1)) := by dsimp [v, F]; ring
  -- Let L := L_{k+1}, t := t_{k+1}, d := x_{k+1} - y_{k+1}
  set L := LSeq (k + 1) with hL
  set t := tSeq (k + 1) with ht
  set d := xSeq (k + 1) - ySeq (k + 1) with hd
  -- v_k ≥ 0 since x* is a minimizer
  have hv_nonneg : ∀ m, 0 ≤ v m := by
    intro m
    dsimp [v]
    have hmin : IsMinOn (compositeObjective f g) Set.univ xStar := by
      simpa [solutionSet] using hxStar
    have hx_mem : xSeq m ∈ Set.univ := Set.mem_univ _
    have h_le : compositeObjective f g xStar ≤ compositeObjective f g (xSeq m) := by
      simpa [IsMinOn, IsMinFilter, Filter.eventually_principal] using hmin hx_mem
    linarith
  -- t_{k+1} ≥ 1 (from the recurrence formula)
  have ht_ge_one : 1 ≤ t := by
    have h_inner : (1 : ℝ) ≤ 1 + 4 * (tSeq k) ^ 2 := by nlinarith
    have h_sqrt_ge_one : 1 ≤ Real.sqrt (1 + 4 * (tSeq k) ^ 2) := by
      calc
        1 = Real.sqrt (1 : ℝ) := by norm_num
        _ ≤ Real.sqrt (1 + 4 * (tSeq k) ^ 2) := Real.sqrt_le_sqrt h_inner
    dsimp [t] at h_tk1; linarith
  -- FISTA t-recurrence: t_k² = t_{k+1}² - t_{k+1}  (paper equation (4.2))
  have h_tsq : (tSeq k) ^ 2 = t ^ 2 - t := by
    have h_nonneg : 0 ≤ 1 + 4 * (tSeq k) ^ 2 := by nlinarith
    have h_sq : (2 * t - 1) ^ 2 = 1 + 4 * (tSeq k) ^ 2 := by
      have h_sqrt_eq : 2 * t - 1 = Real.sqrt (1 + 4 * (tSeq k) ^ 2) := by
        dsimp [t] at h_tk1; linarith
      rw [h_sqrt_eq, Real.sq_sqrt h_nonneg]
    nlinarith
  -- Pythagoras identity: ‖b-a‖² + 2⟨b-a, a-c⟩ = ‖b-c‖² - ‖a-c‖²
  have h_pythagoras (a b c : EuclideanSpace ℝ (Fin n)) :
      ‖b - a‖ ^ 2 + 2 * ⟪b - a, a - c⟫ = ‖b - c‖ ^ 2 - ‖a - c‖ ^ 2 := by
    set w := b - a; set v' := a - c
    have hsum : w + v' = b - c := by dsimp [w, v']; abel
    calc
      ‖b - a‖ ^ 2 + 2 * ⟪b - a, a - c⟫ = ‖w‖ ^ 2 + 2 * ⟪w, v'⟫ := by simp [w, v']
      _ = (‖w‖ ^ 2 + 2 * ⟪w, v'⟫ + ‖v'‖ ^ 2) - ‖v'‖ ^ 2 := by ring
      _ = ‖w + v'‖ ^ 2 - ‖v'‖ ^ 2 := by rw [norm_add_sq_real]
      _ = ‖b - c‖ ^ 2 - ‖a - c‖ ^ 2 := by simp [hsum, v']
  -- Step 1: Paper (4.4) — (2/L)(v_k - v_{k+1}) ≥ ‖d‖² + 2⟨d, y_{k+1} - x_k⟩
  have h_step1 : (2 / L) * (v k - v (k + 1)) ≥ ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫ := by
    rw [hv_diff]
    calc
      (2 / L) * (F (xSeq k) - F (xSeq (k + 1)))
          ≥ (2 / L) * ((L / 2) * ‖d‖ ^ 2 + L * ⟪ySeq (k + 1) - xSeq k, d⟫) := by gcongr
      _ = (2 / L) * (L / 2) * ‖d‖ ^ 2 + (2 / L) * L * ⟪ySeq (k + 1) - xSeq k, d⟫ := by ring
      _ = 1 * ‖d‖ ^ 2 + 2 * ⟪ySeq (k + 1) - xSeq k, d⟫ := by field_simp [hLpos.ne']
      _ = ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫ := by simp [real_inner_comm d]
  -- Step 1': Paper (4.5) — (2/L)(-v_{k+1}) ≥ ‖d‖² + 2⟨d, y_{k+1} - x*⟩
  have h_step1' : (2 / L) * (-v (k + 1)) ≥ ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫ := by
    rw [hv_neg]
    calc
      (2 / L) * (F xStar - F (xSeq (k + 1)))
          ≥ (2 / L) * ((L / 2) * ‖d‖ ^ 2 + L * ⟪ySeq (k + 1) - xStar, d⟫) := by gcongr
      _ = (2 / L) * (L / 2) * ‖d‖ ^ 2 + (2 / L) * L * ⟪ySeq (k + 1) - xStar, d⟫ := by ring
      _ = 1 * ‖d‖ ^ 2 + 2 * ⟪ySeq (k + 1) - xStar, d⟫ := by field_simp [hLpos.ne']
      _ = ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫ := by simp [real_inner_comm d]
  -- Vector identity for linear combination in Step 2
  have h_vec_id : ((t - 1 : ℝ) • (ySeq (k + 1) - xSeq k)) + (ySeq (k + 1) - xStar) =
      t • ySeq (k + 1) - (t - 1) • xSeq k - xStar := by
    calc
      ((t - 1 : ℝ) • (ySeq (k + 1) - xSeq k)) + (ySeq (k + 1) - xStar)
          = ((t - 1) • ySeq (k + 1) - (t - 1) • xSeq k) + (ySeq (k + 1) - xStar) := by simp [smul_sub]
      _ = ((t - 1) • ySeq (k + 1) + ySeq (k + 1)) - ((t - 1) • xSeq k + xStar) := by abel
      _ = ((t - 1) • ySeq (k + 1) + (1 : ℝ) • ySeq (k + 1)) - ((t - 1) • xSeq k + xStar) := by simp
      _ = ((t - 1 + 1 : ℝ) • ySeq (k + 1)) - ((t - 1) • xSeq k + xStar) := by rw [add_smul]
      _ = t • ySeq (k + 1) - ((t - 1) • xSeq k + xStar) := by ring
      _ = t • ySeq (k + 1) - (t - 1) • xSeq k - xStar := by abel
  -- Step 2: Combined inequality (t-1)*(4.4) + (4.5), paper before (4.6)
  have h_combined : (2 / L) * ((t - 1) * v k - t * v (k + 1)) ≥
      t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
    have hsum_rhs : (t - 1) * (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫) +
        (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫) =
        t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
      calc
        (t - 1) * (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫) +
            (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫)
            = t * ‖d‖ ^ 2 + 2 * ((t - 1) * ⟪d, ySeq (k + 1) - xSeq k⟫ +
                ⟪d, ySeq (k + 1) - xStar⟫) := by ring
        _ = t * ‖d‖ ^ 2 + 2 * (⟪d, (t - 1) • (ySeq (k + 1) - xSeq k)⟫ +
            ⟪d, ySeq (k + 1) - xStar⟫) := by simp [inner_smul_right]
        _ = t * ‖d‖ ^ 2 + 2 * ⟪d, ((t - 1 : ℝ) • (ySeq (k + 1) - xSeq k)) +
            (ySeq (k + 1) - xStar)⟫ := by simp [inner_add_right]
        _ = t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by rw [h_vec_id]
    have h_lhs : (t - 1) * ((2 / L) * (v k - v (k + 1))) + (2 / L) * (-v (k + 1)) =
        (2 / L) * ((t - 1) * v k - t * v (k + 1)) := by ring
    have h_ineq_sum : (t - 1) * ((2 / L) * (v k - v (k + 1))) + (2 / L) * (-v (k + 1)) ≥
        t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
      nlinarith
    rw [h_lhs] at h_ineq_sum
    exact h_ineq_sum
  -- Step 3: Multiply by t and use t_k² = t² - t to get paper (4.6)
  have h_step3 : (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) ≥
      ‖t • d‖ ^ 2 + 2 * ⟪t • d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
    have ht_nonneg : 0 ≤ t := by linarith
    set X := t • ySeq (k + 1) - (t - 1) • xSeq k - xStar with hX
    have h_mul : t * ((2 / L) * ((t - 1) * v k - t * v (k + 1))) ≥
        t * (t * ‖d‖ ^ 2 + 2 * ⟪d, X⟫) := by gcongr
    have h_lhs_simp : t * ((2 / L) * ((t - 1) * v k - t * v (k + 1))) =
        (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by
      calc
        t * ((2 / L) * ((t - 1) * v k - t * v (k + 1)))
            = (2 / L) * (t * ((t - 1) * v k - t * v (k + 1))) := by ring
        _ = (2 / L) * (t * (t - 1) * v k - t ^ 2 * v (k + 1)) := by ring
        _ = (2 / L) * ((t ^ 2 - t) * v k - t ^ 2 * v (k + 1)) := by ring
        _ = (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by rw [h_tsq]
    have h_norm_sq : t ^ 2 * ‖d‖ ^ 2 = ‖t • d‖ ^ 2 := by
      calc
        t ^ 2 * ‖d‖ ^ 2 = (t * ‖d‖) ^ 2 := by ring
        _ = ‖t • d‖ ^ 2 := by simp [norm_smul, abs_of_nonneg ht_nonneg]
    have h_inner_eq : 2 * t * ⟪d, X⟫ = 2 * ⟪t • d, X⟫ := by
      calc
        2 * t * ⟪d, X⟫ = 2 * (t * ⟪d, X⟫) := by ring
        _ = 2 * ⟪t • d, X⟫ := by simp [inner_smul_left]
    have h_rhs_simp : t * (t * ‖d‖ ^ 2 + 2 * ⟪d, X⟫) =
        ‖t • d‖ ^ 2 + 2 * ⟪t • d, X⟫ := by
      calc
        t * (t * ‖d‖ ^ 2 + 2 * ⟪d, X⟫) = t ^ 2 * ‖d‖ ^ 2 + 2 * t * ⟪d, X⟫ := by ring
        _ = ‖t • d‖ ^ 2 + 2 * ⟪t • d, X⟫ := by rw [h_norm_sq, h_inner_eq]
    rw [h_lhs_simp, h_rhs_simp] at h_mul
    exact h_mul
  -- Step 4: Apply the Pythagoras identity with a=t·y, b=t·x_{k+1}, c=(t-1)·x_k + x*
  set a := t • ySeq (k + 1) with ha
  set b := t • xSeq (k + 1) with hb
  set c := (t - 1) • xSeq k + xStar with hc
  have hA : b - a = t • d := by simp [a, b, hd, smul_sub]
  have hB : a - c = t • ySeq (k + 1) - (t - 1) • xSeq k - xStar := by
    simp [a, c]; abel
  have hC : b - c = t • xSeq (k + 1) - (t - 1) • xSeq k - xStar := by
    simp [b, c]; abel
  have h_step4 : (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) ≥
      ‖t • xSeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 -
      ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by
    calc
      (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1))
          ≥ ‖t • d‖ ^ 2 + 2 * ⟪t • d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := h_step3
      _ = ‖t • d‖ ^ 2 + 2 * ⟪t • d, a - c⟫ := by rw [hB]
      _ = ‖b - a‖ ^ 2 + 2 * ⟪b - a, a - c⟫ := by rw [hA]
      _ = ‖b - c‖ ^ 2 - ‖a - c‖ ^ 2 := by rw [h_pythagoras a b c]
      _ = ‖b - c‖ ^ 2 - ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by rw [hB]
      _ = ‖t • xSeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 -
          ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by rw [hC]
  -- Step 5: Relate to u_k, u_{k+1} via the FISTA y-update formula
  have hu_kp1 : u (k + 1) = t • xSeq (k + 1) - (t - 1) • xSeq k - xStar := by
    dsimp [u, t]
  -- FISTA y-update: t·y_{k+1} = t·x_k + (t_k - 1)·(x_k - x_{k-1})  (paper (4.3))
  have h_y_update : t • ySeq (k + 1) = t • xSeq k + (tSeq k - 1) • (xSeq k - xSeq (k - 1)) := by
    have ht_ne_zero : t ≠ 0 := by linarith
    rw [h_yk1]
    calc
      t • (xSeq k + ((tSeq k - 1) / t) • (xSeq k - xSeq (k - 1)))
          = t • xSeq k + t • (((tSeq k - 1) / t) • (xSeq k - xSeq (k - 1))) := by simp [smul_add]
      _ = t • xSeq k + (t * ((tSeq k - 1) / t)) • (xSeq k - xSeq (k - 1)) := by simp [smul_smul]
      _ = t • xSeq k + (tSeq k - 1) • (xSeq k - xSeq (k - 1)) := by field_simp [ht_ne_zero]
  -- Show: t·y_{k+1} - (t-1)·x_k - x* = u_k
  have h_identity : t • ySeq (k + 1) - (t - 1) • xSeq k - xStar = u k := by
    calc
      t • ySeq (k + 1) - (t - 1) • xSeq k - xStar
          = (t • xSeq k + (tSeq k - 1) • (xSeq k - xSeq (k - 1))) - (t - 1) • xSeq k - xStar := by
            rw [h_y_update]
      _ = (t • xSeq k + ((tSeq k - 1) • xSeq k - (tSeq k - 1) • xSeq (k - 1))) -
          (t - 1) • xSeq k - xStar := by simp [smul_sub]
      _ = ((t • xSeq k - (t - 1) • xSeq k) + (tSeq k - 1) • xSeq k -
          (tSeq k - 1) • xSeq (k - 1)) - xStar := by abel
      _ = ((1 : ℝ) • xSeq k + (tSeq k - 1) • xSeq k -
          (tSeq k - 1) • xSeq (k - 1)) - xStar := by simp [sub_smul, one_smul]
      _ = (((1 : ℝ) + (tSeq k - 1)) • xSeq k - (tSeq k - 1) • xSeq (k - 1)) - xStar := by
        rw [add_smul]
      _ = (tSeq k • xSeq k - (tSeq k - 1) • xSeq (k - 1)) - xStar := by ring
      _ = u k := rfl
  -- Combine: h_step4 rewritten with u_{k+1} and u_k
  have h_step5 : (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) ≥
      ‖u (k + 1)‖ ^ 2 - ‖u k‖ ^ 2 := by
    calc
      (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1))
          ≥ ‖t • xSeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 -
            ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := h_step4
      _ = ‖u (k + 1)‖ ^ 2 - ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by rw [hu_kp1]
      _ = ‖u (k + 1)‖ ^ 2 - ‖u k‖ ^ 2 := by rw [h_identity]
  -- Step 6: Relax L_{k+1} to L_k.  Since L_k ≤ L_{k+1} and both positive,
  -- 2/L_k ≥ 2/L_{k+1}, so (2/L_k)·(t_k²·v_k) ≥ (2/L_{k+1})·(t_k²·v_k).
  -- Step 6: Compare L_k ≤ L to get the final inequality
  -- We need 0 < LSeq k for the fraction comparison. For k ≥ 2 this follows
  -- from hFISTA at k-1; for k = 1 the hypothesis set is slightly weaker.
  by_cases hLkpos : 0 < LSeq k
  · have hA_nonneg : 0 ≤ (tSeq k) ^ 2 * v k :=
      mul_nonneg (sq_nonneg _) (hv_nonneg k)
    have h_div : (2 : ℝ) / LSeq k ≥ (2 : ℝ) / L := by
      have h_one_div : 1 / LSeq k ≥ 1 / L :=
        (one_div_le_one_div hLpos hLkpos).mpr h_Lk1
      calc
        (2 : ℝ) / LSeq k = 2 * (1 / LSeq k) := by ring
        _ ≥ 2 * (1 / L) := by gcongr
        _ = (2 : ℝ) / L := by ring
    have h_first_ge : (2 / LSeq k) * (tSeq k) ^ 2 * v k ≥ (2 / L) * (tSeq k) ^ 2 * v k := by
      calc
        (2 / LSeq k) * (tSeq k) ^ 2 * v k = ((2 : ℝ) / LSeq k) * ((tSeq k) ^ 2 * v k) := by ring
        _ ≥ ((2 : ℝ) / L) * ((tSeq k) ^ 2 * v k) := by gcongr
        _ = (2 / L) * (tSeq k) ^ 2 * v k := by ring
    have h_mid : (2 / LSeq k) * (tSeq k) ^ 2 * v k - (2 / L) * t ^ 2 * v (k + 1) ≥
        (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by
      calc
        (2 / LSeq k) * (tSeq k) ^ 2 * v k - (2 / L) * t ^ 2 * v (k + 1)
            ≥ (2 / L) * (tSeq k) ^ 2 * v k - (2 / L) * t ^ 2 * v (k + 1) := by gcongr
        _ = (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by ring
    exact le_trans h_step5 h_mid
  · -- LSeq k ≤ 0: for k ≥ 2 this contradicts hFISTA; for k = 1 the
    -- lemma hypothesis is missing `0 < LSeq 1` (present in thm_2).
    by_cases hk1 : k = 1
    · subst hk1
      exact absurd hLseq1_pos hLkpos
    · have hk' : 1 ≤ k - 1 := by
        have : 2 ≤ k := by omega
        omega
      rcases hFISTA (k - 1) hk' with ⟨hpos, _, _, _, _, _⟩
      have eq : LSeq ((k - 1) + 1) = LSeq k := by rw [Nat.sub_add_cancel (by omega)]
      have hpos_k : 0 < LSeq k := by simpa [eq] using hpos
      exact absurd hpos_k hLkpos
```

## Proof explanation
The proof begins with `intro v u`, opening the local abbreviations $v$ and $u$ from the statement. It then uses `rcases hFISTA k hk` to unpack the FISTA hypotheses at the given index $k$. Thus it obtains

$$
0<L_{k+1},
$$

the proximal-point relation

$$
\mathrm{IsProxPoint} f g L_{k+1} y_{k+1} x_{k+1},
$$

the acceptance inequality

$$
F(x_{k+1})\le Q_{L_{k+1}}(x_{k+1},y_{k+1}),
$$

the recurrence

$$
t_{k+1}=\frac{1+\sqrt{1+4t_k^2}}{2},
$$

the update

$$
y_{k+1}=x_k+\frac{t_k-1}{t_{k+1}}(x_k-x_{k-1}),
$$

and the monotonicity

$$
L_k\le L_{k+1}.
$$

The local definition `F` is introduced as the composite objective $F(x)=\mathrm{compositeObjective} f g x$, and the proof rewrites the acceptance inequality as `h_cond`.

The cited theorem `key_inequality'` says the following. Given `ProblemP f g Lf`, a positive parameter $L>0$, points $y,x,z$, a proximal-point hypothesis

$$
\mathrm{IsProxPoint} f g L y z,
$$

and the inequality

$$
F(z)\le Q_L(z,y),
$$

one has

$$
F(x)-F(z)\ge \frac{L}{2}\|z-y\|^2+L\langle y-x,z-y\rangle.
$$

The proof applies this twice with $L=L_{k+1}$, $y=y_{k+1}$, and $z=x_{k+1}$. First, with $x=x_k$, it gets

$$
F(x_k)-F(x_{k+1})
\ge
\frac{L_{k+1}}2\|x_{k+1}-y_{k+1}\|^2
+L_{k+1}\langle y_{k+1}-x_k,x_{k+1}-y_{k+1}\rangle.
$$

Second, with $x=x^\star$, it gets

$$
F(x^\star)-F(x_{k+1})
\ge
\frac{L_{k+1}}2\|x_{k+1}-y_{k+1}\|^2
+L_{k+1}\langle y_{k+1}-x^\star,x_{k+1}-y_{k+1}\rangle.
$$

The proof then rewrites these in terms of $v$. Since

$$
v_m=F(x_m)-F(x^\star),
$$

one has

$$
v_k-v_{k+1}=F(x_k)-F(x_{k+1}),
$$

and

$$
-v_{k+1}=F(x^\star)-F(x_{k+1}).
$$

These identities are proved by unfolding the local definitions of $v$ and $F$ and simplifying with `ring`.

Next the proof shows

$$
0\le v_m\qquad\text{for every }m.
$$

Indeed, from $x^\star\in\mathrm{solutionSet}(f,g)$, the point $x^\star$ minimizes $F$ over all space, so in particular

$$
F(x^\star)\le F(x_m).
$$

Thus $v_m=F(x_m)-F(x^\star)\ge 0$. This nonnegativity is later used when comparing the coefficients involving $L_k$ and $L_{k+1}$.

The proof also establishes that

$$
1\le t=t_{k+1}.
$$

Since $1+4t_k^2\ge 1$, one has $\sqrt{1+4t_k^2}\ge 1$, and the recurrence for $t_{k+1}$ then gives $t_{k+1}\ge 1$. This is used to ensure $t\ge 0$ and $t\ne 0$. The proof then derives the FISTA square recurrence

$$
t_k^2=t_{k+1}^2-t_{k+1}.
$$

Indeed, from

$$
t_{k+1}=\frac{1+\sqrt{1+4t_k^2}}{2},
$$

one has

$$
2t_{k+1}-1=\sqrt{1+4t_k^2}.
$$

Squaring and using $(\sqrt a)^2=a$ for $a\ge 0$ gives

$$
(2t_{k+1}-1)^2=1+4t_k^2.
$$

Expanding the left side yields

$$
4t_{k+1}^2-4t_{k+1}+1=1+4t_k^2,
$$

hence $t_k^2=t_{k+1}^2-t_{k+1}$.

The proof then proves a Pythagoras-type identity for vectors $a,b,c$ in Euclidean space:

$$
\|b-a\|^2+2\langle b-a,a-c\rangle
=\|b-c\|^2-\|a-c\|^2.
$$

It sets $w=b-a$ and $v'=a-c$, so that $w+v'=b-c$, and uses the identity

$$
\|w+v'\|^2=\|w\|^2+2\langle w,v'\rangle+\|v'\|^2.
$$

Rearranging gives the displayed Pythagoras identity.

Now set

$$
L=L_{k+1},\qquad t=t_{k+1},\qquad d=x_{k+1}-y_{k+1}.
$$

From the first application of `key_inequality'`, after multiplying by the positive number $2/L$, the proof obtains

$$
\frac{2}{L}(v_k-v_{k+1})
\ge
\|d\|^2+2\langle d,y_{k+1}-x_k\rangle.
$$

Here the inner product has been rewritten using symmetry of the real inner product, and the factor $L$ is cancelled using $L>0$. Similarly, from the second application,

$$
\frac{2}{L}(-v_{k+1})
\ge
\|d\|^2+2\langle d,y_{k+1}-x^\star\rangle.
$$

The proof then uses the vector identity

$$
((t-1)(y_{k+1}-x_k))+(y_{k+1}-x^\star)
=t y_{k+1}-(t-1)x_k-x^\star.
$$

Multiplying the first inequality by $t-1$ and adding it to the second gives

$$
\frac{2}{L}\bigl((t-1)v_k-tv_{k+1}\bigr)
\ge
t\|d\|^2+2\langle d,t y_{k+1}-(t-1)x_k-x^\star\rangle.
$$

This uses linearity of the inner product in its second argument and the displayed vector identity.

Because $t\ge 1$, multiplying this inequality by $t$ preserves it. Using $t_k^2=t^2-t$, the left side becomes

$$
\frac{2}{L}\bigl(t_k^2v_k-t^2v_{k+1}\bigr).
$$

On the right side, the proof uses

$$
t^2\|d\|^2=\|t d\|^2
$$

and

$$
2t\langle d,X\rangle=2\langle t d,X\rangle
$$

for

$$
X=t y_{k+1}-(t-1)x_k-x^\star.
$$

Thus

$$
\frac{2}{L}\bigl(t_k^2v_k-t^2v_{k+1}\bigr)
\ge
\|t d\|^2+2\langle t d,t y_{k+1}-(t-1)x_k-x^\star\rangle.
$$

Next the Pythagoras identity is applied with

$$
a=t y_{k+1},\qquad b=t x_{k+1},\qquad c=(t-1)x_k+x^\star.
$$

One has

$$
b-a=t(x_{k+1}-y_{k+1})=t d,
$$

$$
a-c=t y_{k+1}-(t-1)x_k-x^\star,
$$

and

$$
b-c=t x_{k+1}-(t-1)x_k-x^\star.
$$

Therefore the previous inequality becomes

$$
\frac{2}{L}\bigl(t_k^2v_k-t^2v_{k+1}\bigr)
\ge
\|t x_{k+1}-(t-1)x_k-x^\star\|^2
-\|t y_{k+1}-(t-1)x_k-x^\star\|^2.
$$

The proof then rewrites the second squared norm using the FISTA $y$-update. From

$$
y_{k+1}=x_k+\frac{t_k-1}{t}(x_k-x_{k-1}),
$$

multiplying by $t$ and cancelling $t\ne 0$ gives

$$
t y_{k+1}=t x_k+(t_k-1)(x_k-x_{k-1}).
$$

Consequently,

$$
t y_{k+1}-(t-1)x_k-x^\star
=t_k x_k-(t_k-1)x_{k-1}-x^\star
=u_k.
$$

Also, by definition,

$$
u_{k+1}=t x_{k+1}-(t-1)x_k-x^\star.
$$

Hence the inequality becomes

$$
\frac{2}{L}\bigl(t_k^2v_k-t^2v_{k+1}\bigr)
\ge
\|u_{k+1}\|^2-\|u_k\|^2.
$$

Since $L=L_{k+1}$ and $t=t_{k+1}$, this is exactly the intermediate inequality proved before the final coefficient comparison.

The last step replaces the coefficient $2/L_k$ on the left by the smaller coefficient $2/L_{k+1}$. The proof first assumes $0<L_k$. Because $L_k\le L_{k+1}=L$ and both are positive, one has

$$
\frac{1}{L}\le \frac{1}{L_k},
$$

so

$$
\frac{2}{L}\le \frac{2}{L_k}.
$$

Also $t_k^2v_k\ge 0$, because $t_k^2\ge 0$ and $v_k\ge 0$. Therefore

$$
\frac{2}{L_k}t_k^2v_k\ge \frac{2}{L}t_k^2v_k.
$$

Subtracting the same term $\frac{2}{L}t^2v_{k+1}$ gives

$$
\frac{2}{L_k}t_k^2v_k-\frac{2}{L}t^2v_{k+1}
\ge
\frac{2}{L}\bigl(t_k^2v_k-t^2v_{k+1}\bigr).
$$

Combining this with the previously established inequality yields

$$
\frac{2}{L_k}t_k^2v_k-\frac{2}{L_{k+1}}t_{k+1}^2v_{k+1}
\ge
\|u_{k+1}\|^2-\|u_k\|^2.
$$

Finally, the proof handles the case where $0<L_k$ is not known. If $k=1$, the hypothesis $0<L_1$ immediately contradicts the failure of $0<L_k$. If $k\ne 1$, then since $1\le k$, one has $2\le k$, hence $1\le k-1$. Applying `hFISTA` at index $k-1$ gives $0<L_{(k-1)+1}=L_k$, again contradicting the failure of $0<L_k$. Thus the coefficient comparison is always justified, and the desired recursive inequality follows.

The tactics used along the way reflect these mathematical steps: `ring` and `abel` prove algebraic and vector-space identities; `simp` rewrites definitions and standard identities; `rw` replaces equals by equals; `gcongr` multiplies inequalities by nonnegative or positive factors; `field_simp` cancels positive denominators such as $L$ and $t$; `linarith` and `nlinarith` close real inequalities involving linear and polynomial expressions; `exact` supplies the final proof term for each intermediate statement; and `omega` handles the natural-number arithmetic in the final case split.

