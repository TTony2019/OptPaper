## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/rem_2.lean`

## Lean statement
```lean
theorem remark_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (hα_bdd : ∃ C, ∀ n, α n ≤ C) (hν_bdd : ∃ C, ∀ n, ν n ≤ C)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y)
    (ρ : ℕ → ℝ) (hρ_pos : ∃ r > 0, ∀ n, ρ n ≥ r) (hρ_bdd : ∃ R, ∀ n, ρ n ≤ R)
    (ρ_lim : ℝ) (hρ_conv : Tendsto ρ atTop (𝓝 ρ_lim))
    (M : ℝ) (hM_x : ∀ n, ‖alg.x (n+1) - x‖ ^ 2 ≤ M) (hM_y : ∀ n, ‖alg.y (n+1) - y‖ ^ 2 ≤ M)
    (h_scaled_alpha_var_summable :
      Summable (fun n => positivePart (α (n+1) / ρ (n+1) - α n / ρ n)))
    (h_scaled_nu_var_summable :
      Summable (fun n => positivePart ((μ + ν (n+1)) / ρ (n+1) - (μ + ν n) / ρ n))) :
    (∃ (ℓ : ℝ), Tendsto (fun (n : ℕ) => An alg.x alg.y x y α ν β μ n) atTop (𝓝 ℓ)) ∧
    Tendsto (fun (n : ℕ) => Bn alg.x alg.y x y α ν β μ n) atTop (𝓝 0)
```

## Statement explanation
The declaration `remark_4_1` is a convergence statement for an alternating proximal-minimization algorithm with costs to move. The ambient space $H$ is a real inner product space, so it carries the norm $\|\cdot\|$ used in all the distances below. The remaining data are two functions $f,g:H\to\mathbb{R}$, real parameters $\beta,\mu$, and sequences $\alpha,\nu:\mathbb{N}\to\mathbb{R}$. The hypothesis `hyp : H41toH46 H f g β μ` is a bundled package of standing assumptions from the paper; its full definition is not expanded in the supplied source, so only the consequences actually used in the proof are described below. The points $x,y\in H$ are reference points.

The hypotheses include:
- $\alpha_n\ge 0$ and $\nu_n\ge 0$ for every $n$.
- $\alpha$ and $\nu$ are bounded above: there are constants $C_\alpha,C_\nu$ with $\alpha_n\le C_\alpha$ and $\nu_n\le C_\nu$ for all $n$.
- `alg` is an instance of the `CA2` algorithm with three quadratic costs $(\xi,\eta)\mapsto \|\xi-\eta\|^2/2$, first step-size sequence $\alpha$, constant second parameter $\beta$, constant third parameter $\mu$, and fourth sequence $\nu$.
- `hine` is an `IsINE` condition involving $f,g$, the same quadratic costs, $0,\beta,\mu,0,x,y$. Its complete definition is not given in the supplied source, so it is treated as a hypothesis passed unchanged to the scaled convergence theorem.
- $\rho:\mathbb{N}\to\mathbb{R}$ is a scaling sequence. It has a positive lower bound: there is $r>0$ with $\rho_n\ge r$ for all $n$. It is bounded above: there is $R$ with $\rho_n\le R$ for all $n$. It converges, $\rho_n\to \rho_{\lim}$.
- $M$ bounds the squared distances of the algorithm iterates to the reference points:

  $$
  \|x_{n+1}-x\|^2\le M,\qquad \|y_{n+1}-y\|^2\le M
  $$

  for all $n$, where $x_n=\mathtt{alg.x}\ n$ and $y_n=\mathtt{alg.y}\ n$.
- The positive parts of the scaled variations of $\alpha$ and $\mu+\nu$ are summable:

  $$
  \sum_n \left(\frac{\alpha_{n+1}}{\rho_{n+1}}-\frac{\alpha_n}{\rho_n}\right)^+ < \infty,
  \qquad
  \sum_n \left(\frac{\mu+\nu_{n+1}}{\rho_{n+1}}-\frac{\mu+\nu_n}{\rho_n}\right)^+ < \infty.
  $$

The conclusion uses the quantities `An` and `Bn`. Here

$$
A_n
=
\alpha_n\mu\|x_n-x\|^2
+
\beta(\mu+\nu_n)\|y_n-y\|^2,
$$

and

$$
B_n
=
\alpha_n\mu\|x_{n+1}-x_n\|^2
+
\beta\nu_n\|y_{n+1}-y_n\|^2
+
\beta\mu\|y_n-x_{n+1}-y+x\|^2
+
\beta\mu\|y_{n+1}-x_{n+1}-y+x\|^2.
$$

The theorem states that, under the above assumptions, there exists a real number $\ell$ such that

$$
A_n\to \ell
$$

as $n\to\infty$, and also

$$
B_n\to 0.
$$

In other words, after proving a scaled convergence statement for $A_n/\rho_n$ and $B_n/\rho_n$, the theorem removes the scaling $\rho_n$ and deduces convergence of the original unscaled quantities.

## Lean proof
```lean
by
  -- Obtain the scaled convergence
  rcases remark_4_1_scaled_convergence hyp x y hα_nonneg hν_nonneg hα_bdd hν_bdd alg hine
    ρ hρ_pos M hM_x hM_y h_scaled_alpha_var_summable h_scaled_nu_var_summable with
    ⟨⟨ℓ', hAdiv⟩, hBdiv_zero⟩
  rcases hρ_bdd with ⟨R, hR⟩
  rcases hρ_pos with ⟨r, hr_pos, hr⟩
  have hρ_pos_all : ∀ n, ρ n > 0 := by
    intro n; exact lt_of_lt_of_le hr_pos (hr n)
  -- ====== A_n → ρ_lim·ℓ' via An_tendsto_of_scaled_tendsto ======
  have hAn_conv : Tendsto (fun n => An alg.x alg.y x y α ν β μ n) atTop (𝓝 (ρ_lim * ℓ')) :=
    An_tendsto_of_scaled_tendsto alg x y ρ ℓ' ρ_lim hAdiv hρ_conv
      (fun n => (hρ_pos_all n).ne')
  -- ====== B_n → 0: proved using ρ_n ≤ R ======
  have hβ_nonneg_rmk : 0 ≤ β := by linarith [hyp.beta_pos]
  have hμ_nonneg_rmk : 0 ≤ μ := by linarith [hyp.mu_pos]
  have hsq_nonneg_rmk : ∀ (v : H), 0 ≤ ‖v‖ ^ 2 := by intro v; positivity
  have hBn_nonneg : ∀ n, 0 ≤ Bn alg.x alg.y x y α ν β μ n := by
    intro n; dsimp [Bn]
    have h1 : 0 ≤ α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 :=
      mul_nonneg (mul_nonneg (hα_nonneg n) hμ_nonneg_rmk) (hsq_nonneg_rmk _)
    have h2 : 0 ≤ β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg_rmk (hν_nonneg n)) (hsq_nonneg_rmk _)
    have h3 : 0 ≤ β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg_rmk hμ_nonneg_rmk) (hsq_nonneg_rmk _)
    have h4 : 0 ≤ β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 :=
      mul_nonneg (mul_nonneg hβ_nonneg_rmk hμ_nonneg_rmk) (hsq_nonneg_rmk _)
    nlinarith
  have hR_nonneg : 0 ≤ R := by
    have h0r : ρ 0 ≥ r := hr 0
    have hR0 : ρ 0 ≤ R := hR 0
    linarith
  have h_upper : ∀ n, Bn alg.x alg.y x y α ν β μ n ≤ R * (Bn alg.x alg.y x y α ν β μ n / ρ n) := by
    intro n
    have hρ_pos' : ρ n > 0 := hρ_pos_all n
    have hρ_le_R : ρ n ≤ R := hR n
    calc
      Bn alg.x alg.y x y α ν β μ n = (Bn alg.x alg.y x y α ν β μ n / ρ n) * ρ n := by
        field_simp [hρ_pos'.ne']
      _ ≤ (Bn alg.x alg.y x y α ν β μ n / ρ n) * R := by
        gcongr
        exact div_nonneg (hBn_nonneg n) (by linarith)
      _ = R * (Bn alg.x alg.y x y α ν β μ n / ρ n) := by ring
  have hR_bound_tendsto : Tendsto (fun n => R * (Bn alg.x alg.y x y α ν β μ n / ρ n)) atTop (𝓝 (R * 0)) :=
    Filter.Tendsto.const_mul R hBdiv_zero
  have hR_bound_zero : Tendsto (fun n => R * (Bn alg.x alg.y x y α ν β μ n / ρ n)) atTop (𝓝 0) := by
    simpa [mul_zero] using hR_bound_tendsto
  have hB_tendsto_zero : Tendsto (fun n => Bn alg.x alg.y x y α ν β μ n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ => (0:ℝ)) atTop _)
      hR_bound_zero (fun n => hBn_nonneg n) (fun n => h_upper n)
  exact ⟨⟨ρ_lim * ℓ', hAn_conv⟩, hB_tendsto_zero⟩
```

## Proof explanation
The proof begins by applying the previously established scaled convergence theorem `remark_4_1_scaled_convergence`. That theorem says that, under the common hypotheses `hyp`, the nonnegativity and boundedness of $\alpha,\nu$, the `CA2` algorithm `alg`, the `IsINE` condition `hine`, the positive lower bound for $\rho$, the bounds `M` and `hM_x,hM_y`, and the two summability assumptions, there exists a real number $\ell'$ such that

$$
\frac{A_n}{\rho_n}\to \ell'
$$

and

$$
\frac{B_n}{\rho_n}\to 0.
$$

The proof calls this theorem with all the corresponding arguments and then uses `rcases ... with ⟨⟨ℓ', hAdiv⟩, hBdiv_zero⟩` to destruct the existential and the conjunction. After this step, `ℓ'` is the scaled limit of $A_n/\rho_n$, `hAdiv` is the proof that $A_n/\rho_n\to \ell'$, and `hBdiv_zero` is the proof that $B_n/\rho_n\to 0$. The hypotheses `hρ_bdd` and `hρ_conv` are not needed by the scaled theorem, so they are not passed to it.

Next the proof extracts bounds on $\rho$. The command `rcases hρ_bdd with ⟨R, hR⟩` obtains a real number $R$ such that $\rho_n\le R$ for all $n$. Similarly, `rcases hρ_pos with ⟨r, hr_pos, hr⟩` obtains $r>0$ and the inequality $\rho_n\ge r$ for all $n$. The auxiliary claim

$$
\forall n,\quad \rho_n>0
$$

is then proved with `intro n; exact lt_of_lt_of_le hr_pos (hr n)`. The tactic `intro n` introduces an arbitrary natural number $n$. The lemma `lt_of_lt_of_le` is the transitivity statement that if $0<r$ and $r\le \rho_n$, then $0<\rho_n$. Thus every $\rho_n$ is positive. This positivity is used later to justify division by $\rho_n$ and to supply the nonzero-denominator hypothesis for the next limit lemma.

The convergence of $A_n$ is obtained by invoking `An_tendsto_of_scaled_tendsto`. That lemma has the following concrete content: if the `CA2` algorithm is the one encoded by `alg`, if

$$
\frac{A_n}{\rho_n}\to \ell',
$$

if

$$
\rho_n\to \rho_{\inf},
$$

and if $\rho_n\ne 0$ for every $n$, then

$$
A_n\to \rho_{\inf}\ell'.
$$

The proof applies it with `ρinf` instantiated as `ρ_lim` and supplies the nonzero condition as `(fun n => (hρ_pos_all n).ne')`, which converts the strict positivity $0<\rho_n$ into $\rho_n\ne 0$. The mathematical reason is that $A_n$ is the product $\rho_n\cdot (A_n/\rho_n)$, and the limit of a product is the product of the limits. Hence the proof obtains

$$
A_n\to \rho_{\lim}\ell'.
$$

The rest of the proof establishes that $B_n\to 0$. First it records nonnegativity of the parameters involved. The bundled hypothesis `hyp` contains a component `hyp.beta_pos`; the proof uses `linarith [hyp.beta_pos]` to derive

$$
0\le \beta.
$$

Similarly, from `hyp.mu_pos` it derives

$$
0\le \mu.
$$

It also proves

$$
\forall v:H,\quad 0\le \|v\|^2
$$

by `intro v; positivity`; this is simply the fact that a squared norm is nonnegative.

Using these facts, the proof shows

$$
\forall n,\quad 0\le B_n.
$$

The command `dsimp [Bn]` unfolds the definition of $B_n$ into its four summands. Each summand is checked to be nonnegative:
- $\alpha_n\mu\|x_{n+1}-x_n\|^2\ge 0$, because $\alpha_n\ge 0$, $\mu\ge 0$, and $\|x_{n+1}-x_n\|^2\ge 0$;
- $\beta\nu_n\|y_{n+1}-y_n\|^2\ge 0$, because $\beta\ge 0$, $\nu_n\ge 0$, and $\|y_{n+1}-y_n\|^2\ge 0$;
- the two terms involving $\beta\mu$ are nonnegative for the same reason.

The tactic `nlinarith` then combines these four individual nonnegativity facts into the nonnegativity of their sum. Thus $0\le B_n$ for every $n$.

The proof next shows that $R$ itself is nonnegative. From `hr 0` it has $\rho_0\ge r$, from `hR 0` it has $\rho_0\le R$, and from `hr_pos` it has $r>0$. Therefore

$$
0<r\le \rho_0\le R,
$$

so `linarith` proves $0\le R$.

The key upper comparison is

$$
B_n\le R\left(\frac{B_n}{\rho_n}\right).
$$

For each fixed $n$, the proof uses $\rho_n>0$ and $\rho_n\le R$. The command `field_simp [hρ_pos'.ne']` rewrites

$$
B_n=\left(\frac{B_n}{\rho_n}\right)\rho_n,
$$

because the denominator $\rho_n$ is nonzero. Since $B_n\ge 0$, also $B_n/\rho_n\ge 0$. Multiplying the inequality $\rho_n\le R$ by the nonnegative factor $B_n/\rho_n$ gives

$$
\left(\frac{B_n}{\rho_n}\right)\rho_n
\le
\left(\frac{B_n}{\rho_n}\right)R.
$$

The tactic `gcongr` performs exactly this monotone multiplication. Finally, `ring` rearranges the right-hand side to

$$
R\left(\frac{B_n}{\rho_n}\right).
$$

Hence $B_n\le R(B_n/\rho_n)$ for every $n$.

Since $B_n/\rho_n\to 0$, multiplying by the constant $R$ preserves the limit. The command `Filter.Tendsto.const_mul R hBdiv_zero` gives

$$
R\left(\frac{B_n}{\rho_n}\right)\to R\cdot 0.
$$

The tactic `simpa [mul_zero]` simplifies $R\cdot 0$ to $0$, yielding

$$
R\left(\frac{B_n}{\rho_n}\right)\to 0.
$$

Finally, the proof applies the squeeze theorem through `tendsto_of_tendsto_of_tendsto_of_le_of_le`. That theorem says that if a lower bounding sequence tends to a limit $L$, an upper bounding sequence tends to the same limit $L$, and the middle sequence is pointwise between them, then the middle sequence also tends to $L$. Here the lower bound is the constant sequence $0$, which tends to $0$; the upper bound is $R(B_n/\rho_n)$, which has just been shown to tend to $0$; and the pointwise inequalities are

$$
0\le B_n\le R\left(\frac{B_n}{\rho_n}\right),
$$

supplied by `hBn_nonneg` and `h_upper`. Therefore the squeeze theorem gives

$$
B_n\to 0.
$$

At the end, the proof combines the two results. The command
`exact ⟨⟨ρ_lim * ℓ', hAn_conv⟩, hB_tendsto_zero⟩`
constructs the required existential and conjunction: choose $\ell=\rho_{\lim}\ell'$. The term `hAn_conv` proves $A_n\to \rho_{\lim}\ell'$, and `hB_tendsto_zero` proves $B_n\to 0$. Thus the theorem is established.

