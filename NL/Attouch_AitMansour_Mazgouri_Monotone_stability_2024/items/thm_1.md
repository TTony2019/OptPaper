## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_1.lean`

## Lean statement
```lean
theorem thm_1 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (u₀ v₀ : M → H) (α : M → ℝ) (θ₁ θ₂ : ℝ)
    (hγ : 0 < γ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂) :
    (∀ μ ∈ V, ∃ x dx ddx : ℝ → H,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) x dx ddx ∧
        ∀ y dy ddy : ℝ → H, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) y dy ddy →
          Set.EqOn x y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V,
      let m_μ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))
      let m := max m_μ m_μ'
      (∃ x x' : ℝ → H, (∃ dx ddx : ℝ → H, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) x dx ddx) ∧
        (∃ dx' ddx' : ℝ → H, ext_def_2 (A μ') γ (u₀ μ') (v₀ μ') x' dx' ddx') ∧
        ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → ‖x t - x' t‖ ≤
          Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂))
```

## Statement explanation
The theorem `thm_1` is a parameter-dependent well-posedness and stability result for a family of damped second-order dynamics indexed by a parameter \(\mu\) in a set \(V\). The space \(H\) is a complete real inner product space, and \(M\) is a normed abelian group containing the parameter set \(V\). For each parameter \(\mu\), the map
\[
A_\mu := A(\mu) : H \to H
\]
is an operator on \(H\). The real number \(\gamma\) is positive and plays the role of a damping coefficient. The maps \(u_0,v_0:M\to H\) give the initial position and initial velocity data depending on \(\mu\), and \(\alpha:M\to\mathbb R\) supplies a cocoercivity constant for each \(A_\mu\). The numbers \(\theta_1,\theta_2\) control Hölder continuity of the family \(\mu\mapsto A_\mu\) in the parameter.

The first main hypothesis is that for every \(\mu\in V\), the constant \(\alpha(\mu)\) is positive and \(A_\mu\) satisfies the cocoercive inequality
\[
\alpha(\mu)\|A_\mu u-A_\mu v\|^2
\le
\langle A_\mu u-A_\mu v,\;u-v\rangle
\qquad\text{for all }u,v\in H.
\]
The second main hypothesis says that \(0<\theta_1\), \(0<\theta_2\), \(\theta_2\le 1\), and that for every \(u\in H\) and \(\mu,\mu'\in V\),
\[
\|A_\mu u-A_{\mu'}u\|
\le
\theta_1\|\mu-\mu'\|^{\theta_2}.
\]
Thus the operators depend Hölder-continuously on the parameter with exponent \(\theta_2\).

The conclusion is a conjunction. First, for every \(\mu\in V\), there exists a solution triple \(x,dx,ddx\) of the project’s solution predicate
\[
\texttt{ext\_def\_2}(A_\mu,\gamma,u_0(\mu),v_0(\mu),x,dx,ddx),
\]
and this solution is unique on the interval \([0,\infty)\) among such solutions: if \(y,dy,ddy\) is any other solution for the same operator, damping, and initial data, then \(x(t)=y(t)\) for every \(t\ge 0\).

Second, for any two parameters \(\mu,\mu'\in V\), define
\[
m_\mu=\sqrt{1+2\gamma^2+\frac{2}{\alpha(\mu)^2}},\qquad
m_{\mu'}=\sqrt{1+2\gamma^2+\frac{2}{\alpha(\mu')^2}},\qquad
m=\max(m_\mu,m_{\mu'}).
\]
Then there exist a solution \(x\) for \(\mu\) and a solution \(x'\) for \(\mu'\) such that, for almost every \(t\) with respect to Lebesgue measure, if \(t\ge 0\), then
\[
\|x(t)-x'(t)\|
\le
e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+
\frac{\theta_1}{m}\bigl(e^{mt}-1\bigr)\|\mu-\mu'\|^{\theta_2}.
\]
In fact the proof establishes the inequality pointwise for every \(t\ge 0\), so the almost-everywhere formulation is immediate.

## Lean proof
```lean
by
  constructor
  · intro μ hμ
    obtain ⟨x, dx, ddx, hx⟩ := exists_damped_solution_of_cocoercive
      (A μ) γ (u₀ μ) (v₀ μ) (α μ) hγ (hC₁ μ hμ).1 (hC₁ μ hμ).2
    refine ⟨x, dx, ddx, hx, ?_⟩
    intro y dy ddy hy t ht
    have hbound := damped_solution_stability (A μ) (A μ) γ
      (u₀ μ) (v₀ μ) (u₀ μ) (v₀ μ) (α μ) (α μ) 0
      (hC₁ μ hμ).1 (hC₁ μ hμ).1 (hC₁ μ hμ).2 (hC₁ μ hμ).2
      (by norm_num) (fun u => by simp) hx hy t ht
    have hzero : ‖x t - y t‖ = 0 := by
      apply le_antisymm
      · simpa using hbound
      · exact norm_nonneg _
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · intro μ hμ μ' hμ'
    dsimp only
    obtain ⟨x, dx, ddx, hx⟩ :=
      exists_damped_solution_of_cocoercive
        (A μ) γ (u₀ μ) (v₀ μ) (α μ) hγ (hC₁ μ hμ).1 (hC₁ μ hμ).2
    obtain ⟨x', dx', ddx', hx'⟩ :=
      exists_damped_solution_of_cocoercive
        (A μ') γ (u₀ μ') (v₀ μ') (α μ') hγ (hC₁ μ' hμ').1 (hC₁ μ' hμ').2
    let D : ℝ := θ₁ * ‖μ - μ'‖ ^ θ₂
    have hD0 : 0 ≤ D := by
      dsimp [D]
      exact mul_nonneg hC₂.1.le (Real.rpow_nonneg (norm_nonneg _) _)
    have hD : ∀ u : H, ‖A μ u - A μ' u‖ ≤ D := by
      intro u
      simpa [D] using hC₂.2.2.2 u μ μ' hμ hμ'
    refine ⟨x, x', ⟨dx, ddx, hx⟩, ⟨dx', ddx', hx'⟩, ?_⟩
    apply Filter.Eventually.of_forall
    intro t ht
    have hstable := damped_solution_stability
      (A μ) (A μ') γ (u₀ μ) (v₀ μ) (u₀ μ') (v₀ μ')
      (α μ) (α μ') D (hC₁ μ hμ).1 (hC₁ μ' hμ').1
      (hC₁ μ hμ).2 (hC₁ μ' hμ').2 hD0 hD hx hx' t ht
    dsimp only at hstable
    convert hstable using 1
    dsimp [D]
    ring
```

## Proof explanation
The proof begins with `constructor`, which splits the conjunction into the existence/uniqueness statement and the two-parameter stability statement.

For the first conjunct, the proof introduces an arbitrary \(\mu\in V\) by `intro μ hμ`. It then invokes `exists_damped_solution_of_cocoercive`. That cited theorem says that if \(H\) is complete, \(\gamma>0\), \(\alpha>0\), and an operator \(A:H\to H\) satisfies
\[
\alpha\|A u-A v\|^2\le \langle A u-A v,u-v\rangle
\]
for all \(u,v\), then there exists a solution triple \(x,dx,ddx\) satisfying `ext_def_2 A γ u₀ v₀ x dx ddx`. Here it is instantiated with \(A=A_\mu\), \(u_0=u_0(\mu)\), \(v_0=v_0(\mu)\), and \(\alpha=\alpha(\mu)\). The positivity of \(\alpha(\mu)\) comes from `(hC₁ μ hμ).1`, and the cocoercivity inequality for \(A_\mu\) comes from `(hC₁ μ hμ).2`. Thus `obtain` extracts a triple \(x,dx,ddx\) and a proof `hx` that it solves the damped system for \(A_\mu\).

To prove uniqueness, the proof fixes another solution \(y,dy,ddy\) and a time \(t\ge 0\), via `intro y dy ddy hy t ht`, and then applies `damped_solution_stability` with both operators equal to \(A_\mu\), both initial data equal to \(u_0(\mu),v_0(\mu)\), both cocoercivity constants equal to \(\alpha(\mu)\), and the uniform distance bound \(D=0\). The hypotheses required by `damped_solution_stability` are supplied as follows: positivity of \(\alpha(\mu)\) twice from `(hC₁ μ hμ).1`; cocoercivity twice from `(hC₁ μ hμ).2`; the nonnegativity \(0\le 0\) by `norm_num`; and the bound
\[
\|A_\mu u-A_\mu u\|\le 0
\]
by `fun u => by simp`, since the left-hand side is the norm of zero. The stability estimate therefore applies to the two solutions `hx` and `hy`.

Because the two operators, the two initial data, and the perturbation bound \(D\) are all identical or zero, the right-hand side of the stability estimate collapses to \(0\). The command `simpa using hbound` simplifies the resulting inequality to
\[
\|x(t)-y(t)\|\le 0.
\]
Together with `norm_nonneg _`, which gives \(0\le \|x(t)-y(t)\|\), the tactic `apply le_antisymm` proves
\[
\|x(t)-y(t)\|=0.
\]
Then `norm_eq_zero.mp` converts this into \(x(t)-y(t)=0\), and `sub_eq_zero.mp` converts that into \(x(t)=y(t)\). Since \(t\ge 0\) was arbitrary, this proves `Set.EqOn x y (Set.Ici 0)`, i.e. equality on \([0,\infty)\).

For the second conjunct, the proof introduces arbitrary \(\mu,\mu'\in V\). The command `dsimp only` unfolds the local `let` definitions of \(m_\mu\), \(m_{\mu'}\), and \(m\) in the goal so that the maximum of the two square roots is visible explicitly. It then uses `exists_damped_solution_of_cocoercive` twice, once for \(A_\mu\) and once for \(A_{\mu'}\), obtaining solution triples \(x,dx,ddx\) and \(x',dx',ddx'\).

The proof then defines
\[
D=\theta_1\|\mu-\mu'\|^{\theta_2}
\]
as the uniform bound between \(A_\mu\) and \(A_{\mu'}\). To show \(D\ge 0\), it unfolds \(D\), uses `hC₂.1.le` to get \(0\le \theta_1\), and uses `Real.rpow_nonneg (norm_nonneg _) _` to get
\[
0\le \|\mu-\mu'\|^{\theta_2}.
\]
Then `mul_nonneg` proves \(0\le D\). Next, the proof proves
\[
\|A_\mu u-A_{\mu'}u\|\le D
\]
for every \(u\in H\). This is exactly the Hölder-continuity hypothesis: the fourth conjunct of `hC₂` gives
\[
\|A_\mu u-A_{\mu'}u\|\le \theta_1\|\mu-\mu'\|^{\theta_2},
\]
and `simpa [D]` rewrites the right-hand side as \(D\).

The proof now supplies the two solution triples as witnesses and uses `apply Filter.Eventually.of_forall`. This reduces the almost-everywhere assertion
\[
\forall^{\mathrm{a.e.}} t,\; 0\le t\to \|x(t)-x'(t)\|\le\cdots
\]
to the stronger pointwise assertion for every real \(t\). After `intro t ht`, it applies `damped_solution_stability` with \(A=A_\mu\), \(B=A_{\mu'}\), initial data \(u_0(\mu),v_0(\mu)\) and \(u_0(\mu'),v_0(\mu')\), cocoercivity constants \(\alpha(\mu),\alpha(\mu')\), and the uniform bound \(D\). The hypotheses are supplied by the positivity and cocoercivity parts of `hC₁`, the nonnegativity `hD0`, the bound `hD`, and the two solution proofs `hx` and `hx'`.

The resulting stability estimate is
\[
\|x(t)-x'(t)\|
\le
e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+
\frac{D}{m}\bigl(e^{mt}-1\bigr),
\]
with the same \(m=\max(m_\mu,m_{\mu'})\). The command `dsimp only at hstable` unfolds the `let` definition of \(m\) inside this stability statement. Then `convert hstable using 1` aligns the estimate produced by `damped_solution_stability` with the exact right-hand side required by `thm_1`. The remaining difference is that `hstable` contains \(D\), whereas the target contains \(\theta_1\|\mu-\mu'\|^{\theta_2}\). After `dsimp [D]`, the tactic `ring` proves the required algebraic identity, using that
\[
D=\theta_1\|\mu-\mu'\|^{\theta_2}
\]
and commutativity/associativity of multiplication in \(\mathbb R\). Thus the stability inequality matches the conclusion of the theorem. Since \(t\ge 0\) was arbitrary, the pointwise estimate implies the stated almost-everywhere estimate. There is no use of `rw` or `linarith` in this proof; the arithmetic and algebraic simplifications are handled by `norm_num`, `simp`, `simpa`, `convert`, and `ring`.

