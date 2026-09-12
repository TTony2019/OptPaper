## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/prop_4.lean`

## Lean statement
```lean
theorem din_equiv_gradient_system
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H)
    (hΦ : ContDiff ℝ 2 Φ) (hx : ContDiff ℝ 2 x)
    (hαpos : 0 < α) (hβpos : 0 < β) (hαβ : 1 < α * β) :
    IsDINTrajectory H Φ α β x ↔
      ∃ z : ℝ → H,
        ContDiffOn ℝ 2 z (Set.Ici 0) ∧
        IsRescaledGDINTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (z 0) x z ∧
        IsGradientSystemTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (z 0) x z
```

## Statement explanation
The declaration is a theorem about a complete real inner product space $H$. It fixes a potential $\Phi:H\to\mathbb R$, real parameters $\alpha,\beta$, and a curve $x:\mathbb R\to H$. The hypotheses are that $\Phi$ is twice continuously differentiable, $x$ is twice continuously differentiable, $\alpha>0$, $\beta>0$, and $1<\alpha\beta$. The conclusion is an equivalence between the statement that $x$ is a DIN trajectory for $\Phi,\alpha,\beta$ and the existence of an auxiliary curve $z:\mathbb R\to H$ satisfying two additional properties.

Write

$$
a=\alpha-\frac1\beta,\qquad b=\frac1\beta.
$$

The hypothesis $1<\alpha\beta$, together with $\beta>0$, implies $a>0$; indeed $1/\beta<\alpha$. Also $b>0$ because $\beta>0$. These are the choices of $a,b$ used throughout the theorem.

The predicate `IsRescaledGDINTrajectory Φ β a b x₀ z₀ x z` is defined explicitly. It says that for all $t\ge 0$,

$$
x'(t)+\beta\nabla\Phi(x(t))+a x(t)+\sqrt{ab}\,z(t)=0,
$$

and

$$
z'(t)+\sqrt{ab}\,x(t)+b z(t)=0,
$$

together with the initial conditions

$$
x(0)=x_0,\qquad z(0)=z_0.
$$

Here $x'$ and $z'$ are the derivatives of the curves, and $\nabla\Phi$ is the gradient of $\Phi$.

The predicate `IsGradientSystemTrajectory Φ β a b x₀ z₀ x z` is not unfolded in the supplied source. The cited theorem `rescaled_gDIN_iff_gradient_system` states that, under $a>0$, $b>0$, and $\Phi$ being $C^1$, this gradient-system predicate is equivalent to the rescaled gDIN trajectory predicate just described with the same parameters and initial data.

Thus the theorem says: $x$ is a DIN trajectory for $\Phi,\alpha,\beta$ if and only if there exists a curve $z$, twice continuously differentiable on $[0,\infty)$, such that the pair $(x,z)$, with initial data $(x(0),z(0))$, is both a rescaled gDIN trajectory with parameters

$$
\beta,\qquad a=\alpha-\frac1\beta,\qquad b=\frac1\beta
$$

and a gradient-system trajectory with those same parameters. The proof combines three equivalences: the equivalence between DIN trajectories and solutions of the gDIN system, the equivalence between gDIN solutions and rescaled gDIN trajectories, and the equivalence between rescaled gDIN trajectories and gradient-system trajectories.

## Lean proof
```lean
by
  have ha : 0 < α - 1 / β := by
    apply sub_pos.mpr
    exact (div_lt_iff₀ hβpos).2 (by simpa using hαβ)
  have hb : 0 < 1 / β := one_div_pos.mpr hβpos
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hβne : β ≠ 0 := ne_of_gt hβpos
  constructor
  · intro hDIN
    rcases hDIN with ⟨hα, hβ, hEq⟩
    let y₀ : H :=
      -(β • deriv x 0 + (β ^ 2) • gradient Φ (x 0) +
        (β * (α - 1 / β)) • x 0)
    obtain ⟨y, hyC2, hsol⟩ :=
      (din_iff_gdin Φ α β (α - 1 / β) (1 / β) x (x 0) y₀
        hΦ hx hα hβ rfl rfl rfl (by rfl)).mp ⟨hα, hβ, hEq⟩
    let z : ℝ → H := fun t => Real.sqrt ((1 / β) / (α - 1 / β)) • y t
    have hR0 :=
      (isSolution_gDIN_iff_rescaled_gDIN Φ β (α - 1 / β) (1 / β) ha hb
        (x 0) y₀ x y).mp hsol
    have hR :
        IsRescaledGDINTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (z 0) x z := by
      simpa [z, hsol.2.2.2]
        using hR0
    have hzC2 : ContDiffOn ℝ 2 z (Set.Ici 0) := by
      dsimp [z]
      exact hyC2.const_smul _
    have hG :=
      (rescaled_gDIN_iff_gradient_system Φ β (α - 1 / β) (1 / β)
        ha hb hΦ1 (x 0) (z 0) x z).mp hR
    exact ⟨z, hzC2, hR, hG⟩
  · rintro ⟨z, hzC2, hR, _hG⟩
    let y : ℝ → H := fun t => Real.sqrt ((α - 1 / β) / (1 / β)) • z t
    let y₀ : H := y 0
    have hcd :
        Real.sqrt ((1 / β) / (α - 1 / β)) *
            Real.sqrt ((α - 1 / β) / (1 / β)) = 1 := by
      exact sqrt_b_div_a_mul_sqrt_a_div_b (α - 1 / β) (1 / β) ha hb
    have hzy : (fun t => Real.sqrt ((1 / β) / (α - 1 / β)) • y t) = z := by
      funext t
      dsimp [y]
      rw [smul_smul, hcd, one_smul]
    have hzy0 :
        Real.sqrt ((1 / β) / (α - 1 / β)) • y₀ = z 0 := by
      dsimp [y₀]
      exact congrFun hzy 0
    have hR' :
        IsRescaledGDINTrajectory Φ β (α - 1 / β) (1 / β)
          (x 0) (Real.sqrt ((1 / β) / (α - 1 / β)) • y₀) x
          (fun t => Real.sqrt ((1 / β) / (α - 1 / β)) • y t) := by
      rw [hzy, hzy0]
      exact hR
    have hsol :=
      (isSolution_gDIN_iff_rescaled_gDIN Φ β (α - 1 / β) (1 / β) ha hb
        (x 0) y₀ x y).mpr hR'
    have hyC2 : ContDiffOn ℝ 2 y (Set.Ici 0) := by
      dsimp [y]
      exact hzC2.const_smul _
    have hy₀ : y₀ =
        -(β • deriv x 0 + (β ^ 2) • gradient Φ (x 0) +
          (β * (α - 1 / β)) • x 0) := by
      have hfirst := hsol.1 0 le_rfl
      have hscaled := congrArg (fun q : H => β • q) hfirst
      apply eq_neg_iff_add_eq_zero.mpr
      simp only [smul_add, smul_smul, smul_zero] at hscaled
      rw [show β * (1 / β) = 1 by field_simp [hβne]] at hscaled
      dsimp [y₀]
      simpa [pow_two, add_assoc, add_comm, add_left_comm, mul_comm] using hscaled
    exact
      (din_iff_gdin Φ α β (α - 1 / β) (1 / β) x (x 0) y₀
        hΦ hx hαpos hβpos rfl rfl rfl hy₀).mpr ⟨y, hyC2, hsol⟩
```

## Proof explanation
The proof begins by establishing the positivity of the two auxiliary parameters. First, it proves

$$
0<\alpha-\frac1\beta.
$$

The tactic `apply sub_pos.mpr` reduces this to the inequality

$$
\frac1\beta<\alpha.
$$

Because $\beta>0$, the lemma `div_lt_iff₀` says that

$$
\frac1\beta<\alpha \quad\Longleftrightarrow\quad 1<\alpha\beta.
$$

The hypothesis $1<\alpha\beta$ is therefore exactly what is needed, and `simpa` supplies it in the required form. Next, the proof proves

$$
0<\frac1\beta
$$

using `one_div_pos.mpr hβpos`, which is the standard fact that the reciprocal of a positive real number is positive. It also records that $\Phi$ is $C^1$, since $C^2$ implies $C^1$; this is done by `hΦ.of_le` with `norm_num` verifying $1\le 2$. Finally it notes $\beta\ne0$, which follows from $\beta>0$.

The proof then splits the equivalence with `constructor`.

For the forward direction, assume `hDIN`, i.e. that $x$ is a DIN trajectory. The proof destructs this predicate as

$$
\langle h_\alpha,h_\beta,h_{\mathrm{Eq}}\rangle,
$$

where $h_\alpha$ is $0<\alpha$, $h_\beta$ is $0<\beta$, and $h_{\mathrm{Eq}}$ is the differential equation or condition carried by the DIN trajectory predicate. It then defines the vector

$$
y_0
=
-\bigl(\beta x'(0)+\beta^2\nabla\Phi(x(0))+\beta a x(0)\bigr),
$$

with $a=\alpha-1/\beta$. This is exactly the initial datum required by the cited theorem `din_iff_gdin`.

The theorem `din_iff_gdin` states, for the present parameters $a=\alpha-1/\beta$ and $b=1/\beta$, that under the $C^2$ hypotheses on $\Phi$ and $x$, the positivity of $\alpha,\beta$, the identities $a=\alpha-1/\beta$, $b=1/\beta$, and $x(0)=x_0$, and the above formula for $y_0$, the assertion that $x$ is a DIN trajectory is equivalent to the existence of a curve $y:\mathbb R\to H$ that is twice continuously differentiable on $[0,\infty)$ and satisfies the gDIN solution predicate

$$
\operatorname{IsSolution\_gDIN}\Phi\beta a b x_0 y_0 x y.
$$

Applying the forward implication `.mp` of this equivalence with $x_0=x(0)$, $a=\alpha-1/\beta$, $b=1/\beta$, and the displayed $y_0$, the proof obtains such a curve $y$, its $C^2$-regularity `hyC2`, and the gDIN solution `hsol`.

Next the proof defines

$$
z(t)=\sqrt{\frac{b}{a}}\,y(t)
=
\sqrt{\frac{1/\beta}{\alpha-1/\beta}}\,y(t).
$$

It applies the cited theorem `isSolution_gDIN_iff_rescaled_gDIN` in the forward direction to `hsol`. That theorem says that for positive $a,b$, being a gDIN solution is equivalent to being a rescaled gDIN trajectory after scaling the auxiliary curve by $\sqrt{b/a}$. Concretely, it gives

$$
\operatorname{IsRescaledGDINTrajectory}
\Phi\beta a b x(0) \bigl(\sqrt{b/a}\,y_0\bigr) x
\bigl(t\mapsto \sqrt{b/a}\,y(t)\bigr).
$$

Using the definition of $z$ and the initial condition component of `hsol`, which identifies $y(0)$ with $y_0$, the proof rewrites this into

$$
\operatorname{IsRescaledGDINTrajectory}
\Phi\beta a b x(0) (z(0)) x z.
$$

This is `hR`.

The regularity of $z$ is obtained by `hyC2.const_smul`, because multiplying a $C^2$ function on $[0,\infty)$ by a constant scalar preserves $C^2$-regularity. Thus $z$ is twice continuously differentiable on $[0,\infty)$.

The proof then applies `rescaled_gDIN_iff_gradient_system` in the forward direction. This theorem states that, under $a>0$, $b>0$, and $\Phi$ being $C^1$, the rescaled gDIN trajectory predicate is equivalent to the gradient-system trajectory predicate with the same data. Since the proof has already established $a>0$, $b>0$, and $\Phi$ is $C^1$, it obtains

$$
\operatorname{IsGradientSystemTrajectory}
\Phi\beta a b x(0) z(0) x z.
$$

Combining this with $z$'s $C^2$-regularity and the rescaled trajectory property `hR`, the forward direction is complete.

For the backward direction, assume

$$
\exists z,\quad z \text{ is } C^2 \text{ on } [0,\infty),\quad
\operatorname{IsRescaledGDINTrajectory}\Phi\beta a b x(0) z(0) x z,
$$

and also a gradient-system trajectory condition, which is not used. The proof introduces such a $z$, its regularity `hzC2`, and the rescaled trajectory property `hR`.

It now defines the inverse scaling

$$
y(t)=\sqrt{\frac{a}{b}}\,z(t)
=
\sqrt{\frac{\alpha-1/\beta}{1/\beta}}\,z(t).
$$

Set $y_0=y(0)$. The scaling factors are inverse to each other. The cited lemma `sqrt_b_div_a_mul_sqrt_a_div_b` states that for positive $a,b$,

$$
\sqrt{\frac b a}\,\sqrt{\frac a b}=1.
$$

Here this is applied with $a=\alpha-1/\beta$ and $b=1/\beta$. The proof uses `funext` to prove the pointwise function identity

$$
\bigl(t\mapsto \sqrt{b/a}\,y(t)\bigr)=z.
$$

Indeed, unfolding $y$ reduces the left side to

$$
\sqrt{b/a}\,\sqrt{a/b}\,z(t),
$$

and the lemma gives $1\cdot z(t)=z(t)$. Evaluating at $0$ gives

$$
\sqrt{b/a}\,y_0=z(0).
$$

Therefore the rescaled trajectory property `hR` for $z$ can be rewritten as a rescaled trajectory property for the scaled curve $t\mapsto \sqrt{b/a}\,y(t)$ and initial datum $\sqrt{b/a}\,y_0$.

Now the proof applies the reverse direction `.mpr` of `isSolution_gDIN_iff_rescaled_gDIN`. Since the scaled curve and scaled initial datum satisfy the rescaled gDIN trajectory predicate, the theorem yields

$$
\operatorname{IsSolution\_gDIN}\Phi\beta a b x(0) y_0 x y.
$$

The regularity of $y$ follows from `hzC2.const_smul`, since $y$ is a constant scalar multiple of $z$.

It remains to verify the initial-value formula required by `din_iff_gdin`. The proof uses the first component of the gDIN solution `hsol`, evaluated at time $0$. This gives the first gDIN differential equation at $t=0$. Multiplying that equation by $\beta$ and simplifying scalar multiplications, in particular using

$$
\beta\cdot\frac1\beta=1,
$$

which follows from $\beta\ne0$ by `field_simp`, yields an identity equivalent to

$$
y_0
=
-\bigl(\beta x'(0)+\beta^2\nabla\Phi(x(0))+\beta a x(0)\bigr).
$$

The tactic `eq_neg_iff_add_eq_zero.mpr` is used to turn the goal $y_0=-V$ into the equivalent equation $y_0+V=0$, and `simpa` with associativity, commutativity, and `pow_two` rearranges the terms to match the multiplied differential equation.

Finally, the proof applies the reverse direction `.mpr` of `din_iff_gdin`. The hypotheses are $\Phi$ and $x$ being $C^2$, $\alpha>0$, $\beta>0$, the definitional identities $a=\alpha-1/\beta$, $b=1/\beta$, the initial condition $x(0)=x(0)$, the formula for $y_0$, and the existence of the $C^2$ curve $y$ satisfying the gDIN solution predicate. The conclusion is precisely

$$
\operatorname{IsDINTrajectory} H \Phi \alpha \beta x,
$$

which completes the equivalence.

