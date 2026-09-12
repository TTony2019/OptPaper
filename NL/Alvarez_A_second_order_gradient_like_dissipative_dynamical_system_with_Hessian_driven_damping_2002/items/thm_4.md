## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_4.lean`

## Lean statement
```lean
theorem din_iff_gdin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (Φ : H → ℝ) (α β a b : ℝ) (x : ℝ → H)
  (x₀ y₀ : H)
  (hΦ : ContDiff ℝ 2 Φ)
  (hx : ContDiff ℝ 2 x)
  (hαpos : 0 < α) (hβpos : 0 < β)
  (ha : a = α - 1 / β) (hb : b = 1 / β)
  (hx₀ : x 0 = x₀)
  (hy₀ : y₀ = -(β • deriv x 0 + (β ^ 2) • gradient Φ (x 0) + (β * a) • x 0)) :
  (IsDINTrajectory H Φ α β x) ↔
  ∃ y : ℝ → H, (ContDiffOn ℝ 2 y (Set.Ici 0)) ∧ IsSolution_gDIN Φ β a b x₀ y₀ x y
```

## Statement explanation
The theorem is stated in a complete real inner product space $H$, that is, a real Hilbert space. The data are a function $\Phi:H\to \mathbb R$, real parameters $\alpha,\beta,a,b$, a curve $x:\mathbb R\to H$, and two initial vectors $x_0,y_0\in H$.

The main smoothness assumptions are that

$$
\Phi \text{ is } C^2
\qquad\text{and}\qquad
x \text{ is } C^2.
$$

The parameter assumptions are

$$
\alpha>0,\qquad \beta>0,\qquad a=\alpha-\frac1\beta,\qquad b=\frac1\beta.
$$

The initial condition on $x$ is

$$
x(0)=x_0,
$$

and the initial value $y_0$ is required to satisfy

```math
y_0
=-\Bigl(\beta\,\dot x(0)+\beta^2\,\nabla\Phi(x_0)+\beta a\,x_0\Bigr).
```

Here $\nabla\Phi$ is the gradient of $\Phi$, and $\dot x(0)=\mathrm{deriv}x(0)$.

The left-hand predicate $\mathrm{IsDINTrajectory}_H(\Phi,\alpha,\beta,x)$ is not defined in the cited declarations, but the proof treats it as a triple whose first two components are the positivity assumptions $\alpha\gt 0$, $\beta\gt 0$, and whose third component is the second-order equation on $t\ge 0$,

```math
\ddot x(t)+\alpha \dot x(t)
+\beta\,\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
+\nabla\Phi(x(t))=0 .
```

Here $D(\nabla\Phi)(x(t))$ is the Fréchet derivative of $\nabla\Phi$ at $x(t)$, applied to the velocity $\dot x(t)$. This is the Hessian-driven damping term.

The right-hand side says that there exists a curve $y:\mathbb R\to H$ which is $C^2$ on $[0,\infty)$ and which, together with $x$, satisfies the generalized damped inertial system

```math
\mathrm{IsSolution\_gDIN}(\Phi,\beta,a,b,x_0,y_0,x,y).
```

According to its definition, this means the following four conditions. For every $t\ge 0$,

```math
\dot x(t)+\beta\,\nabla\Phi(x(t))+a\,x(t)+b\,y(t)=0,
```

and

```math
\dot y(t)+a\,x(t)+b\,y(t)=0.
```

Also

$$
x(0)=x_0,\qquad y(0)=y_0.
$$

Thus the theorem asserts that the second-order Hessian-damped trajectory $x$ with parameters $\alpha,\beta$ is equivalent to the existence of an auxiliary curve $y$ solving the first-order gDIN system with parameters $\beta,a,b$, where the parameters are related by $a=\alpha-1/\beta$ and $b=1/\beta$, and where the initial value $y_0$ is exactly the value obtained from the formula

```math
y(t)=-\Bigl(\beta\,\dot x(t)+\beta^2\,\nabla\Phi(x(t))+\beta a\,x(t)\Bigr)
```

at $t=0$.

## Lean proof
```lean
by
  have hβ : β ≠ 0 := ne_of_gt hβpos
  have hba : β * a = β * α - 1 := by
    rw [ha]
    field_simp [hβ]
  have hab : a + b = α := by
    rw [ha, hb]
    ring
  have hbβ : b * β = 1 := by
    rw [hb]
    field_simp [hβ]
  have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by simpa using hΦ)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgradDeriv : ∀ z, HasFDerivAt (gradient Φ)
      (fderiv ℝ (gradient Φ) z) z := by
    intro z
    exact (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  have hxDeriv : ∀ t, HasDerivAt x (deriv x t) t := by
    intro t
    exact (hx.differentiable (by norm_num) t).hasDerivAt
  have hvDeriv : ∀ t, HasDerivAt (deriv x) (deriv (deriv x) t) t := by
    intro t
    exact (hx.differentiable_deriv_two t).hasDerivAt
  have hvC1 : ContDiff ℝ 1 (deriv x) := by
    exact (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) x by simpa using hx)).2.2
  have hgradCompC1 : ContDiff ℝ 1 (fun t => gradient Φ (x t)) := by
    simpa [Function.comp_def] using
      hgradC1.comp (hx.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  constructor
  · rintro ⟨_, _, hEq⟩
    let y : ℝ → H := fun t =>
      -(β • deriv x t + (β ^ 2) • gradient Φ (x t) + (β * a) • x t)
    let dy : ℝ → H := fun t => deriv x t + β • gradient Φ (x t)
    have hgradx : ∀ t, HasDerivAt (fun s => gradient Φ (x s))
        ((fderiv ℝ (gradient Φ) (x t)) (deriv x t)) t := by
      intro t
      simpa [Function.comp_def] using
        (hgradDeriv (x t)).comp_hasDerivAt t (hxDeriv t)
    have hfirst : ∀ t, 0 ≤ t →
        deriv x t + β • gradient Φ (x t) + a • x t + b • y t = 0 := by
      intro t ht
      dsimp [y]
      rw [hb]
      simp only [smul_neg, smul_add, smul_smul]
      rw [show (1 / β) * β = 1 by field_simp [hβ],
        show (1 / β) * β ^ 2 = β by field_simp [hβ],
        show (1 / β) * (β * a) = a by field_simp [hβ]]
      module
    have hdy : ∀ t, 0 ≤ t → HasDerivAt y (dy t) t := by
      intro t ht
      have hyraw : HasDerivAt y
          (-(β • deriv (deriv x) t + (β ^ 2) •
            (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            (β * a) • deriv x t)) t := by
        dsimp [y]
        have hsum := ((hvDeriv t).const_smul β).add
          ((hgradx t).const_smul (β ^ 2))
        have hsum' := hsum.add ((hxDeriv t).const_smul (β * a))
        exact hsum'.neg
      have hacc : deriv (deriv x) t =
          -(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            gradient Φ (x t)) := by
        exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hEq t ht)
      convert hyraw using 1
      rw [hacc]
      dsimp [dy]
      simp only [smul_neg, smul_add, smul_smul]
      rw [hba]
      module
    have hdyC1 : ContDiff ℝ 1 dy := by
      dsimp [dy]
      exact hvC1.add (hgradCompC1.const_smul β)
    have hyC2 : ContDiffOn ℝ 2 y (Set.Ici 0) :=
      contDiffOn_two_of_hasDerivAt_of_contDiffOn_one (uniqueDiffOn_Ici 0) hdy
        hdyC1.contDiffOn
    refine ⟨y, hyC2, ?_⟩
    dsimp [IsSolution_gDIN]
    refine ⟨hfirst, ?_, hx₀, ?_⟩
    · intro t ht
      rw [(hdy t ht).deriv]
      simpa [dy] using hfirst t ht
    · simpa [y] using hy₀.symm
  · rintro ⟨y, hyC2, hgDIN⟩
    rcases hgDIN with ⟨hfirst, hsecond, hx0, hy0⟩
    refine ⟨hαpos, hβpos, ?_⟩
    have hDIN_pos : ∀ t, 0 < t →
        deriv (deriv x) t + α • deriv x t +
          β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            gradient Φ (x t) = 0 := by
      intro t ht
      have hdyEq : deriv y t = deriv x t + β • gradient Φ (x t) := by
        have hsub : deriv x t + β • gradient Φ (x t) - deriv y t = 0 := by
          calc
            deriv x t + β • gradient Φ (x t) - deriv y t =
                (deriv x t + β • gradient Φ (x t) + a • x t + b • y t) -
                  (deriv y t + a • x t + b • y t) := by module
            _ = 0 := by rw [hfirst t ht.le, hsecond t ht.le]; module
        exact (sub_eq_zero.mp hsub).symm
      have hgradx : HasDerivAt (fun s => gradient Φ (x s))
          ((fderiv ℝ (gradient Φ) (x t)) (deriv x t)) t := by
        simpa [Function.comp_def] using
          (hgradDeriv (x t)).comp_hasDerivAt t (hxDeriv t)
      have hyAt : HasDerivAt y (deriv y t) t := by
        exact (hyC2.differentiableOn (by norm_num)).hasDerivAt (Ici_mem_nhds ht)
      have hR : HasDerivAt (fun s =>
          -(β • gradient Φ (x s) + a • x s + b • y s))
          (-(β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            a • deriv x t + b • deriv y t)) t := by
        exact (((hgradx.const_smul β).add ((hxDeriv t).const_smul a)).add
          (hyAt.const_smul b)).neg
      have hxEq : (fun s => deriv x s) =ᶠ[𝓝 t] (fun s =>
          -(β • gradient Φ (x s) + a • x s + b • y s)) := by
        filter_upwards [Ici_mem_nhds ht] with s hs
        exact eq_neg_iff_add_eq_zero.mpr
          (by simpa [add_assoc] using hfirst s hs)
      have hvraw : HasDerivAt (deriv x)
          (-(β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            a • deriv x t + b • deriv y t)) t :=
        hR.congr_of_eventuallyEq hxEq
      have hsecondDeriv := hvraw.deriv
      rw [hsecondDeriv, hdyEq]
      simp only [smul_add, smul_smul]
      rw [← hab, add_smul, hbβ, one_smul]
      module
    let res : ℝ → H := fun t =>
      deriv (deriv x) t + α • deriv x t +
        β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t)
    have hresCont : Continuous res := by
      have hclm : Continuous (fun t =>
          (fderiv ℝ (gradient Φ) (x t)) (deriv x t)) := by
        exact (hgradC1.continuous_fderiv one_ne_zero).comp hx.continuous |>.clm_apply
          (hx.continuous_deriv (by norm_num))
      dsimp [res]
      have hc1 := (hvC1.continuous_deriv_one).add
        ((hx.continuous_deriv (by norm_num)).const_smul α)
      have hc2 := hc1.add (hclm.const_smul β)
      have hc3 := hc2.add hgradCompC1.continuous
      simpa only [Pi.add_apply] using hc3
    have hresOn : Set.EqOn res (fun _ => (0 : H)) (Set.Ioi 0) := by
      intro t ht
      exact hDIN_pos t ht
    have hresClosure := hresOn.closure hresCont continuous_const
    have hzero : res 0 = 0 := by
      have h := hresClosure (show (0 : ℝ) ∈ closure (Set.Ioi 0) by
        rw [closure_Ioi]
        exact Set.self_mem_Ici)
      exact h
    intro t ht
    by_cases ht0 : t = 0
    · simpa [res, ht0] using hzero
    · exact hDIN_pos t (lt_of_le_of_ne ht (Ne.symm ht0))
```

## Proof explanation
The proof begins by recording several scalar consequences of $\beta\gt 0$. Since $\beta\neq 0$, division by $\beta$ is legitimate. The proof establishes

$$
\beta a=\beta\alpha-1,
\qquad
a+b=\alpha,
\qquad
b\beta=1.
$$

The first identity is obtained from $a=\alpha-1/\beta$ by multiplying by $\beta$ and using $\beta\neq 0$. The second follows by substituting $a=\alpha-1/\beta$ and $b=1/\beta$. The third follows from $b=1/\beta$. These identities are used later to cancel coefficients in the vector equations. The tactics `rw`, `field_simp`, and `ring` perform these scalar simplifications.

Next the proof proves smoothness facts. From $\Phi$ being $C^2$, it obtains that the Fréchet derivative of $\Phi$ is $C^1$. The gradient $\nabla\Phi$ is obtained by composing that derivative with the inverse Riesz isomorphism from $H^*$ to $H$, so $\nabla\Phi$ is also $C^1$. This is recorded as `hgradC1`. Consequently, $\nabla\Phi$ is differentiable everywhere, and its Fréchet derivative at $z$ is $D(\nabla\Phi)(z)$, giving `hgradDeriv`. Similarly, since $x$ is $C^2$, it has a derivative at every $t$,

$$
x'(t)=\dot x(t),
$$

and the derivative function $\dot x$ is itself differentiable, with derivative

$$
(\dot x)'(t)=\ddot x(t).
$$

Also $\dot x$ is $C^1$, and the composite

$$
t\mapsto \nabla\Phi(x(t))
$$

is $C^1$. These facts are `hxDeriv`, `hvDeriv`, `hvC1`, and `hgradCompC1`.

For the forward implication, assume $\mathrm{IsDINTrajectory}_H(\Phi,\alpha,\beta,x)$. The proof destructs this predicate into a triple and keeps the third component, `hEq`, which is the second-order equation

```math
\ddot x(t)+\alpha\dot x(t)
+\beta\,\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
+\nabla\Phi(x(t))=0
```

for $t\ge 0$.

The proof defines the candidate auxiliary curve

```math
y(t)
=-\Bigl(\beta\,\dot x(t)+\beta^2\,\nabla\Phi(x(t))+\beta a\,x(t)\Bigr),
```

and also defines

```math
dy(t)=\dot x(t)+\beta\,\nabla\Phi(x(t)).
```

The goal is to show that this $y$ is $C^2$ on $[0,\infty)$ and satisfies $`\mathrm{IsSolution\_gDIN}`$.

First, using the chain rule, the proof computes the derivative of $t\mapsto \nabla\Phi(x(t))$:

$$
\frac{d}{dt}\nabla\Phi(x(t))
=\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t).
$$

This is `hgradx`.

Then the proof verifies the first gDIN equation:

$$
\dot x(t)+\beta\nabla\Phi(x(t))+a x(t)+b y(t)=0.
$$

Substituting the definition of $y$, and using $b=1/\beta$, gives

$$
b y(t)
=\frac1\beta y(t)
=-\Bigl(\dot x(t)+\beta\nabla\Phi(x(t))+a x(t)\Bigr).
$$

Therefore the sum is zero. The tactics `dsimp`, `rw`, `simp`, and `module` perform this cancellation.

Next the proof computes the derivative of $y$. Differentiating the definition of $y$ gives, before simplification,

```math
\dot y(t)
=-\Bigl(\beta\ddot x(t)
+\beta^2\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
+\beta a\,\dot x(t)\Bigr).
```

The second-order equation `hEq` says

$$
\ddot x(t)
=-\Bigl(\alpha\dot x(t)
+\beta\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
+\nabla\Phi(x(t))\Bigr).
$$

Substituting this into the expression for $\dot y(t)$, and using $\beta a=\beta\alpha-1$, the terms cancel and one obtains

$$
\dot y(t)=\dot x(t)+\beta\nabla\Phi(x(t))=dy(t).
$$

Thus $y$ has derivative $dy$ on $t\ge 0$. This is `hdy`.

Since $dy$ is the sum of $\dot x$ and $\beta\nabla\Phi(x(t))$, and both are $C^1$, the function $dy$ is $C^1$. The proof now applies the cited theorem `contDiffOn_two_of_hasDerivAt_of_contDiffOn_one`. Its statement says that if $s\subseteq\mathbb R$ is a unique differentiability set, if $f$ has derivative $f'$ at every point of $s$, and if $f'$ is $C^1$ on $s$, then $f$ is $C^2$ on $s$. Here $s=[0,\infty)$, which is a unique differentiability set, $f=y$, and $f'=dy$. The proof has already shown that $y$ has derivative $dy$ at every $t\ge 0$, and that $dy$ is $C^1$. Therefore

$$
y \text{ is } C^2 \text{ on } [0,\infty).
$$

This is `hyC2`.

Now the proof assembles the gDIN solution. The first equation was verified as `hfirst`. For the second equation, at $t\ge 0$, we have $\dot y(t)=dy(t)=\dot x(t)+\beta\nabla\Phi(x(t))$, so the first equation gives

$$
\dot y(t)+a x(t)+b y(t)=0.
$$

The initial condition $x(0)=x_0$ is exactly `hx₀`. For $y(0)$, the definition of $y$ and the hypothesis on $y_0$ give

$$
y(0)=y_0.
$$

Thus the forward direction produces the required $y$.

For the reverse implication, assume there exists a curve $y$ which is $C^2$ on $[0,\infty)$ and satisfies $`\mathrm{IsSolution\_gDIN}`$. The proof extracts the two differential equations, the initial conditions, and then must prove$\mathrm{IsDINTrajectory}_H(\Phi,\alpha,\beta,x)$. It constructs this predicate using the already available hypotheses$\alpha>0$and$\beta>0$, and it remains to prove the second-order equation.

For $t\gt 0$, the proof first derives

$$
\dot y(t)=\dot x(t)+\beta\nabla\Phi(x(t)).
$$

Indeed, subtracting the second gDIN equation from the first gives

$$
\dot x(t)+\beta\nabla\Phi(x(t))-\dot y(t)=0.
$$

This is `hdyEq`.

The proof then differentiates the first gDIN equation. More precisely, it considers the function

$$
t\mapsto -\Bigl(\beta\nabla\Phi(x(t))+a x(t)+b y(t)\Bigr).
$$

Because the first gDIN equation says

$$
\dot x(t)=-\Bigl(\beta\nabla\Phi(x(t))+a x(t)+b y(t)\Bigr),
$$

and because this equality holds eventually near $t$ when $t\gt 0$, the derivative of $\dot x$ at $t$ equals the derivative of that negative expression. This uses `HasDerivAt.congr_of_eventuallyEq`. The resulting derivative is

$$
\ddot x(t)
=-\Bigl(\beta\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
+a\dot x(t)+b\dot y(t)\Bigr).
$$

Now substitute $\dot y(t)=\dot x(t)+\beta\nabla\Phi(x(t))$. The right-hand side becomes

$$
-\Bigl(\beta D(\nabla\Phi)(x(t))\dot x(t)
+a\dot x(t)
+b\dot x(t)
+b\beta\nabla\Phi(x(t))\Bigr).
$$

Using $a+b=\alpha$ and $b\beta=1$, this simplifies to

$$
-\Bigl(\beta D(\nabla\Phi)(x(t))\dot x(t)
+\alpha\dot x(t)
+\nabla\Phi(x(t))\Bigr).
$$

Therefore

$$
\ddot x(t)+\alpha\dot x(t)
+\beta D(\nabla\Phi)(x(t))\dot x(t)
+\nabla\Phi(x(t))=0
$$

for every $t\gt 0$. This is `hDIN_pos`.

It remains to extend this equation to $t=0$. The proof defines

$$
\mathrm{res}(t)
=\ddot x(t)+\alpha\dot x(t)
+\beta\bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
+\nabla\Phi(x(t)).
$$

It proves $\mathrm{res}$ is continuous. The term $t\mapsto \ddot x(t)$ is continuous because $\dot x$ is $C^1$. The term $t\mapsto \alpha\dot x(t)$ is continuous because $x$ is $C^2$. The term

$$
t\mapsto \bigl(D(\nabla\Phi)(x(t))\bigr)\dot x(t)
$$

is continuous because $D(\nabla\Phi)$ is continuous, $x$ is continuous, and $\dot x$ is continuous. Finally $t\mapsto \nabla\Phi(x(t))$ is continuous. Hence the sum is continuous.

The proof already knows that $\mathrm{res}(t)=0$ for all $t\gt 0$. Since $\mathrm{res}$ is continuous and agrees with the zero function on $(0,\infty)$, it agrees with zero on the closure of $(0,\infty)$, which is $[0,\infty)$. In particular,

$$
\mathrm{res}(0)=0.
$$

Thus the second-order equation holds at $t=0$ as well.

Finally, for an arbitrary $t\ge 0$, the proof splits into the cases $t=0$ and $t\neq 0$. If $t=0$, it uses $\mathrm{res}(0)=0$. If $t\neq 0$, then $t\gt 0$, and the already proved `hDIN_pos` gives the equation. Therefore $x$ satisfies the full second-order equation for all $t\ge 0$, completing the reverse implication and hence the equivalence.

The proof does not use `linarith`; scalar arithmetic is handled by `field_simp` and `ring`, while vector-space linear algebra is handled by `module`.

