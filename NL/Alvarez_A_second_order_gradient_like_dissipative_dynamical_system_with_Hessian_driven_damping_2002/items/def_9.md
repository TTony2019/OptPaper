## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/def_9.lean`

## Lean statement
```lean
theorem rescaled_gDIN_iff_gradient_system
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hΦ : ContDiff ℝ 1 Φ)
    (x₀ z₀ : H) (x z : ℝ → H) :
    IsRescaledGDINTrajectory Φ β a b x₀ z₀ x z ↔
      IsGradientSystemTrajectory Φ β a b x₀ z₀ x z
```

## Statement explanation
The declaration is a theorem about two predicates on curves in a real Hilbert space $H$. The typeclass assumptions say that $H$ is a complete real inner product space, i.e. a real Hilbert space. The map $\Phi:H\to\mathbb R$ is the potential. The real parameters $\beta,a,b$ satisfy $a\gt 0$ and $b\gt 0$, while $\beta$ is unrestricted. The hypothesis $h\Phi$ says that $\Phi$ is $C^1$, i.e. continuously Fréchet differentiable to order one. The points $x_0,z_0\in H$ are initial data, and $x,z:\mathbb R\to H$ are two curves, thought of as time-dependent trajectories in $H$.

The conclusion is the equivalence

$$
\mathrm{IsRescaledGDINTrajectory}(\Phi,\beta,a,b,x_0,z_0,x,z)
\iff
\mathrm{IsGradientSystemTrajectory}(\Phi,\beta,a,b,x_0,z_0,x,z).
$$

The proof shows that `IsRescaledGDINTrajectory` consists of four pieces: a first scalar differential equation for $x$, a second scalar differential equation for $z$, and the initial conditions $x(0)=x_0$ and $z(0)=z_0$. The predicate `IsGradientSystemTrajectory` also has four pieces: first, for every time $t$, two differentiability assertions for the energy function denoted by `gradientSystemEnergy Φ β a b`; second, the pair form of the same two scalar differential equations; third and fourth, the same initial conditions.

The two energy differentiability assertions are precisely the ones supplied by the cited lemmas. For the first argument, the derivative of $v\mapsto \mathrm{gradientSystemEnergy}(\Phi,\beta,a,b,v,w)$ at $u$ is the continuous linear functional

```math
v \mapsto \bigl\langle \beta \nabla \Phi(u)+a u+\sqrt{ab}\,w,\; v\bigr\rangle .
```

For the second argument, the derivative of $v\mapsto \mathrm{gradientSystemEnergy}(\Phi,\beta,a,b,u,v)$ at $w$ is the continuous linear functional

```math
v \mapsto \bigl\langle \sqrt{ab}\,u+b w,\; v\bigr\rangle .
```

Thus the theorem says that, under $a\gt 0$, $b\gt 0$, and $C^1$ regularity of $\Phi$, the notion of a rescaled gDIN trajectory is exactly the same as the notion of a gradient-system trajectory. The only apparent extra condition on the gradient-system side is the differentiability of the energy; the theorem proves that this condition is automatic from $\Phi$ being $C^1$, while the differential equations agree coordinate by coordinate.

## Lean proof
```lean
by
  have hgradΦ : ∀ u, HasFDerivAt Φ (innerSL ℝ (gradient Φ u)) u := by
    intro u
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) u).hasGradientAt.hasFDerivAt)
  constructor
  · rintro ⟨hx, hz, hx₀, hz₀⟩
    refine ⟨?_, ?_, hx₀, hz₀⟩
    · intro t ht
      exact ⟨gradientSystemEnergy_hasFDerivAt_fst Φ β a b ha hb hgradΦ
          (x t) (z t),
        gradientSystemEnergy_hasFDerivAt_snd Φ β a b ha hb (x t) (z t)⟩
    · intro t ht
      apply Prod.ext
      · simpa [add_assoc] using hx t ht
      · simpa [add_assoc] using hz t ht
  · rintro ⟨_, hpair, hx₀, hz₀⟩
    refine ⟨?_, ?_, hx₀, hz₀⟩
    · intro t ht
      simpa [add_assoc] using congrArg Prod.fst (hpair t ht)
    · intro t ht
      simpa [add_assoc] using congrArg Prod.snd (hpair t ht)
```

## Proof explanation
The proof first constructs a Fréchet-derivative form of the gradient of $\Phi$. The `have hgradΦ` block proves

$$
\forall u,\quad \mathrm{HasFDerivAt}\ \Phi\ \bigl(\mathrm{innerSL}\mathbb R(\nabla\Phi(u))\bigr)\ u.
$$

Inside this block, `intro u` fixes an arbitrary point $u\in H$. The hypothesis $h\Phi:\mathrm{ContDiff}\mathbb R 1 \Phi$ implies that $\Phi$ is differentiable at $u$, because $1\neq 0$; the side condition is discharged by `by norm_num`. The resulting `HasGradientAt` statement says that the gradient of $\Phi$ at $u$ is $\nabla\Phi(u)$. The theorem `HasGradientAt.hasFDerivAt` converts this into the Fréchet derivative statement that the derivative is the continuous linear map $v\mapsto\langle \nabla\Phi(u),v\rangle$. The `simpa [innerSL]` step unfolds the definition of `innerSL`, putting the derivative into exactly the form required by the first energy lemma. This `hgradΦ` is the hypothesis passed to `gradientSystemEnergy_hasFDerivAt_fst`.

Next, `constructor` splits the iff into two implications.

For the forward implication, `rintro ⟨hx, hz, hx₀, hz₀⟩` decomposes a rescaled gDIN trajectory into its two scalar differential equations, named `hx` and `hz`, and its initial conditions `hx₀` and `hz₀`. Then `refine ⟨?_, ?_, hx₀, hz₀⟩` begins to build a gradient-system trajectory; the initial conditions are reused unchanged.

The first remaining goal is the energy differentiability component. For a fixed time $t$ with domain membership `ht`, the proof uses the pair

```math
\bigl\langle
\text{gradientSystemEnergy\_hasFDerivAt\_fst}\ \Phi\ \beta\ a\ b\ ha\ hb\ hgrad\Phi\ (x t)\ (z t),
\;
\text{gradientSystemEnergy\_hasFDerivAt\_snd}\ \Phi\ \beta\ a\ b\ ha\ hb\ (x t)\ (z t)
\bigr\rangle .
```

The first cited lemma, applied with $u=x(t)$ and $w=z(t)$, uses $a\gt 0$, $b\gt 0$, and the previously established `hgradΦ`. It concludes that the function

$$
v\mapsto \mathrm{gradientSystemEnergy}(\Phi,\beta,a,b,v,z(t))
$$

has Fréchet derivative at $x(t)$ equal to

```math
v\mapsto \bigl\langle \beta\nabla\Phi(x(t))+a x(t)+\sqrt{ab}\,z(t),\; v\bigr\rangle .
```

The second cited lemma, applied with the same $u=x(t)$ and $w=z(t)$, concludes that the function

$$
v\mapsto \mathrm{gradientSystemEnergy}(\Phi,\beta,a,b,x(t),v)
$$

has Fréchet derivative at $z(t)$ equal to

```math
v\mapsto \bigl\langle \sqrt{ab}\,x(t)+b z(t),\; v\bigr\rangle .
```

Together these two facts are exactly the two partial differentiability assertions required by `IsGradientSystemTrajectory`.

The second remaining goal in the forward direction is the pair differential equation. Again `intro t ht` fixes a time. The command `apply Prod.ext` reduces the equality of two pairs to equality of their first and second coordinates. The first coordinate is proved by `simpa [add_assoc] using hx t ht`, and the second by `simpa [add_assoc] using hz t ht`. Thus the two scalar equations of the rescaled gDIN trajectory are precisely the two coordinates of the gradient-system pair equation, up to associativity of addition. This completes the forward implication.

For the reverse implication, `rintro ⟨_, hpair, hx₀, hz₀⟩` decomposes a gradient-system trajectory. The first component, the energy differentiability, is discarded because it is not needed to reconstruct the rescaled trajectory. The pair differential equation `hpair` and the initial conditions are kept. Then `refine ⟨?_, ?_, hx₀, hz₀⟩` begins to build a rescaled gDIN trajectory.

For the first scalar equation, the proof fixes $t$ and `ht`. The fact `hpair t ht` is an equality of pairs. Applying `congrArg Prod.fst` to both sides extracts the equality of the first coordinates. The `simpa [add_assoc]` step normalizes associativity of addition so that the extracted equality matches the first scalar equation expected by `IsRescaledGDINTrajectory`. For the second scalar equation, the same argument is repeated with `congrArg Prod.snd`, extracting the equality of the second coordinates, and `simpa [add_assoc]` matches the second scalar equation. The initial conditions are reused directly. This completes the reverse implication and hence the equivalence.

