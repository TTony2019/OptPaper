## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/def_2.lean`

## Lean statement
```lean
def IsDrygradTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (r : ℝ) (f : H → ℝ) (z : ℝ → H) (t₀ : ℝ) : Prop :=
  ∀ t ∈ Set.Ici t₀, ∃ u : H,
    u ∈ ERealFunction.subdifferential
      (dryFrictionPotential (H := H) r) (deriv z t) ∧
        deriv z t + u + gradient f (z t) = 0
```

## Statement explanation
The declaration defines a predicate `IsDrygradTrajectory` on a real Hilbert space $H$. The ambient assumptions are that $H$ is a normed additive commutative group, an inner product space over $\mathbb R$, and complete, so $H$ is a real Hilbert space. The parameters are a real number $r$, a function $f:H\to\mathbb R$, a trajectory $z:\mathbb R\to H$, and an initial time $t_0\in\mathbb R$.

The predicate

$$
\mathrm{IsDrygradTrajectory}(r,f,z,t_0)
$$

holds exactly when, for every time $t$ in the right-closed interval $[t_0,\infty)$, there exists a vector $u\in H$ such that

$$
u\in \partial \varphi_r(\dot z(t))
$$

and

$$
\dot z(t)+u+\nabla f(z(t))=0.
$$

Here $\dot z(t)$ is the Lean term `deriv z t`, the time derivative of $z$ at $t$, and $\nabla f(z(t))$ is the Lean term `gradient f (z t)`, the gradient of $f$ at the point $z(t)$. The symbol $\partial \varphi_r$ denotes the subdifferential of the dry-friction potential `dryFrictionPotential (H := H) r`; its exact formula is not part of this declaration. The condition only states membership in that subdifferential set at the velocity $\dot z(t)$.

Equivalently, the equation says that the particular vector

$$
u=-\dot z(t)-\nabla f(z(t))
$$

must belong to the subdifferential of the dry-friction potential at $\dot z(t)$. Thus the definition says that for every $t\ge t_0$, the differential inclusion

$$
0\in \dot z(t)+\partial \varphi_r(\dot z(t))+\nabla f(z(t))
$$

is satisfied at time $t$. The chosen $u$ may depend on $t$. No convexity, differentiability, or regularity condition on $f$ or $z$ is explicitly added by this declaration beyond the conditions appearing in the formula itself.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so its body is the defining proposition itself rather than a theorem to be proved. Consequently, there are no cited lemmas, no theorem applications, and no proof tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain. The logical content is entirely contained in the definition: a universal quantifier over $t\in[t_0,\infty)$, an existential quantifier over $u\in H$, a subdifferential membership condition, and a vector equation. To unfold the definition for a concrete trajectory would mean replacing the name `IsDrygradTrajectory` by exactly that proposition; the provided source does not perform any such unfolding or verification.

