## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/def_1.lean`

## Lean statement
```lean
theorem DF_r.toEReal_mem_gammaZero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {phi : H → ℝ} {r : ℝ} (h : DF_r phi r) : phi.toEReal ∈ Γ₀(H)
```

## Statement explanation
The declaration is a theorem about a real-valued function $\phi$ on a real inner product space $H$. The type variable $H$ carries the hypotheses `[NormedAddCommGroup H]` and `[InnerProductSpace ℝ H]`, so $H$ is a real inner product space with its associated norm topology; no completeness hypothesis is present. The function $\phi : H \to \mathbb{R}$ is real-valued, and $r : \mathbb{R}$ is a real parameter. The hypothesis $`h : \text{DF\_r}\ \phi\ r`$says that$\phi$ satisfies the `DF_r` condition with parameter $r$. The conclusion is that the canonical extension $\phi^{\mathrm{EReal}} : H \to \overline{\mathbb{R}}$, defined by $x \mapsto (\phi(x) : \overline{\mathbb{R}})$, belongs to $\Gamma_0(H)$. In the standard notation of convex analysis, $\Gamma_0(H)$ is the class of proper, convex, lower semicontinuous functions $H \to \overline{\mathbb{R}}$. Concretely, membership in $\Gamma_0(H)$ means that the extended-real function is proper, satisfies the usual convexity inequality, and is lower semicontinuous, equivalently has closed sublevel sets. Since $\phi$ is real-valued, its extension $\phi^{\mathrm{EReal}}$ is finite everywhere, so properness is automatic; the substantive content is that the dry-friction hypothesis forces convexity and lower semicontinuity. The parameter $r$ does not appear in the conclusion, and no positivity or sign condition on $r$ is assumed. The internal definitions of `DF_r` and `DryFriction` are not shown in the snippet; the proof uses only that `DF_r` projects to the weaker base dry-friction hypothesis and that this base hypothesis entails $\Gamma_0$-membership.

## Lean proof
```lean
h.toDryFriction.toEReal_mem_gammaZero
```

## Proof explanation
The proof is a single term, not a tactic proof. It is the expression `h.toDryFriction.toEReal_mem_gammaZero`; none of `intro`, `rw`, `simp`, `exact`, or `linarith` occurs. The term is evaluated as a composition of a projection and an application of a previously available fact. First, from the hypothesis $`h : \text{DF\_r}\ \phi\ r`$, the projection `h.toDryFriction` extracts the weaker assertion that $\phi$ satisfies the base `DryFriction` condition. Mathematically, this is the step of forgetting the extra $r$-parameterized dry-friction structure and keeping only the underlying dry-friction property. Second, the result `toEReal_mem_gammaZero` associated with `DryFriction` is applied to that extracted evidence. The exact consequence visible here is that a proof of `DryFriction phi` yields a proof of $\phi^{\mathrm{EReal}} \in \Gamma_0(H)$. Specialized to the current $\phi$, it says that if $\phi$ has the base dry-friction property, then its extended-real version is a proper convex lower semicontinuous function on $H$. This is precisely the goal. Therefore the composed term `h.toDryFriction.toEReal_mem_gammaZero` has the required type and proves the theorem. No additional assumptions, rewrites, or arithmetic reasoning are involved.

