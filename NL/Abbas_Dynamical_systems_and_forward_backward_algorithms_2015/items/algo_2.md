## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/algo_2.lean`

## Lean statement
```lean
theorem backward_forward_unit_step {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (alg : BackwardForwardDiscretization f hf B mu 1) :
    ∀ k, alg.x (k + 1) =
      ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.x k - mu • B (alg.x k))
```

## Statement explanation
The theorem concerns a complete real inner-product space $H$, that is, a real Hilbert space. The function $f$ is extended-real-valued: in Lean it has codomain `Set.Ioi (⊥ : EReal)`, the subtype of extended reals strictly larger than the bottom element $-\infty$, so $f(x)$ is never $-\infty$, though it may be finite or $+\infty$. The hypothesis $hf$ states that $f$ belongs to `ERealFunction.gammaZero H`, written $\Gamma_0(H)$ in the cited definition of the scaled proximity operator; this is the membership condition under which the scaled proximity operator is defined. The map $B : H \to H$ is the forward operator, and $\mu \in \mathbb{R}$ is the step size. The object `alg` is a `BackwardForwardDiscretization f hf B mu 1`, i.e. a backward-forward discretization with final parameter $1$. It supplies the sequences $x_k$ and $y_k$, the recurrence relations used below, and in particular the proof $0<\mu$ stored as `alg.mu_pos`; the theorem does not list $0<\mu$ separately, because it is part of `alg`.

The conclusion is that for every index $k$,

$$
x_{k+1}
=
\mathrm{Prox}_{\mu f}\bigl(x_k-\mu B(x_k)\bigr),
$$

where $\mathrm{Prox}_{\mu f}$ denotes `scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩`. The cited definition says this is the proximity operator of the pointwise scaled function $\gamma f$, where the positive real $\gamma$ is represented by the value $\mu$ together with the proof `alg.mu_pos`. The auxiliary facts in that definition, `smul_mem_gammaZero` and `hasUniqueProxPoint_of_mem_gammaZero`, ensure that positive scaling preserves membership in $\Gamma_0(H)$ and that the scaled function has a unique proximity point. Thus the theorem says that for the unit parameter choice, the next iterate is obtained by first taking the forward step $x_k \mapsto x_k-\mu B(x_k)$ and then applying the proximal map of $\mu f$, i.e. the standard proximal-gradient/backward-forward update.

## Lean proof
```lean
by
  intro k
  calc
    alg.x (k + 1) = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.y (k + 1)) := alg.prox_step (k + 1)
    _ = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        ((1 - (1 : ℝ)) • alg.y k + (1 : ℝ) • (alg.x k - mu • B (alg.x k))) := by
      rw [alg.equation_step]
    _ = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.x k - mu • B (alg.x k)) := by simp
```

## Proof explanation
The proof begins with `intro k`, which fixes an arbitrary index $k$ and reduces the goal to proving the identity for that fixed $k$. The proof is then a `calc` block, i.e. a chain of equalities using transitivity.

First,

$$
x_{k+1}
=
\mathrm{Prox}_{\mu f}\bigl(y_{k+1}\bigr)
$$

by `alg.prox_step (k+1)`. The field `alg.prox_step` is the proximal/backward step of the discretization: for every index $n$, it states

$$
x_{n+1}
=
\mathrm{Prox}_{\mu f}\bigl(y_{n+1}\bigr).
$$

Specializing to $n=k+1$ gives the first equality. Mathematically, this says that the new $x$-iterate is obtained by applying the proximal map of $\mu f$ to the current $y$-iterate.

Second, the proof rewrites this expression using `alg.equation_step`. In the present unit-parameter specialization, that recurrence gives

$$
y_{k+1}
=
(1-1)\cdot y_k+1\cdot \bigl(x_k-\mu B(x_k)\bigr).
$$

The `rw [alg.equation_step]` tactic performs exactly this replacement inside the argument of the fixed function $\mathrm{Prox}_{\mu f}$. Therefore the middle line of the `calc` block is

$$
\mathrm{Prox}_{\mu f}\left((1-1)\cdot y_k+1\cdot \bigl(x_k-\mu B(x_k)\bigr)\right).
$$

The equality with the previous line is simply the fact that applying the same function to equal arguments gives equal values.

Finally, `simp` simplifies the argument:

$$
(1-1)\cdot y_k+1\cdot \bigl(x_k-\mu B(x_k)\bigr)
=
0\cdot y_k+\bigl(x_k-\mu B(x_k)\bigr)
=
0+\bigl(x_k-\mu B(x_k)\bigr)
=
x_k-\mu B(x_k).
$$

These simplifications use elementary real arithmetic and the vector-space laws for scalar multiplication, such as $1\cdot z=z$ and $0\cdot y=0$. Hence the last line of the `calc` block is

$$
\mathrm{Prox}_{\mu f}\bigl(x_k-\mu B(x_k)\bigr),
$$

which is exactly the desired conclusion. The proof does not use any further minimization property of the proximity operator beyond the fact that it is a function, nor does it explicitly invoke the completeness of $H$; completeness is part of the ambient Hilbert-space setting. No separate `exact` or `linarith` step occurs; the final equality is closed by simplification.

