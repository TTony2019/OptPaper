## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/cor_3.lean`

## Lean statement
```lean
theorem cor_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M)
    (A : M → SetValuedOperator H H) (hA : ∀ μ ∈ V, (A μ).IsMaximalMonotone)
    (J : M → H → H) (γ lam θ₁ θ₂ : ℝ) (x dx ddx : M → ℝ → H)
    (u₀ v₀ : M → H)
    (hlam : 0 < lam) (hθ₁ : 0 < θ₁) (hθ₂_pos : 0 < θ₂) (hθ₂_le : θ₂ ≤ 1)
    (hJ : ∀ μ ∈ V, ∀ x_ : H,
      J μ x_ ∈ SetValuedOperator.resolvent (lam • A μ) x_)
    (h15 : ∀ (lam' : ℝ) (_ : 0 < lam'),
      ∀ (J' : M → H → H), (∀ μ ∈ V, ∀ x_ : H,
        J' μ x_ ∈ SetValuedOperator.resolvent (lam' • A μ) x_) →
      ∀ u : H, ∀ μ ∈ V, ∀ μ' ∈ V, ‖J' μ u - J' μ' u‖ ≤ lam' * θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hsol : ∀ μ ∈ V, ext_def_2 (fun u : H => lam⁻¹ • (u - J μ u)) γ
      (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ)) :
    let m
```

## Statement explanation
The declaration `cor_3` states a stability and uniqueness result for a parametrized family of second-order evolution problems. The ambient space $H$ is a complete real inner product space, and $M$ is a normed additive commutative group. The set $V\subseteq M$ is the set of admissible parameters.

For each $\mu\in M$, $A_\mu$ is a set-valued operator on $H$. The hypothesis `hA` says that for every $\mu\in V$, $A_\mu$ is maximal monotone. The map $J$ chooses, for each $\mu$, a point $J_\mu(x)$ in the resolvent of $\lambda A_\mu$ at $x$. Concretely, `hJ` says that for every $\mu\in V$ and every $x\in H$,

$$
J_\mu(x)\in \operatorname{resolvent}(\lambda A_\mu)(x).
$$

Thus $J_\mu$ is a selected resolvent map for the operator $\lambda A_\mu$.

The real parameters satisfy $\lambda>0$, $\theta_1>0$, $0<\theta_2\le 1$, and $\gamma$ is used by the solution predicate `ext_def_2`. The functions

$$
x,dx,ddx : M\to(\mathbb R\to H),\qquad u_0,v_0:M\to H
$$

represent, for each parameter $\mu$, a candidate trajectory $x_\mu$, its first and second derivatives, and initial data $u_0(\mu),v_0(\mu)$.

The hypothesis `h15` is a uniform Hölder-continuity assumption on resolvent selections. For every $\lambda'>0$, every selection $J'$ of the resolvent of $\lambda'A_\mu$, every $u\in H$, and every $\mu,\mu'\in V$,

$$
\|J'_\mu(u)-J'_{\mu'}(u)\|
\le \lambda'\theta_1\|\mu-\mu'\|^{\theta_2}.
$$

The hypothesis `hsol` says that for every $\mu\in V$, the triple

$$
(x_\mu,dx_\mu,ddx_\mu)
$$

satisfies `ext_def_2` for the single-valued map

$$
B_\mu(u)=\lambda^{-1}(u-J_\mu(u)),
$$

with parameter $\gamma$ and initial data $u_0(\mu),v_0(\mu)$. The provided definition of `ext_def_2` is

$$
\text{`ext\_def\_2`}(A,\gamma,u_0,v_0,x,dx,ddx)
\iff
0<\gamma \ \wedge\ \text{`def\_3`}(A,\gamma,u_0,v_0,x,dx,ddx).
$$

The internal predicate `def_3` is not provided, so its exact differential equation or inclusion is not expanded here. The proof treats `ext_def_2` as the solution predicate for the relevant evolution problem.

The conclusion is as follows. Define

$$
m=\sqrt{1+2\gamma^2+\frac{2}{\lambda^2}}.
$$

Then:

1. For every $\mu\in V$, there exist functions $x_\mu,dx_\mu,ddx_\mu:\mathbb R\to H$ satisfying `ext_def_2` for $B_\mu$, $\gamma$, $u_0(\mu)$, and $v_0(\mu)$, and any other such triple is equal to this one on $[0,\infty)$. In other words, the problem has a solution, and that solution is unique on the nonnegative half-line.

2. For every $\mu,\mu'\in V$, for almost every $t$ with respect to Lebesgue measure, if $0\le t$, then

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le
e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+
\frac{\theta_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\theta_2}.
$$

Here $x_\mu$ and $x_{\mu'}$ are the given functions from the hypotheses, not the existential functions from part 1. The uniqueness statement in part 1 is what allows the comparison bound from the auxiliary theorem to be transferred to the given solutions.

If $V$ is empty, both universal statements over $\mu\in V$ are vacuously true.

## Lean proof
```lean
Real.sqrt (1 + 2 * γ ^ 2 + 2 / (lam ^ 2))
    (∀ μ ∈ V, ∃ x_μ dx_μ ddx_μ : ℝ → H,
      ext_def_2 (fun u : H => lam⁻¹ • (u - J μ u)) γ
          (u₀ μ) (v₀ μ) x_μ dx_μ ddx_μ ∧
        ∀ y dy ddy : ℝ → H,
          ext_def_2 (fun u : H => lam⁻¹ • (u - J μ u)) γ
              (u₀ μ) (v₀ μ) y dy ddy →
            Set.EqOn x_μ y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      ‖x μ t - x μ' t‖ ≤ Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂) := by
  dsimp
  by_cases hV : V.Nonempty
  · rcases hV with ⟨μ₀, hμ₀⟩
    have hγ : 0 < γ := (hsol μ₀ hμ₀).1
    let B : M → H → H := fun μ u => lam⁻¹ • (u - J μ u)
    have hC1 : ∀ μ ∈ V, 0 < lam ∧ ∀ u v : H,
        lam * ‖B μ u - B μ v‖ ^ 2 ≤ inner ℝ (B μ u - B μ v) (u - v) := by
      intro μ hμ
      refine ⟨hlam, ?_⟩
      intro u v
      have hu := (SetValuedOperator.mem_resolvent_smul_iff (A μ) lam u (J μ u)).mp
        (hJ μ hμ u)
      have hv := (SetValuedOperator.mem_resolvent_smul_iff (A μ) lam v (J μ v)).mp
        (hJ μ hμ v)
      rcases hu with ⟨a, ha, hua⟩
      rcases hv with ⟨b, hb, hvb⟩
      have hmono : 0 ≤ inner ℝ (a - b) (J μ u - J μ v) :=
        (hA μ hμ).1 a ha b hb
      have hua' : u - J μ u = lam • a := by
        calc
          u - J μ u = (J μ u + lam • a) - J μ u :=
            (congrArg (fun z => z - J μ u) hua).symm
          _ = lam • a := by module
      have hvb' : v - J μ v = lam • b := by
        calc
          v - J μ v = (J μ v + lam • b) - J μ v :=
            (congrArg (fun z => z - J μ v) hvb).symm
          _ = lam • b := by module
      have hBdiff : B μ u - B μ v = a - b := by
        dsimp [B]
        rw [hua', hvb']
        rw [smul_smul, smul_smul]
        simp [inv_mul_cancel₀ (ne_of_gt hlam)]
      have huv : u - v = (J μ u - J μ v) + lam • (a - b) := by
        calc
          u - v = (J μ u + lam • a) - (J μ v + lam • b) := by rw [hua, hvb]
          _ = (J μ u - J μ v) + lam • (a - b) := by module
      rw [hBdiff, huv, inner_add_right, inner_smul_right]
      have hnorm : ‖a - b‖ ^ 2 = inner ℝ (a - b) (a - b) := by simp
      rw [hnorm]
      nlinarith
    have hC2 : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V →
        ‖B μ u - B μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂ := by
      refine ⟨hθ₁, hθ₂_pos, hθ₂_le, ?_⟩
      intro u μ μ' hμ hμ'
      have h15lam := h15 lam hlam J hJ u μ hμ μ' hμ'
      have hdiff : B μ u - B μ' u = lam⁻¹ • (J μ' u - J μ u) := by
        dsimp [B]
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), norm_sub_rev]
      rw [show lam⁻¹ * ‖J μ u - J μ' u‖ = ‖J μ u - J μ' u‖ / lam by ring]
      exact (div_le_iff₀ hlam).mpr (by simpa [mul_assoc, mul_left_comm, mul_comm] using h15lam)
    rcases thm_1 V B γ u₀ v₀ (fun _ : M => lam) θ₁ θ₂ hγ hC1 hC2 with
      ⟨hunique, hcomparison⟩
    constructor
    · simpa [B] using hunique
    · intro μ hμ μ' hμ'
      rcases hcomparison μ hμ μ' hμ' with ⟨y, y', hysol, hy'sol, hybound⟩
      rcases hysol with ⟨dy, ddy, hysol⟩
      rcases hy'sol with ⟨dy', ddy', hy'sol⟩
      obtain ⟨z, dz, ddz, hzsol, hzuniq⟩ := hunique μ hμ
      have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
        (hzuniq (x μ) (dx μ) (ddx μ) (by simpa [B] using hsol μ hμ) ht).symm.trans
          (hzuniq y dy ddy (by simpa [B] using hysol) ht)
      obtain ⟨z', dz', ddz', hz'sol, hz'uniq⟩ := hunique μ' hμ'
      have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
        (hz'uniq (x μ') (dx μ') (ddx μ') (by simpa [B] using hsol μ' hμ') ht).symm.trans
          (hz'uniq y' dy' ddy' (by simpa [B] using hy'sol) ht)
      filter_upwards [hybound] with t ht
      intro ht_nonneg
      have ht_bound := ht ht_nonneg
      rw [← hxy ht_nonneg, ← hxy' ht_nonneg] at ht_bound
      simpa only [max_self] using ht_bound
  · constructor
    · intro μ hμ
      exact (hV ⟨μ, hμ⟩).elim
    · intro μ hμ
      exact (hV ⟨μ, hμ⟩).elim
```

## Proof explanation
The proof first applies `dsimp`, which unfolds the `let`-binding for

$$
m=\sqrt{1+2\gamma^2+2/\lambda^2}
$$

and reduces the goal to the explicit two-conjunct statement.

Then the proof performs a case split with `by_cases hV : V.Nonempty`.

### Case 1: $V$ is nonempty

The proof chooses a parameter $\mu_0\in V$. From `hsol μ₀ hμ₀` and the definition of `ext_def_2`, whose first conjunct is $0<\gamma$, it obtains

$$
h\gamma : 0<\gamma.
$$

This is needed later for the auxiliary theorem `thm_1`.

The proof then defines the single-valued map

$$
B_\mu(u)=\lambda^{-1}(u-J_\mu(u)).
$$

This is the resolvent-type or Yosida-type approximation associated to $A_\mu$.

#### Verification of the coercivity hypothesis `hC1`

The proof establishes

$$
\forall \mu\in V,\quad
0<\lambda
\ \wedge\
\forall u,v\in H,\quad
\lambda\|B_\mu(u)-B_\mu(v)\|^2
\le
\langle B_\mu(u)-B_\mu(v),\,u-v\rangle.
$$

This is the coercivity/monotonicity condition needed by `thm_1`.

Fix $\mu\in V$ and $u,v\in H$. From `hJ`, we know

$$
J_\mu(u)\in \operatorname{resolvent}(\lambda A_\mu)(u),
\qquad
J_\mu(v)\in \operatorname{resolvent}(\lambda A_\mu)(v).
$$

The cited theorem `mem_resolvent_smul_iff` says, specialized to this situation, that

$$
J_\mu(u)\in \operatorname{resolvent}(\lambda A_\mu)(u)
\iff
u\in (A_\mu).\text{identityAddScaled}(\lambda)(J_\mu(u)).
$$

Unpacking the right-hand side as the proof does gives the existence of

$$
a\in A_\mu(J_\mu(u))
$$

such that

$$
u=J_\mu(u)+\lambda a.
$$

Similarly, for $v$, there exists

$$
b\in A_\mu(J_\mu(v))
$$

such that

$$
v=J_\mu(v)+\lambda b.
$$

Because $A_\mu$ is maximal monotone, in particular monotone, its first component gives the inequality

$$
0\le \langle a-b,\,J_\mu(u)-J_\mu(v)\rangle.
$$

This is the monotonicity inequality for the original set-valued operator $A_\mu$. The proof uses only this monotonicity part of `hA`.

Next, the proof computes algebraically that

$$
u-J_\mu(u)=\lambda a,
\qquad
v-J_\mu(v)=\lambda b.
$$

Therefore

$$
B_\mu(u)-B_\mu(v)=a-b.
$$

It also computes

$$
u-v=(J_\mu(u)-J_\mu(v))+\lambda(a-b).
$$

Using linearity of the inner product in the second variable, the proof expands

$$
\langle B_\mu(u)-B_\mu(v),\,u-v\rangle
=
\langle a-b,\,(J_\mu(u)-J_\mu(v))+\lambda(a-b)\rangle
$$

as

$$
\langle a-b,J_\mu(u)-J_\mu(v)\rangle
+
\lambda\langle a-b,a-b\rangle.
$$

By monotonicity, the first term is nonnegative. Since

$$
\|a-b\|^2=\langle a-b,a-b\rangle,
$$

and since $B_\mu(u)-B_\mu(v)=a-b$, we obtain

$$
\lambda\|B_\mu(u)-B_\mu(v)\|^2
\le
\langle B_\mu(u)-B_\mu(v),\,u-v\rangle.
$$

This proves `hC1`. The tactic `nlinarith` closes the resulting real inequality after the inner-product and norm identities have been rewritten.

#### Verification of the Hölder-continuity hypothesis `hC2`

The proof next establishes

$$
0<\theta_1,\qquad 0<\theta_2,\qquad \theta_2\le 1,
$$

and

$$
\forall u\in H,\ \forall \mu,\mu'\in V,\quad
\|B_\mu(u)-B_{\mu'}(u)\|
\le
\theta_1\|\mu-\mu'\|^{\theta_2}.
$$

The first three inequalities are exactly the assumptions `hθ₁`, `hθ₂_pos`, and `hθ₂_le`.

For the continuity estimate, fix $u\in H$ and $\mu,\mu'\in V$. The proof instantiates `h15` with $\lambda'=\lambda$ and $J'=J$. Since `hJ` says that $J$ is a resolvent selection for $\lambda A_\mu$, this instance gives

$$
\|J_\mu(u)-J_{\mu'}(u)\|
\le
\lambda\theta_1\|\mu-\mu'\|^{\theta_2}.
$$

Now the proof computes

$$
B_\mu(u)-B_{\mu'}(u)
=
\lambda^{-1}(u-J_\mu(u))
-
\lambda^{-1}(u-J_{\mu'}(u))
=
\lambda^{-1}(J_{\mu'}(u)-J_\mu(u)).
$$

Taking norms and using $\lambda>0$, so that $|\lambda^{-1}|=\lambda^{-1}$, gives

$$
\|B_\mu(u)-B_{\mu'}(u)\|
=
\lambda^{-1}\|J_{\mu'}(u)-J_\mu(u)\|.
$$

The lemma `norm_sub_rev` changes the order inside the norm to $\|J_\mu(u)-J_{\mu'}(u)\|$. Thus

$$
\|B_\mu(u)-B_{\mu'}(u)\|
\le
\lambda^{-1}\cdot \lambda\theta_1\|\mu-\mu'\|^{\theta_2}
=
\theta_1\|\mu-\mu'\|^{\theta_2}.
$$

This proves `hC2`.

#### Application of `thm_1`

The proof now applies the cited theorem `thm_1` to the family $B$, the same set $V$, the initial data $u_0,v_0$, the constant function

$$
\alpha(\mu)=\lambda,
$$

and the parameters $\gamma,\theta_1,\theta_2$.

The theorem `thm_1` has the following content. If $0<\gamma$, if for every $\mu\in V$ the map $A_\mu$ satisfies the coercivity condition

$$
\alpha(\mu)\|A_\mu(u)-A_\mu(v)\|^2
\le
\langle A_\mu(u)-A_\mu(v),u-v\rangle,
$$

and if the family $A_\mu$ is Hölder continuous in $\mu$ with exponent $\theta_2$ and constant $\theta_1$, then:

1. For each $\mu\in V$, there exists a triple $(x,dx,ddx)$ satisfying `ext_def_2` for $A_\mu,\gamma,u_0(\mu),v_0(\mu)$, and any other such triple agrees with it on $[0,\infty)$.

2. For each $\mu,\mu'\in V$, with

$$
m_\mu=\sqrt{1+2\gamma^2+\frac{2}{(\alpha(\mu))^2}},
\qquad
m_{\mu'}=\sqrt{1+2\gamma^2+\frac{2}{(\alpha(\mu'))^2}},
$$

and

$$
m=\max(m_\mu,m_{\mu'}),
$$

there exist solutions $y$ for $\mu$ and $y'$ for $\mu'$ such that, for almost every $t$, if $0\le t$, then

$$
\|y(t)-y'(t)\|
\le
e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+
\frac{\theta_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\theta_2}.
$$

The hypotheses `hγ`, `hC1`, and `hC2` are exactly what `thm_1` requires for $B$. Since $\alpha(\mu)=\lambda$ is constant, both $m_\mu$ and $m_{\mu'}$ are equal to

$$
m=\sqrt{1+2\gamma^2+\frac{2}{\lambda^2}}.
$$

Thus the maximum $\max(m_\mu,m_{\mu'})$ is simply $m$.

Let `hunique` and `hcomparison` be the two parts of the conclusion of `thm_1`.

#### First conclusion: existence and uniqueness

The first conjunct of the target is obtained by

$$
\text{`simpa [B] using hunique`}.
$$

This unfolds the local definition of $B$ so that the existence-and-uniqueness statement from `thm_1` matches the target statement, which uses the explicit expression

$$
u\mapsto \lambda^{-1}(u-J_\mu(u)).
$$

#### Second conclusion: comparison of the given solutions

The proof now fixes $\mu,\mu'\in V$. From `hcomparison μ hμ μ' hμ'`, it obtains functions $y,y'$, together with proofs that $y$ and $y'$ solve the `ext_def_2` problems for $B_\mu$ and $B_{\mu'}$, respectively, and an almost-everywhere bound for $\|y(t)-y'(t)\|$.

However, the desired conclusion concerns the given functions $x_\mu$ and $x_{\mu'}$. To transfer the bound, the proof uses uniqueness.

From `hunique μ hμ`, the proof obtains a solution $z$ for the $\mu$-problem such that every other solution equals $z$ on $[0,\infty)$. Since `hsol μ hμ` shows that the given $x_\mu$ is a solution, and since $y$ is also a solution, both $x_\mu$ and $y$ equal $z$ on $[0,\infty)$. Therefore

$$
x_\mu(t)=y(t)
$$

for all $t\ge 0$. The proof obtains this by composing the equality $x_\mu=z$ with $z=y$ using `Set.EqOn` symmetry and transitivity.

The same argument for $\mu'$ gives

$$
x_{\mu'}(t)=y'(t)
$$

for all $t\ge 0$.

Now `hybound` is an almost-everywhere statement. The tactic `filter_upwards [hybound]` keeps the same almost-everywhere set and reduces the goal to a pointwise statement at a generic $t$ lying in that set. For such a $t$, assuming $0\le t$, the bound for $y,y'$ holds. Using the equalities

$$
x_\mu(t)=y(t),\qquad x_{\mu'}(t)=y'(t)
$$

on $[0,\infty)$, the proof rewrites the bound from $y,y'$ into a bound for $x_\mu,x_{\mu'}$.

Finally, the bound from `thm_1` contains the maximum

$$
\max(m_\mu,m_{\mu'}).
$$

But $m_\mu=m_{\mu'}=m$, so `max_self` simplifies $\max(m,m)=m$. This is the last step

$$
\text{`simpa only [max\_self] using ht\_bound`}.
$$

Thus the desired almost-everywhere comparison estimate for the given solutions is obtained.

### Case 2: $V$ is empty

If $V$ is empty, then both target conjuncts are universal statements over $\mu\in V$. The proof splits the conjunction with `constructor`. In each branch, after introducing an arbitrary $\mu\in V$, the hypothesis that $V$ is empty contradicts $\mu\in V$. The tactic

$$
\text{`exact (hV ⟨μ,hμ⟩).elim`}
$$

closes the goal from this contradiction. Hence both statements are vacuously true.

