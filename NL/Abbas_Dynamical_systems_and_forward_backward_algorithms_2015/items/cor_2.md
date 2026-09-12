## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/cor_2.lean`

## Lean statement
```lean
theorem bounded_inf_compact_strong_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x v : ℝ → H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hlam : 0 < lam) (hmu : 0 < mu)
    (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)))
    (hinfcompact : ∀ r a : ℝ,
      IsCompact (Metric.closedBall (Classical.choose hS) r ∩
        {y | (Phi y : EReal) ≤ (a : EReal)})) :
    ∃ z ∈ S, Tendsto x atTop (nhds z)
```

## Statement explanation
The theorem `bounded_inf_compact_strong_convergence` is a strong-convergence result for a continuous-time forward-backward dynamical system in a real Hilbert space $H$. It assumes that a trajectory $x$ has a weak limit point in a set $S$ of solutions, and that the extended-real function $\Phi$ has compact sublevel intersections with closed balls; under the remaining dynamical, regularity, cocoercivity, and domain hypotheses, it concludes that the same weak limit is actually a strong limit.

The variables and hypotheses are as follows. $H$ is a complete real inner-product space, hence a real Hilbert space. The function $\Phi:H\to \mathrm{EReal}$ is extended-real valued; more precisely, its Lean codomain is the subtype of extended reals strictly greater than $\bot$, the bottom element, so its values are not $-\infty$. The hypothesis `hPhi` says $\Phi$ belongs to the class `ERealFunction.gammaZero H`; the supplied context does not expand the definition of that class, so its visible role is as a structural assumption required by the earlier result `proposition_2_16`. The map $B:H\to H$ is a single-valued operator, and `hB` says that $B$ is cocoercive on all of $H$ with constant $\beta\gt 0$. The set $S\subseteq H$ is nonempty. The maps $x,v:\mathbb R\to H$ are the primal and dual trajectories. The real parameters satisfy

$$
\lambda>0,\qquad \mu>0,\qquad \mu\lambda=1,\qquad \beta>0.
$$

The regularity hypotheses say that $x$ and $v$ are absolutely continuous on every interval $[0,b]$ with $b\gt 0$, that for every $T\gt 0$ the derivatives of $x$ and $v$ exist almost everywhere on $[0,T]$ with the stated values, and that $v$ and the derivative of $x$ are square-integrable on every $[0,b]$. The subgradient condition is

$$
v(t)\in\partial\Phi(x(t))\quad\text{for all }t\ge 0.
$$

The dynamical equation holds almost everywhere on $[0,\infty)$:

$$
v(t)\in\partial\Phi(x(t)),\qquad
\lambda \dot{x}(t)+\dot{v}(t)+v(t)+B(x(t))=0.
$$

The set $S$ consists of solutions in the subgradient sense:

$$
w\in S\implies -Bw\in\partial\Phi(w),
$$

equivalently $0\in Bw+\partial\Phi(w)$. The domain hypothesis says that $x(t)\in\mathrm{dom}\Phi$ for all $t\ge0$, and that every $w\in S$ lies in $\mathrm{dom}\Phi$. The weak-convergence hypothesis says that there exists $x_\infty\in S$ such that $x(t)$ converges weakly to $x_\infty$ as $t\to\infty$. Finally, `hinfcompact` says that for every radius $r$ and every real level $a$, the set

```math
\overline{B}(z_0,r)\cap\{y\in H:\Phi(y)\le a\}
```

is compact, where $z_0$ is the element of $S$ selected by `Classical.choose hS`. This is a bounded inf-compactness condition on $\Phi$.

The conclusion is that there exists $z\in S$ such that $x(t)\to z$ strongly as $t\to\infty$. In fact the proof obtains the strong limit $x_\infty$ supplied by the weak-convergence hypothesis.

## Lean proof
```lean
by
  let z0 : H := Classical.choose hS
  have hz0 : z0 ∈ S := Classical.choose_spec hS
  obtain ⟨_, _, xinf, hxinfS, hxweak, hvalue⟩ :=
    proposition_2_16 S Phi hPhi B x v z0 lam mu beta hS hz0 hlam hmu hmu_lam hbeta
      hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2 horbit hsolution hdom hweak
  obtain ⟨C, hC⟩ := cor218_eventually_norm_le_of_tendsto_weakly hxweak
  let a : ℝ := (Phi xinf : EReal).toReal + 1
  let R : ℝ := C + ‖z0‖
  let K : Set H := Metric.closedBall z0 R ∩ {y | (Phi y : EReal) ≤ (a : EReal)}
  have hK : IsCompact K := by
    dsimp [K, R, a, z0]
    exact hinfcompact (C + ‖Classical.choose hS‖) ((Phi xinf : EReal).toReal + 1)
  have hEventuallyK : ∀ᶠ t in atTop, x t ∈ K := by
    have hlt : ∀ᶠ t in atTop, (Phi (x t) : EReal).toReal < a := by
      dsimp [a]
      exact hvalue.eventually_lt_const (lt_add_one _)
    filter_upwards [hC, hlt, eventually_ge_atTop (0 : ℝ)] with t ht htv ht0
    constructor
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hsum : ‖x t‖ + ‖z0‖ ≤ C + ‖z0‖ := by linarith
      exact le_trans (norm_sub_le _ _) (by simpa [R] using hsum)
    · have hcoer : ((Phi (x t) : EReal).toReal : EReal) ≤ (a : EReal) := by
        exact_mod_cast le_of_lt htv
      exact (EReal.le_coe_toReal (ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp
        (hdom.1 t ht0)))).trans hcoer
  have hscalar : ∀ ell : H →L[ℝ] ℝ,
      Tendsto (fun t ↦ ell (x t)) atTop (nhds (ell xinf)) := by
    intro ell
    let u : H := (InnerProductSpace.toDual ℝ H).symm ell
    have hu := (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H xinf) |>.comp hxweak
    have hrepr (y : H) : ell y = inner ℝ y u := by
      calc
        ell y = inner ℝ u y := (InnerProductSpace.toDual_symm_apply).symm
        _ = inner ℝ y u := real_inner_comm _ _
    simpa only [hrepr] using hu
  exact ⟨xinf, hxinfS,
    cor218_strong_tendsto_of_eventually_compact_and_weak_scalar_convergence x xinf K hK
      hEventuallyK hscalar⟩
```

## Proof explanation
The proof begins by selecting a point from the nonempty set $S$. The command `let z0 : H := Classical.choose hS` introduces a chosen element $z_0\in H$, and `Classical.choose_spec hS` proves `hz0 : z0 ∈ S`. This witness is needed because the earlier theorem `proposition_2_16` requires a particular solution $z\in S$.

Next the proof invokes `proposition_2_16`. That theorem, under the same dynamical, cocoercivity, regularity, subgradient, $L^2$, domain, and weak-convergence assumptions, and given a point $z\in S$, states that the function

$$
t\mapsto \mathrm{toReal}(\Phi(x(t)))
-\mathrm{toReal}(\Phi(z))
+\langle Bz,x(t)-z\rangle
$$

is integrable on $[0,\infty)$, that this function tends to $0$ as $t\to\infty$, and that there exists $x_\infty\in S$ such that

$$
x(t)\rightharpoonup x_\infty
$$

weakly and

$$
\mathrm{toReal}(\Phi(x(t)))\to \mathrm{toReal}(\Phi(x_\infty)).
$$

The proof applies this result with $z=z_0$. The `obtain` pattern discards the integrability conclusion and the energy-to-zero conclusion, keeping only the existence of $x_\infty\in S$, its weak convergence property `hxweak`, and the convergence of the real parts of the $\Phi$-values `hvalue`. Thus the proof has a candidate limit $x_\infty\in S$, weak convergence of $x(t)$ to $x_\infty$, and convergence of $\mathrm{toReal}(\Phi(x(t)))$ to $L=\mathrm{toReal}(\Phi(x_\infty))$.

The next step uses `cor218_eventually_norm_le_of_tendsto_weakly`. This lemma says that if $x(t)$ converges weakly to a point $z$, then there exists a real constant $C$ such that eventually $`\|x(t)\|\le C`$. Applied to `hxweak`, it gives `hC : ∀ᶠ t, ‖x(t)‖ ≤ C`. This is the uniform eventual boundedness of a weakly convergent trajectory, and it will be used to keep $x(t)$ inside a closed ball.

The proof then defines

```math
a=L+1,\qquad R=C+\|z_0\|,\qquad
K=\overline{B}(z_0,R)\cap\{y:\Phi(y)\le a\}.
```

The set $K$ is an intersection of a closed ball around $z_0$ with a sublevel set of $\Phi$. To prove that $K$ is compact, the proof uses `hinfcompact`, which exactly asserts compactness of sets of this form for the chosen center $z_0$. The tactic `dsimp [K, R, a, z0]` unfolds the local definitions, and `exact hinfcompact (C + ‖Classical.choose hS‖) ((Phi xinf).toReal + 1)` matches the required radius and level. Hence `hK : IsCompact K`.

The proof now shows that $x(t)$ is eventually contained in $K$. From `hvalue`, which says $\mathrm{toReal}(\Phi(x(t)))\to L$, and from $L\lt a=L+1$, the lemma `eventually_lt_const` gives

$$
\forallᶠ t,\quad \mathrm{toReal}(\Phi(x(t)))<a.
$$

The command `filter_upwards [hC, hlt, eventually_ge_atTop 0]` combines three eventual facts: the norm bound $`\|x(t)\|\le C`$, the strict upper bound on the real part of$\Phi(x(t))$, and the eventual condition$t\ge0$.

For such a $t$, the proof proves $x(t)\in K$ by proving both components of the intersection. First, for the closed ball, `rw [Metric.mem_closedBall, dist_eq_norm]` rewrites the goal into the norm inequality

```math
\|x(t)-z_0\|\le R.
```

From $`\|x(t)\|\le C`$, `linarith` derives

```math
\|x(t)\|+\|z_0\|\le C+\|z_0\|.
```

Then `norm_sub_le` gives

```math
\|x(t)-z_0\|\le \|x(t)\|+\|z_0\|,
```

and `le_trans` combines the two inequalities. Since $`R=C+\|z_0\|`$, this proves$x(t)\in\overline{B}(z_0,R)$.

Second, for the sublevel condition, the proof must show

$$
\Phi(x(t))\le a.
$$

From the already established real inequality $\mathrm{toReal}(\Phi(x(t)))\lt a$, the command `exact_mod_cast le_of_lt htv` coerces the non-strict inequality to $\mathrm{EReal}$:

$$
(\mathrm{toReal}(\Phi(x(t))):\mathrm{EReal})\le (a:\mathrm{EReal}).
$$

The domain hypothesis `hdom.1 t ht0` says $x(t)\in\mathrm{dom}\Phi$. The lemma `ERealFunction.mem_effectiveDomain_iff` turns this into the side condition needed by `EReal.le_coe_toReal`; that lemma says an extended real number which is not $+\infty$ is bounded above by the coercion of its real part. Thus

$$
\Phi(x(t))\le (\mathrm{toReal}(\Phi(x(t))):\mathrm{EReal}).
$$

Combining this with the previous coercion inequality gives $\Phi(x(t))\le a$. Therefore $x(t)\in K$, and `filter_upwards` packages this as the eventual statement `hEventuallyK`.

The proof then converts the weak convergence hypothesis into convergence against every continuous linear functional. For an arbitrary $\ell:H\to_L[\mathbb R]\mathbb R$, the command `intro ell` introduces it. In a Hilbert space, $\ell$ is represented by an element $u\in H$ via

$$
\ell(y)=\langle y,u\rangle.
$$

The proof sets $u = (\texttt{InnerProductSpace.toDual ℝ H}).\texttt{symm }\ell$. The equality $\ell(y)=\langle u,y\rangle$ follows from `InnerProductSpace.toDual_symm_apply`, and `real_inner_comm` swaps the arguments to obtain $\ell(y)=\langle y,u\rangle$. This is the local lemma `hrepr`.

The cited result `weakSpace_continuous_inner_right u` says that the map

$$
X\mapsto \left\langle (\mathrm{toWeakSpace})^{-1}(X),u\right\rangle
$$

is continuous on the weak space. Composing its continuity with the weak convergence `hxweak` gives

$$
\langle x(t),u\rangle \to \langle x_\infty,u\rangle.
$$

Using `simpa only [hrepr]`, the proof rewrites the inner products as $\ell(x(t))$ and $\ell(x_\infty)$, obtaining

$$
\ell(x(t))\to \ell(x_\infty)
$$

for every continuous linear functional $\ell$. This is exactly the scalar form of weak convergence required by the next theorem.

Finally, the proof applies
`cor218_strong_tendsto_of_eventually_compact_and_weak_scalar_convergence`.
That theorem states that if a map $x:\mathbb R\to H$ is eventually contained in a compact set $K$, and if for every continuous linear functional $\ell$ one has $\ell(x(t))\to \ell(x_\star)$, then $x(t)\to x_\star$ strongly in norm. The proof supplies the compactness `hK`, the eventual membership `hEventuallyK`, and the scalar convergence `hscalar`, with $x_\star=x_\infty$. The returned conclusion is

$$
x(t)\to x_\infty
$$

strongly. Since `hxinfS` gives $x_\infty\in S$, the final `exact` assembles the required existential:

$$
\exists z\in S,\quad x(t)\to z
$$

strongly as $t\to\infty$.

