## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_3.lean`

## Lean statement
```lean
theorem id_sub_cocoercive_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (B : H → H) (beta mu : ℝ)
    (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)) (hmu : 0 < mu ∧ mu < 2 * beta) :
    LipschitzWith 1 (fun x : H ↦ x - mu • B x)
```

## Statement explanation
The declaration states a nonexpansiveness property in a real inner product space. Let \(H\) be a type equipped with a normed additive commutative group structure and an \(\mathbb R\)-inner product structure, so that \(H\) has a norm \(\|\cdot\|\), a distance, and a real inner product \(\langle \cdot,\cdot\rangle\). Let \(B:H\to H\) be an operator, and let \(\beta,\mu\in\mathbb R\).

The hypothesis on \(B\) says that \(B\), regarded as a map on the whole set \(H\) (encoded by `Set.univ`), is cocoercive on all of \(H\) with constant \(\beta\). The exact consequence used in the proof is that for every \(x,y\in H\),

\[
\beta\|B x-B y\|^2\le \langle x-y, Bx-By\rangle .
\]

The hypothesis on the parameter \(\mu\) is

\[
0<\mu<2\beta .
\]

The conclusion is that the map

\[
T_\mu(x)=x-\mu Bx
\]

is \(1\)-Lipschitz, i.e. nonexpansive:

\[
\operatorname{dist}(T_\mu x,T_\mu y)\le 1\cdot \operatorname{dist}(x,y)
\]

for all \(x,y\in H\), equivalently

\[
\|(x-\mu Bx)-(y-\mu By)\|\le \|x-y\| .
\]

Thus the theorem says that subtracting from the identity a \(\mu\)-multiple of a \(\beta\)-cocoercive operator is nonexpansive whenever \(\mu\) lies strictly between \(0\) and \(2\beta\).

## Lean proof
```lean
by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hco : beta * ‖B x - B y‖ ^ 2 ≤ inner ℝ (x - y) (B x - B y) := by
    simpa using hB.ineq (⟨x, Set.mem_univ x⟩ : (Set.univ : Set H))
      (⟨y, Set.mem_univ y⟩ : (Set.univ : Set H))
  have hparam :
      mu * (mu * ‖B x - B y‖ ^ 2) ≤
        mu * ((2 * beta) * ‖B x - B y‖ ^ 2) := by
    have hq : mu * ‖B x - B y‖ ^ 2 ≤
        (2 * beta) * ‖B x - B y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hmu.2.le (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hq hmu.1.le
  have hco_mu :
      mu * (beta * ‖B x - B y‖ ^ 2) ≤
        mu * inner ℝ (x - y) (B x - B y) :=
    mul_le_mul_of_nonneg_left hco hmu.1.le
  have hrewrite :
      (x - mu • B x) - (y - mu • B y) =
        (x - y) - mu • (B x - B y) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hsq : ‖(x - mu • B x) - (y - mu • B y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    calc
      ‖(x - mu • B x) - (y - mu • B y)‖ ^ 2 =
          ‖(x - y) - mu • (B x - B y)‖ ^ 2 := by rw [hrewrite]
      _ = ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) (mu • (B x - B y)) +
          ‖mu • (B x - B y)‖ ^ 2 := by rw [norm_sub_sq_real]
      _ = ‖x - y‖ ^ 2 - 2 * mu * inner ℝ (x - y) (B x - B y) +
          mu ^ 2 * ‖B x - B y‖ ^ 2 := by
        rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hmu.1]
        ring
      _ ≤ ‖x - y‖ ^ 2 := by
        nlinarith [hparam, hco_mu]
  have hnorm : ‖(x - mu • B x) - (y - mu • B y)‖ ≤ ‖x - y‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  simpa [dist_eq_norm] using hnorm
```

## Proof explanation
The proof starts with `refine LipschitzWith.of_dist_le_mul ?_`. The lemma `LipschitzWith.of_dist_le_mul` is the pointwise criterion for being Lipschitz: if a function \(f\) satisfies

\[
\operatorname{dist}(f x,f y)\le K\operatorname{dist}(x,y)
\]

for all \(x,y\), then \(f\) is \(K\)-Lipschitz. Here \(K=1\) and \(f(x)=x-\mu Bx\). The `refine` command applies this criterion and leaves the pointwise estimate as the new goal.

Next, `intro x y` introduces arbitrary \(x,y\in H\). The proof must show the distance inequality for these two arbitrary points.

The first auxiliary fact is `hco`. It is obtained from `hB.ineq` applied to the subtype elements corresponding to \(x\) and \(y\) in `Set.univ`. Since the function on `Set.univ` is just \(x\mapsto Bx\), and since `simpa` removes the subtype coercions, this produces exactly

\[
\beta\|B x-B y\|^2\le \langle x-y,Bx-By\rangle .
\]

This is the only place where the cocoercivity hypothesis on \(B\) is used.

The second auxiliary fact is `hparam`. The proof first derives

\[
\mu\|Bx-By\|^2\le (2\beta)\|Bx-By\|^2 .
\]

Indeed, from \(0<\mu<2\beta\) we have \(\mu\le 2\beta\), and \(\|Bx-By\|^2\ge 0\); the lemma `mul_le_mul_of_nonneg_right` multiplies the inequality \(\mu\le 2\beta\) on the right by the nonnegative factor \(\|Bx-By\|^2\). Then `mul_le_mul_of_nonneg_left` multiplies this resulting inequality on the left by the nonnegative number \(\mu\), using \(0\le\mu\). Therefore

\[
\mu^2\|Bx-By\|^2\le 2\beta\mu\|Bx-By\|^2 .
\]

The third auxiliary fact is `hco_mu`. It multiplies the cocoercivity inequality `hco` by the nonnegative scalar \(\mu\), again using `mul_le_mul_of_nonneg_left` and \(0\le\mu\). This gives

\[
\mu\beta\|Bx-By\|^2\le \mu\langle x-y,Bx-By\rangle .
\]

The auxiliary identity `hrewrite` is purely algebraic:

\[
(x-\mu Bx)-(y-\mu By)=(x-y)-\mu(Bx-By).
\]

It is proved by `simp` using the facts that subtraction is addition of negatives and that addition is associative and commutative. This identity is needed to compare the difference of the two updated points with the simpler expression \((x-y)-\mu(Bx-By)\).

The main estimate is `hsq`, which proves

\[
\|(x-\mu Bx)-(y-\mu By)\|^2\le \|x-y\|^2 .
\]

It proceeds by a `calc` chain. First, by `hrewrite`,

\[
\|(x-\mu Bx)-(y-\mu By)\|^2
=
\|(x-y)-\mu(Bx-By)\|^2 .
\]

Then the lemma `norm_sub_sq_real` expands the squared norm of a difference in a real inner product space:

\[
\|a-b\|^2=\|a\|^2-2\langle a,b\rangle+\|b\|^2 .
\]

Applying this with \(a=x-y\) and \(b=\mu(Bx-By)\) gives

\[
\|(x-y)-\mu(Bx-By)\|^2
=
\|x-y\|^2
-2\langle x-y,\mu(Bx-By)\rangle
+\|\mu(Bx-By)\|^2 .
\]

Next the proof rewrites the inner product and the norm. The lemma `real_inner_smul_right` gives

\[
\langle x-y,\mu(Bx-By)\rangle
=
\mu\langle x-y,Bx-By\rangle .
\]

The lemmas `norm_smul`, `Real.norm_eq_abs`, and `abs_of_pos hmu.1` give

\[
\|\mu(Bx-By)\|^2
=
(|\mu|\,\|Bx-By\|)^2
=
\mu^2\|Bx-By\|^2,
\]

because \(0<\mu\). Thus the expression becomes

\[
\|x-y\|^2
-2\mu\langle x-y,Bx-By\rangle
+\mu^2\|Bx-By\|^2 .
\]

The final inequality in the `calc` chain is proved by `nlinarith [hparam, hco_mu]`. The two cited inequalities combine as follows. From `hparam`,

\[
\mu^2\|Bx-By\|^2\le 2\beta\mu\|Bx-By\|^2 .
\]

From `hco_mu`, after multiplying by \(2\),

\[
2\mu\beta\|Bx-By\|^2\le 2\mu\langle x-y,Bx-By\rangle .
\]

Since real multiplication is commutative, \(2\beta\mu=2\mu\beta\), so

\[
\mu^2\|Bx-By\|^2\le 2\mu\langle x-y,Bx-By\rangle .
\]

Therefore the extra terms satisfy

\[
-2\mu\langle x-y,Bx-By\rangle+\mu^2\|Bx-By\|^2\le 0,
\]

and hence

\[
\|x-y\|^2
-2\mu\langle x-y,Bx-By\rangle
+\mu^2\|Bx-By\|^2
\le
\|x-y\|^2 .
\]

The tactic `nlinarith` checks exactly this nonlinear arithmetic implication from `hparam` and `hco_mu`.

From `hsq`, the proof derives `hnorm`:

\[
\|(x-\mu Bx)-(y-\mu By)\|\le \|x-y\| .
\]

This uses `sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)`. That lemma says that for two nonnegative real numbers \(a,b\), the inequality \(a^2\le b^2\) implies \(a\le b\). Here both quantities are norms, so they are nonnegative, and `hsq` is precisely the squared inequality.

Finally, `simpa [dist_eq_norm] using hnorm` converts the norm inequality into the required distance inequality. The lemma `dist_eq_norm` states that in a normed additive group,

\[
\operatorname{dist}(u,v)=\|u-v\| .
\]

Thus the inequality

\[
\|(x-\mu Bx)-(y-\mu By)\|\le \|x-y\|
\]

is exactly

\[
\operatorname{dist}(x-\mu Bx,y-\mu By)\le \operatorname{dist}(x,y),
\]

which is the pointwise form of the claim that \(x\mapsto x-\mu Bx\) is \(1\)-Lipschitz.

