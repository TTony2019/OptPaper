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
The theorem is set in a real inner-product space \(H\) with an additive normed commutative group structure. The variables are: a map \(B:H\to H\); real numbers \(\beta\) and \(\mu\); a hypothesis \(hB\) saying that \(B\) is \(\beta\)-cocoercive on the whole space \(\operatorname{Set.univ}\), meaning for all \(x,y\in H\),

\[
\beta \,\|Bx-By\|^2 \le \langle x-y,\; Bx-By\rangle,
\]

where the inner product is over \(\mathbb R\); and a hypothesis \(hmu\) asserting

\[
0<\mu \quad\text{and}\quad \mu<2\beta.
\]

The conclusion is that the function

\[
F(x)=x-\mu\, Bx
\]

is Lipschitz with constant \(1\), i.e.

\[
\operatorname{LipschitzWith}\;1\;\bigl(x\mapsto x-\mu\,Bx\bigr).
\]

In the normed metric this is equivalent to saying that for all \(x,y\in H\),

\[
\|F(x)-F(y)\|\le \|x-y\|.
\]

Thus the claim is: subtracting a \(\beta\)-cocoercive operator multiplied by a sufficiently small positive parameter \(\mu\) gives a nonexpansive mapping.

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
The Lean proof starts by using `refine LipschitzWith.of_dist_le_mul ?_`, which reduces the Lipschitz statement to proving a pointwise distance inequality for all \(x,y\). Then `intro x y` introduces arbitrary elements \(x,y\in H\); the remaining goal is \(\operatorname{dist}(F(x),F(y))\le 1\cdot \operatorname{dist}(x,y)\).

The proof instantiates the cocoercivity hypothesis at these \(x,y\). Since the hypothesis is stated on the subtype `Set.univ`, the proof forms elements \(\langle x,\operatorname{mem}\rangle\) and \(\langle y,\operatorname{mem}\rangle\) and uses `hB.ineq`; the `simpa` command simplifies the subtype notation and yields the main inequality

\[
hco:\quad \beta\,\|Bx-By\|^2
\le \langle x-y,\; Bx-By\rangle .
\]

Next, several auxiliary inequalities are derived.

- Because \(\mu<2\beta\), we have \(\mu\le 2\beta\). Multiplying \(\mu\le 2\beta\) by the nonnegative number \(\|Bx-By\|^2\), and then by the nonnegative number \(\mu\), gives

\[
hparam:\quad 
\mu\Bigl(\mu\,\|Bx-By\|^2\Bigr)
\le 
\mu\Bigl((2\beta)\,\|Bx-By\|^2\Bigr).
\]

This is done using `mul_le_mul_of_nonneg_right`, `mul_le_mul_of_nonneg_left`, and the fact that squares are nonnegative.

- Multiplying the cocoercivity inequality `hco` by the nonnegative number \(\mu\) gives

\[
hco\_mu:\quad
\mu\Bigl(\beta\,\|Bx-By\|^2\Bigr)
\le 
\mu\,\langle x-y,\; Bx-By\rangle .
\]

The proof then records an algebraic identity:

\[
hrewrite:\quad
(x-\mu\,Bx)-(y-\mu\,By)
=
(x-y)-\mu\,(Bx-By).
\]

This follows by rewriting subtraction as addition and using associativity and commutativity; the `simp` command handles the algebra.

The central part is proving the squared norm inequality

\[
hsq:\quad \|F(x)-F(y)\|^2\le \|x-y\|^2.
\]

The `calc` block expands the left-hand side.

1. By `hrewrite`,

\[
\|F(x)-F(y)\|^2
=
\|(x-y)-\mu\,(Bx-By)\|^2.
\]

2. Applying `norm_sub_sq_real` expands the square of a difference in an inner-product space:

\[
\|(x-y)-\mu(Bx-By)\|^2
=
\|x-y\|^2
-2\,\langle x-y,\;\mu(Bx-By)\rangle
+\|\mu(Bx-By)\|^2.
\]

3. Using linearity of the inner product in the second argument and the behavior of norms under scalar multiplication, the middle and last terms are simplified. The rewrite uses `real_inner_smul_right`, `norm_smul`, `Real.norm_eq_abs`, and `abs_of_pos hmu.1` to replace \(\mu\) by its positive value, then `ring` closes the algebraic simplification. The result is

\[
\|F(x)-F(y)\|^2
=
\|x-y\|^2
-2\mu\,\langle x-y,\;Bx-By\rangle
+\mu^2\,\|Bx-By\|^2.
\]

4. The final estimate is

\[
\|F(x)-F(y)\|^2\le \|x-y\|^2.
\]

This follows by showing that the additional terms are nonpositive. Writing

\[
n=\|Bx-By\|^2,\qquad c=\langle x-y,\;Bx-By\rangle ,
\]

the extra terms are \(-2\mu c+\mu^2 n\). The needed inequality is \(\mu^2 n\le 2\mu c\). The previously derived facts provide

\[
\mu^2 n\le 2\beta\mu n
\]

from `hparam`, and

\[
2\beta\mu n\le 2\mu c
\]

from `hco_mu`. The tactic `nlinarith [hparam, hco_mu]` combines these nonlinear real inequalities to finish the target inequality.

From the squared inequality `hsq`, the proof obtains

\[
\|F(x)-F(y)\|\le \|x-y\|
\]

using `sq_le_sq₀`, since both norm expressions are nonnegative. Finally, `simpa [dist_eq_norm] using hnorm` converts this norm inequality into the metric inequality

\[
\operatorname{dist}(F(x),F(y))\le \operatorname{dist}(x,y),
\]

which completes the proof of the Lipschitz property.

The important Lean commands play the following roles: `intro` introduces the universal quantifiers over \(x\) and \(y\); `rw` replaces expressions using previously proved equalities or standard library identities; `simp` performs algebraic simplification, especially rewriting subtype elements and final distance notation; `exact` supplies a direct proof of an intermediate multiplication step; and `nlinarith` solves the final real nonlinear inequality using the hypotheses `hparam` and `hco_mu`.

