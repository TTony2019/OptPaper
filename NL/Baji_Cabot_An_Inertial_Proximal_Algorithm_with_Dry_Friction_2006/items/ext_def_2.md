## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/ext_def_2.lean`

## Lean statement
```lean
theorem resolvent_single_valued (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (lam : ℝ) (hlam : lam > 0) :
    SetValuedOperator.IsAtMostSingleValued (J[(lam • A)])
```

## Statement explanation
The declaration is made in the ambient setting of a real vector space \(H\) equipped with the inner product and norm operations used in the proof. The object \(A\) is a set-valued operator on \(H\), so \(A\) assigns to each point \(u\in H\) a subset \(A(u)\subseteq H\). The hypothesis \(hA\) says that \(A\) is maximal monotone. In particular, the proof uses the monotonicity part of this hypothesis: whenever \(a_1\in A(u_1)\) and \(a_2\in A(u_2)\), one has
\[
\langle a_1-a_2,u_1-u_2\rangle\ge 0.
\]
The real number \(\lambda\) satisfies \(\lambda>0\). The notation \(J_{\lambda A}\) denotes the resolvent of the scaled set-valued operator \(\lambda A\). The cited characterization `mem_resolvent_smul_iff` says that
\[
y\in J_{\lambda A}(x)
\quad\Longleftrightarrow\quad
x\in (I+\lambda A)(y),
\]
where, by the cited definition of `identityAddScaled`,
\[
(I+\lambda A)(y)=\{y+\lambda a\mid a\in A(y)\}.
\]
Thus \(y\in J_{\lambda A}(x)\) holds exactly when there exists \(a\in A(y)\) such that \(x=y+\lambda a\).

The conclusion is
\[
\operatorname{IsAtMostSingleValued}(J_{\lambda A}),
\]
which means that for every \(x\in H\), the set \(J_{\lambda A}(x)\) has at most one element. Equivalently, if \(y_1,y_2\in J_{\lambda A}(x)\), then \(y_1=y_2\). So the theorem states that a positive scalar multiple of a maximal monotone set-valued operator has an at-most-single-valued resolvent.

## Lean proof
```lean
by
  intro x y₁ hy₁ y₂ hy₂
  rw [mem_resolvent_smul_iff] at hy₁ hy₂
  dsimp [SetValuedOperator.identityAddScaled] at hy₁ hy₂
  rcases hy₁ with ⟨a₁, ha₁, hx₁⟩
  rcases hy₂ with ⟨a₂, ha₂, hx₂⟩
  have hy_sub : y₁ - y₂ = lam • (a₂ - a₁) := by
    have hy₁_expr : y₁ = x - lam • a₁ := by
      calc
        y₁ = (y₁ + lam • a₁) - lam • a₁ := (add_sub_cancel_right _ _).symm
        _ = x - lam • a₁ := by rw [hx₁]
    have hy₂_expr : y₂ = x - lam • a₂ := by
      calc
        y₂ = (y₂ + lam • a₂) - lam • a₂ := (add_sub_cancel_right _ _).symm
        _ = x - lam • a₂ := by rw [hx₂]
    rw [hy₁_expr, hy₂_expr]
    calc
      (x - lam • a₁) - (x - lam • a₂) = lam • a₂ - lam • a₁ := by abel
      _ = lam • (a₂ - a₁) := by rw [smul_sub]
  have hmono : 0 ≤ inner ℝ (a₁ - a₂) (y₁ - y₂) := hA.1 a₁ ha₁ a₂ ha₂
  rw [hy_sub, real_inner_smul_right] at hmono
  have hinner : inner ℝ (a₁ - a₂) (a₂ - a₁) = -‖a₁ - a₂‖ ^ 2 := by
    have : a₂ - a₁ = -(a₁ - a₂) := by abel
    rw [this, inner_neg_right]
    simp
  rw [hinner] at hmono
  have hsq : ‖a₁ - a₂‖ ^ 2 = 0 := by
    nlinarith [hlam, sq_nonneg (‖a₁ - a₂‖)]
  have haeq : a₁ = a₂ := by
    have hnorm : ‖a₁ - a₂‖ = 0 := by
      nlinarith [norm_nonneg (a₁ - a₂), hsq]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact sub_eq_zero.mp (by simpa [haeq] using hy_sub)
```

## Proof explanation
The proof begins with

```lean
intro x y₁ hy₁ y₂ hy₂
```

This unfolds the meaning of `SetValuedOperator.IsAtMostSingleValued`. To prove that \(J_{\lambda A}\) is at most single-valued, it suffices to fix an arbitrary \(x\in H\), two candidate values \(y_1,y_2\), and hypotheses
\[
hy_1:y_1\in J_{\lambda A}(x),
\qquad
hy_2:y_2\in J_{\lambda A}(x),
\]
and then prove \(y_1=y_2\).

Next,

```lean
rw [mem_resolvent_smul_iff] at hy₁ hy₂
```

uses the cited theorem `mem_resolvent_smul_iff`. Specialized to the current variables, it converts
\[
y_i\in J_{\lambda A}(x)
\]
into
\[
x\in (I+\lambda A)(y_i)
\]
for \(i=1,2\). The cited definition `identityAddScaled` says that \((I+\lambda A)(y_i)\) is the set
\[
\{y_i+\lambda a\mid a\in A(y_i)\}.
\]
Therefore membership in this set is the existence of some \(a_i\in A(y_i)\) satisfying \(y_i+\lambda a_i=x\).

Accordingly,

```lean
dsimp [SetValuedOperator.identityAddScaled] at hy₁ hy₂
```

unfolds the definition of `identityAddScaled`, and then

```lean
rcases hy₁ with ⟨a₁, ha₁, hx₁⟩
rcases hy₂ with ⟨a₂, ha₂, hx₂⟩
```

extracts witnesses
\[
a_1\in A(y_1),\qquad y_1+\lambda a_1=x,
\]
and
\[
a_2\in A(y_2),\qquad y_2+\lambda a_2=x.
\]

The proof then derives the relation between \(y_1-y_2\) and the selected elements \(a_1,a_2\). First it obtains
\[
y_1=x-\lambda a_1,\qquad y_2=x-\lambda a_2.
\]
The calculation uses `add_sub_cancel_right`, which has the concrete form
\[
(y+\lambda a)-\lambda a=y,
\]
and then rewrites \(y_i+\lambda a_i\) to \(x\) using \(hx_1\) and \(hx_2\). Subtracting the two expressions gives
\[
y_1-y_2=(x-\lambda a_1)-(x-\lambda a_2)
=\lambda a_2-\lambda a_1
=\lambda(a_2-a_1).
\]
The first equality is handled by `abel`, a tactic for additive abelian group identities, and the last equality by `smul_sub`, which says
\[
\lambda a_2-\lambda a_1=\lambda(a_2-a_1).
\]
Thus the proof establishes
\[
hy_{\text{sub}}:y_1-y_2=\lambda(a_2-a_1).
\]

Next,

```lean
have hmono : 0 ≤ inner ℝ (a₁ - a₂) (y₁ - y₂) := hA.1 a₁ ha₁ a₂ ha₂
```

uses the monotonicity part of the maximal monotonicity hypothesis. Since \(a_1\in A(y_1)\) and \(a_2\in A(y_2)\), monotonicity of \(A\) gives
\[
0\le \langle a_1-a_2,y_1-y_2\rangle.
\]
This is the only place where \(hA\) is used in this proof; the maximality part of the hypothesis is not otherwise invoked.

Substituting the already proved formula for \(y_1-y_2\),

```lean
rw [hy_sub, real_inner_smul_right] at hmono
```

turns the monotonicity inequality into
\[
0\le \langle a_1-a_2,\lambda(a_2-a_1)\rangle.
\]
The theorem `real_inner_smul_right` pulls the scalar out of the second argument of the real inner product:
\[
\langle a_1-a_2,\lambda(a_2-a_1)\rangle
=
\lambda\langle a_1-a_2,a_2-a_1\rangle.
\]
So the inequality becomes
\[
0\le \lambda\langle a_1-a_2,a_2-a_1\rangle.
\]

The proof then computes the inner product of a vector with its negative. Since
\[
a_2-a_1=-(a_1-a_2),
\]
and since `inner_neg_right` gives
\[
\langle u,-v\rangle=-\langle u,v\rangle,
\]
one obtains
\[
\langle a_1-a_2,a_2-a_1\rangle
=
\langle a_1-a_2,-(a_1-a_2)\rangle
=
-\langle a_1-a_2,a_1-a_2\rangle.
\]
The `simp` step then uses the real inner product identity
\[
\langle u,u\rangle=\|u\|^2,
\]
so the previous expression is
\[
-\|a_1-a_2\|^2.
\]
This is exactly the statement of `hinner`:
\[
\langle a_1-a_2,a_2-a_1\rangle=-\|a_1-a_2\|^2.
\]

Rewriting this into `hmono` gives
\[
0\le \lambda\bigl(-\|a_1-a_2\|^2\bigr).
\]
Since \(\lambda>0\) and \(\|a_1-a_2\|^2\ge 0\), the only possibility is
\[
\|a_1-a_2\|^2=0.
\]
This is obtained by

```lean
nlinarith [hlam, sq_nonneg (‖a₁ - a₂‖)]
```

which is a nonlinear arithmetic step using \(\lambda>0\) and nonnegativity of the square.

Then

```lean
have hnorm : ‖a₁ - a₂‖ = 0 := by
  nlinarith [norm_nonneg (a₁ - a₂), hsq]
```

uses nonnegativity of the norm and the fact that its square is zero to conclude
\[
\|a_1-a_2\|=0.
\]
From `norm_eq_zero.mp`, this yields
\[
a_1-a_2=0,
\]
and from `sub_eq_zero.mp`, this yields
\[
a_1=a_2.
\]
So the two selected elements from the sets \(A(y_1)\) and \(A(y_2)\) are equal.

Finally,

```lean
exact sub_eq_zero.mp (by simpa [haeq] using hy_sub)
```

uses the relation
\[
y_1-y_2=\lambda(a_2-a_1).
\]
Since \(a_1=a_2\), the right-hand side becomes \(\lambda\cdot 0=0\), so `simpa [haeq] using hy_sub` simplifies this relation to
\[
y_1-y_2=0.
\]
Applying `sub_eq_zero.mp` gives
\[
y_1=y_2.
\]
This proves that any two elements of \(J_{\lambda A}(x)\) are equal, so \(J_{\lambda A}\) is at most single-valued.

