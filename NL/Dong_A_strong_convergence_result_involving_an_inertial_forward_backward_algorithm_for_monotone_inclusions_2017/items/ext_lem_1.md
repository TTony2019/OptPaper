## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/ext_lem_1.lean`

## Lean statement
```lean
theorem squared_distance_constraint_isClosed_convex {C : Set H} (hClosed : IsClosed C)
    (hConvex : Convex ℝ C) (x y z : H) (a : ℝ) :
    IsClosed {v ∈ C | ‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a} ∧
      Convex ℝ {v ∈ C | ‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a}
```

## Statement explanation
The declaration `squared_distance_constraint_isClosed_convex` is stated in an ambient real inner-product space $H$. It takes a set $C\subseteq H$ that is assumed closed and convex over $\mathbb R$, three points $x,y,z\in H$, and a real number $a$. The set under consideration is

$$
S=\{v\in C \mid \|y-v\|^{2}\le \|x-v\|^{2}+\langle z,v\rangle+a\}.
$$

The conclusion asserts two things about this set $S$:

$$
S \text{ is closed}
\qquad\text{and}\qquad
S \text{ is convex over } \mathbb R.
$$

Mathematically, the defining inequality is a squared-distance constraint with an additional real linear term $\langle z,v\rangle$ and constant $a$. Expanding the two squared norms shows that the quadratic terms $\|v\|^{2}$ cancel, so the inequality is really a closed half-space condition. Indeed,

$$
\|y-v\|^{2}=\|y\|^{2}-2\langle y,v\rangle+\|v\|^{2},
\qquad
\|x-v\|^{2}=\|x\|^{2}-2\langle x,v\rangle+\|v\|^{2}.
$$

After cancellation, the inequality is equivalent to

$$
\langle 2(x-y)-z,v\rangle \le \|x\|^{2}-\|y\|^{2}+a.
$$

Thus the theorem says that intersecting the closed convex set $C$ with this closed affine half-space remains closed and convex.

## Lean proof
```lean
by
  let w : H := (2 : ℝ) • (x - y) - z
  let b : ℝ := ‖x‖ ^ 2 - ‖y‖ ^ 2 + a
  let D : Set H := {v | inner ℝ w v ≤ b}
  have hconstraint : ∀ v : H,
      (‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a) ↔ v ∈ D := by
    intro v
    dsimp [D, w, b]
    rw [norm_sub_sq_real y v, norm_sub_sq_real x v]
    simp only [inner_sub_left, real_inner_smul_left]
    constructor <;> intro hv <;> linarith
  have hD_closed : IsClosed D := by
    dsimp [D]
    exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hD_convex : Convex ℝ D := by
    dsimp [D]
    simpa [Set.preimage, innerSL_apply_apply] using
      (convex_Iic b).is_linear_preimage (innerSL ℝ w).isLinear
  have htarget : {v ∈ C | ‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a} = C ∩ D := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    exact and_congr Iff.rfl (hconstraint v)
  rw [htarget]
  exact ⟨hClosed.inter hD_closed, hConvex.inter hD_convex⟩
```

## Proof explanation
The proof first introduces local abbreviations.

$$
w=2(x-y)-z,\qquad
b=\|x\|^{2}-\|y\|^{2}+a,\qquad
D=\{v\in H \mid \langle w,v\rangle\le b\}.
$$

The command `let` in Lean simply names these expressions; mathematically, $D$ is the closed half-space obtained after cancelling the $\|v\|^{2}$ terms from the original constraint.

The first main step is `hconstraint`. It proves that for every $v\in H$,

$$
\|y-v\|^{2}\le \|x-v\|^{2}+\langle z,v\rangle+a
\quad\Longleftrightarrow\quad
v\in D.
$$

After `intro v`, the proof uses `dsimp [D, w, b]` to unfold the definitions. Then it applies `norm_sub_sq_real y v` and `norm_sub_sq_real x v`. These rewrite the squared norms by the real inner-product expansions

$$
\|y-v\|^{2}=\|y\|^{2}-2\langle y,v\rangle+\|v\|^{2},
\qquad
\|x-v\|^{2}=\|x\|^{2}-2\langle x,v\rangle+\|v\|^{2}.
$$

Next, `simp only [inner_sub_left, real_inner_smul_left]` expands

$$
\langle w,v\rangle
=
\langle 2(x-y)-z,v\rangle
=
2\langle x,v\rangle-2\langle y,v\rangle-\langle z,v\rangle.
$$

After these rewrites, both sides of the claimed equivalence are linear inequalities in the inner products. The tactic line `constructor <;> intro hv <;> linarith` splits the equivalence into two implications and proves each direction by linear arithmetic. In the forward direction, the original inequality yields

$$
\langle w,v\rangle\le b.
$$

In the reverse direction, the half-space inequality yields the original squared-distance inequality. The tactic `linarith` handles cancellation of $\|v\|^{2}$ and rearrangement of the remaining linear terms.

The second main step proves `hD_closed`, i.e. that $D$ is closed. After unfolding $D$, the proof applies `isClosed_le` to the two continuous functions

$$
v\mapsto \langle w,v\rangle,
\qquad
v\mapsto b.
$$

The first is continuous because it is the inner product of a constant vector with the identity map; the second is constant. The lemma `isClosed_le` says that a set defined by a pointwise inequality $f(v)\le g(v)$ between continuous real-valued functions is closed. Hence

$$
D=\{v\mid \langle w,v\rangle\le b\}
$$

is closed.

The third main step proves `hD_convex`, i.e. that $D$ is convex. The proof uses `convex_Iic b`, which states that the real interval

$$
\{t\in\mathbb R \mid t\le b\}
$$

is convex. It also uses `(innerSL ℝ w).isLinear`, which supplies the linear map

$$
v\mapsto \langle w,v\rangle.
$$

The lemma `is_linear_preimage` says that the preimage of a convex set under a linear map is convex. Since $D$ is the preimage of $\{t\mid t\le b\}$ under the linear functional $v\mapsto \langle w,v\rangle$, it follows that $D$ is convex. The `simpa` rewrites the set-preimage notation and uses the identification of `innerSL` to match exactly the definition of $D$.

The fourth step proves the set equality

$$
\{v\in C \mid \|y-v\|^{2}\le \|x-v\|^{2}+\langle z,v\rangle+a\}
=
C\cap D.
$$

The proof uses `ext v`, i.e. set extensionality, so it suffices to prove the equivalence of membership for an arbitrary $v$. After simplifying set-membership notation, membership in the left-hand set means

$$
v\in C
\quad\text{and}\quad
\|y-v\|^{2}\le \|x-v\|^{2}+\langle z,v\rangle+a.
$$

Membership in $C\cap D$ means

$$
v\in C
\quad\text{and}\quad
v\in D.
$$

The first condition is identical, so it is discharged by `Iff.rfl`; the second condition is exactly the equivalence `hconstraint v`. The term `and_congr Iff.rfl (hconstraint v)` combines these two equivalences into the required equivalence of conjunctions.

Finally, the proof rewrites the original target set as $C\cap D$ using `rw [htarget]`. The conclusion is then

$$
\langle hClosed.inter hD_closed,\ hConvex.inter hD_convex\rangle.
$$

Here `IsClosed.inter` says that the intersection of two closed sets is closed, so $C\cap D$ is closed. Similarly, `Convex.inter` says that the intersection of two convex sets is convex, so $C\cap D$ is convex. Therefore the original squared-distance constraint set is both closed and convex.

