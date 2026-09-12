## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_thm_3.lean`

## Lean statement
```lean
theorem supportFunction_representation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (F : E → ℝ)
    (hconv : ConvexOn ℝ Set.univ F) (hhom : PositivelyHomogeneous F) (u : E) :
    ∃ l ∈ subdifferential (fun y => (F y : EReal)) 0, F u = inner ℝ l u ∧
      ∀ l' ∈ subdifferential (fun y => (F y : EReal)) 0, inner ℝ l' u ≤ inner ℝ l u
```

## Statement explanation
The theorem `supportFunction_representation` is stated for a finite-dimensional real inner product space $E$. Its data are a real-valued function $F:E\to\mathbb R$, a proof `hconv` that $F$ is convex on all of $E$, a proof `hhom` that $F$ is positively homogeneous, meaning that for every positive real $t$ and every $x\in E$, $F(tx)=tF(x)$, and a vector $u\in E$.

The subdifferential appearing in the statement is taken for the extended-real-valued function

$$
y\mapsto (F(y))_{\mathbb R},
$$

where $(F(y))_{\mathbb R}$ is $F(y)$ regarded as an element of the extended reals. Thus

$$
l\in \partial\bigl(y\mapsto (F(y))_{\mathbb R}\bigr)(0)
$$

means that $l$ is a subgradient at the origin of this extended-real-valued function. For the real-valued function $F$, the cited lemma `mem_convexSubdifferential_iff` identifies this condition with

$$
\forall v\in E,\qquad F(0)+\langle l,v-0\rangle\le F(v).
$$

Since positive homogeneity will force $F(0)=0$, this is equivalently

$$
\forall v\in E,\qquad \langle l,v\rangle\le F(v).
$$

The conclusion of the theorem is that there exists a subgradient $l$ of this extended-real function at $0$ such that

$$
F(u)=\langle l,u\rangle
$$

and such that $l$ maximizes the linear functional $l'\mapsto \langle l',u\rangle$ over all subgradients at $0$:

$$
\forall l'\in \partial\bigl(y\mapsto (F(y))_{\mathbb R}\bigr)(0),\qquad
\langle l',u\rangle\le \langle l,u\rangle.
$$

In ordinary mathematical language, the theorem says that for a convex positively homogeneous real-valued function $F$ on a finite-dimensional real inner product space, the value $F(u)$ is attained as the maximum of $\langle l,u\rangle$ over all subgradients $l$ of $F$ at the origin. Equivalently, $F$ is the support function of its subdifferential at $0$.

## Lean proof
```lean
by
  have htwo := hhom (by norm_num : (0 : ℝ) < 2) (0 : E)
  norm_num at htwo
  have hF0 : F 0 = 0 := by linarith
  have hcont : Continuous F :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hlsc : LowerSemicontinuous F := hcont.lowerSemicontinuous
  have haffine := hconv.real_univ_sSup_affine_eq hlsc
  have hne : (subdifferential (fun y => (F y : EReal)) 0).Nonempty := by
    obtain ⟨L, c, hle, _⟩ := hconv.exists_affine_le_of_lt (𝕜 := ℝ)
      (a := F 0 - 1) (show (0 : E) ∈ Set.univ by simp) (by linarith) isClosed_univ
      (lowerSemicontinuousOn_univ_iff.mpr hlsc)
    have hminor : ∀ x, L x + c ≤ F x := by
      intro x
      simpa using hle ⟨x, Set.mem_univ x⟩
    obtain ⟨hp, _⟩ := riesz_mem_convexSubdifferential_of_affine_minorant
      F hF0 hhom L c hminor
    exact ⟨_, hp⟩
  have hclosed : IsClosed (subdifferential (fun y => (F y : EReal)) 0) := by
    have hset : subdifferential (fun y => (F y : EReal)) 0 =
        ⋂ v : E, {l : E | F 0 + inner ℝ l (v - 0) ≤ F v} := by
      ext l
      rw [mem_convexSubdifferential_iff]
      simp
    rw [hset]
    apply isClosed_iInter
    intro v
    apply isClosed_le
    · fun_prop
    · fun_prop
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunitcompact : IsCompact (Metric.closedBall (0 : E) 1) :=
    ProperSpace.isCompact_closedBall 0 1
  obtain ⟨z, hz, hzmax⟩ := hunitcompact.exists_isMaxOn
    ⟨0, by
      rw [Metric.mem_closedBall, dist_self]
      norm_num⟩ (hcont.abs.continuousOn)
  let B : ℝ := |F z|
  have hB : ∀ x ∈ Metric.closedBall (0 : E) 1, |F x| ≤ B := by
    intro x hx
    exact hzmax hx
  have hBnonneg : 0 ≤ B := abs_nonneg _
  have hbounded : subdifferential (fun y => (F y : EReal)) 0 ⊆ Metric.closedBall 0 B := by
    intro l hl
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hl0 : l = 0
    · simp [hl0, hBnonneg]
    · let q : E := (‖l‖⁻¹ : ℝ) • l
      have hnorm : 0 < ‖l‖ := norm_pos_iff.mpr hl0
      have hqnorm : ‖q‖ = 1 := by
        dsimp [q]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀]
        exact ne_of_gt hnorm
      have hq : q ∈ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, hqnorm]
      have hlq : inner ℝ l q ≤ F q := by
        have hl' : ∀ v, F 0 + inner ℝ l (v - 0) ≤ F v :=
          (mem_convexSubdifferential_iff F 0 l).mp hl
        simpa [hF0, sub_zero] using hl' q
      have hinter : inner ℝ l q = ‖l‖ := by
        dsimp [q]
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [← hinter]
      exact le_trans hlq (le_trans (le_abs_self _) (hB q hq))
  have hcompact : IsCompact (subdifferential (fun y => (F y : EReal)) 0) :=
    (ProperSpace.isCompact_closedBall 0 B).of_isClosed_subset hclosed hbounded
  obtain ⟨l, hl, hlmax⟩ := hcompact.exists_isMaxOn hne
    (by fun_prop : ContinuousOn (fun x : E => inner ℝ x u) (subdifferential (fun y => (F y : EReal)) 0))
  have hsupport_le : ∀ l ∈ subdifferential (fun y => (F y : EReal)) 0, inner ℝ l u ≤ F u := by
    intro l hl
    have hl' : ∀ v, F 0 + inner ℝ l (v - 0) ≤ F v :=
      (mem_convexSubdifferential_iff F 0 l).mp hl
    simpa [hF0, sub_zero] using hl' u
  let A : Set (E → ℝ) :=
    {g | g ≤ F ∧ ∃ (L : E →L[ℝ] ℝ) (c : ℝ), g = L + Function.const E c}
  have hAne : A.Nonempty := by
    let L : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E l
    refine ⟨L, ?_, L, 0, ?_⟩
    · intro x
      change inner ℝ l x ≤ F x
      have hl' : ∀ v, F 0 + inner ℝ l (v - 0) ≤ F v :=
        (mem_convexSubdifferential_iff F 0 l).mp hl
      simpa [hF0, sub_zero] using hl' x
    · ext x
      simp
  have hA_le : ∀ g ∈ A, g u ≤ inner ℝ l u := by
    intro g hg
    obtain ⟨hgF, L, c, hgeq⟩ := hg
    have hminor : ∀ x, L x + c ≤ F x := by
      intro x
      simpa [hgeq] using hgF x
    have hc : c ≤ 0 := by
      have := hminor 0
      simpa [hF0] using this
    obtain ⟨hp, hrepr⟩ := riesz_mem_convexSubdifferential_of_affine_minorant
      F hF0 hhom L c hminor
    calc
      g u = L u + c := by simp [hgeq]
      _ ≤ L u := by linarith
      _ = inner ℝ ((InnerProductSpace.toDual ℝ E).symm L) u := hrepr u
      _ ≤ inner ℝ l u := hlmax hp
  have haffineA : sSup A = F := by
    simpa [A] using haffine
  have hFu_le : F u ≤ inner ℝ l u := by
    letI : Nonempty {g // g ∈ A} := hAne.to_subtype
    rw [← congrFun haffineA u, sSup_apply]
    apply ciSup_le
    intro g
    exact hA_le g g.property
  have hleFu : inner ℝ l u ≤ F u := hsupport_le l hl
  have heq : F u = inner ℝ l u := le_antisymm hFu_le hleFu
  exact ⟨l, hl, heq, fun l' hl' => hlmax hl'⟩
```

## Proof explanation
The proof first derives the hidden fact $F(0)=0$. It applies positive homogeneity to the scalar $2>0$ and the vector $0$, obtaining

$$
F(2\cdot 0)=2F(0).
$$

After simplification this becomes $F(0)=2F(0)$, and `linarith` then gives $F(0)=0$.

Next the proof obtains continuity and lower semicontinuity. Since $F$ is convex on all of $E$, and $E$ is open, the invocation `hconv.continuousOn isOpen_univ` gives continuity of $F$ on all of $E$. The command `continuousOn_univ.mp` converts continuity on the whole space into global continuity, producing `hcont : Continuous F`. Then `hcont.lowerSemicontinuous` gives that $F$ is lower semicontinuous. Lower semicontinuity is used for the affine-supremum description of $F$ and for the separation step that produces an affine minorant.

The proof then invokes `hconv.real_univ_sSup_affine_eq hlsc`. The concrete content used here is that a convex lower semicontinuous real-valued function on the whole finite-dimensional space is the pointwise supremum of all affine continuous functions lying below it. Later the proof defines

$$
A=\{g:E\to\mathbb R \mid g\le F \text{ and } \exists L\in E\to_L[\mathbb R]\mathbb R,\ \exists c\in\mathbb R,\ g=L+c\}.
$$

The equality `haffineA : sSup A = F` records exactly this affine-supremum representation.

To show that the subdifferential at $0$ is nonempty, the proof uses `hconv.exists_affine_le_of_lt` with the value $F(0)-1$ and the point $0$. This separation theorem produces a continuous linear functional $L:E\to\mathbb R$ and a constant $c\in\mathbb R$ such that

$$
\forall x\in E,\qquad L(x)+c\le F(x).
$$

The proof discards the additional strict inequality at $0$ and keeps only this affine minorant. It then applies `riesz_mem_convexSubdifferential_of_affine_minorant` to $F$, the equality $F(0)=0$, positive homogeneity, and the affine minorant $L(x)+c\le F(x)$. The consequence visible in the proof is that this result produces a point of

$$
\partial\bigl(y\mapsto (F(y))_{\mathbb R}\bigr)(0).
$$

Hence the subdifferential at $0$ is nonempty.

The proof next shows that this subdifferential is closed. Using `mem_convexSubdifferential_iff`, membership

$$
l\in \partial\bigl(y\mapsto (F(y))_{\mathbb R}\bigr)(0)
$$

is rewritten as

$$
F(0)+\langle l,v-0\rangle\le F(v)
$$

for every $v\in E$. Therefore the subdifferential is the intersection over $v\in E$ of the sets

$$
\{l\in E \mid F(0)+\langle l,v-0\rangle\le F(v)\}.
$$

Each such set is closed because $l\mapsto F(0)+\langle l,v-0\rangle$ and the constant function $F(v)$ are continuous; this is what `apply isClosed_le` with `fun_prop` verifies. Then `isClosed_iInter` gives closedness of the whole intersection.

The proof then bounds the subdifferential. Since $E$ is finite-dimensional, `FiniteDimensional.proper ℝ E` makes $E$ a proper metric space, so closed balls are compact. In particular, the closed unit ball $\overline B(0,1)$ is compact. The continuous function $x\mapsto |F(x)|$ attains a maximum on this compact ball at some point $z$. Let

$$
B=|F(z)|.
$$

Then for every $x$ in the closed unit ball,

$$
|F(x)|\le B.
$$

Using this bound, the proof shows that every subgradient $l\in\partial F(0)$ satisfies $\|l\|\le B$. If $l=0$, this is immediate. Otherwise set

$$
q=\frac{1}{\|l\|}l.
$$

Then $\|q\|=1$, so $q$ lies in the closed unit ball. Since $l$ is a subgradient at $0$,

$$
F(0)+\langle l,q-0\rangle\le F(q).
$$

Using $F(0)=0$, this gives

$$
\langle l,q\rangle\le F(q)\le |F(q)|\le B.
$$

But

$$
\langle l,q\rangle
=
\left\langle l,\frac{1}{\|l\|}l\right\rangle
=
\frac{1}{\|l\|}\langle l,l\rangle
=
\|l\|.
$$

Therefore $\|l\|\le B$. Thus

$$
\partial\bigl(y\mapsto (F(y))_{\mathbb R}\bigr)(0)\subseteq \overline B(0,B).
$$

Since $\overline B(0,B)$ is compact and the subdifferential is closed, `of_isClosed_subset` gives that the subdifferential at $0$ is compact.

Now the proof maximizes the continuous linear functional $l\mapsto \langle l,u\rangle$ over this nonempty compact subdifferential. The compactness theorem `exists_isMaxOn` produces a point $l$ in the subdifferential such that

$$
\forall l'\in \partial\bigl(y\mapsto (F(y))_{\mathbb R}\bigr)(0),\qquad
\langle l',u\rangle\le \langle l,u\rangle.
$$

This is the maximality property required in the conclusion.

It remains to identify $F(u)$ with $\langle l,u\rangle$. First, for any subgradient $l'$ at $0$, the subgradient inequality at $u$ gives

$$
F(0)+\langle l',u-0\rangle\le F(u).
$$

Since $F(0)=0$, this becomes

$$
\langle l',u\rangle\le F(u).
$$

Applying this to the chosen maximizing subgradient $l$ gives the upper bound

$$
\langle l,u\rangle\le F(u).
$$

The reverse inequality is obtained from affine minorants. Let $A$ be the set of affine functions below $F$, as above. The proof first shows that $A$ is nonempty: the chosen subgradient $l$ gives the affine function $x\mapsto \langle l,x\rangle$, and the subgradient inequality at $0$ gives $\langle l,x\rangle\le F(x)$ for all $x$. Thus this affine function belongs to $A$.

Now take any affine minorant $g\in A$. Write

$$
g=L+c
$$

with $L$ continuous linear and $c\in\mathbb R$. Since $g\le F$, we have

$$
\forall x\in E,\qquad L(x)+c\le F(x).
$$

Evaluating at $0$ gives

$$
c=L(0)+c\le F(0)=0.
$$

The proof then applies `riesz_mem_convexSubdifferential_of_affine_minorant` to $L,c$. The visible consequences used are that it produces a subgradient $p$ at $0$ and the representation

$$
L(u)=\langle p,u\rangle,
$$

where $p$ is the Riesz vector corresponding to $L$. Therefore

$$
g(u)=L(u)+c\le L(u)=\langle p,u\rangle.
$$

Since $l$ maximizes $\langle\cdot,u\rangle$ over all subgradients at $0$, and $p$ is such a subgradient, we get

$$
\langle p,u\rangle\le \langle l,u\rangle.
$$

Hence every affine minorant $g\in A$ satisfies

$$
g(u)\le \langle l,u\rangle.
$$

Finally, the affine-supremum representation says $F=\sup A$ as functions. Evaluating at $u$ gives

$$
F(u)=\sup_{g\in A} g(u).
$$

The command `ciSup_le` applies because every $g(u)$ is at most $\langle l,u\rangle$. Therefore

$$
F(u)\le \langle l,u\rangle.
$$

Combining this with the previously obtained inequality $\langle l,u\rangle\le F(u)$ and using antisymmetry gives

$$
F(u)=\langle l,u\rangle.
$$

The final `exact` packages the chosen subgradient $l$, its membership in the subdifferential at $0$, the equality $F(u)=\langle l,u\rangle$, and the maximality property over all subgradients at $0$. This is precisely the asserted support-function representation.

