## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/def_2.lean`

## Lean statement
```lean
theorem resolvent_of_maximal_monotone
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∀ u : H, ∃! z : H, u ∈ A.identityAddScaled lambda z) ∧
      ∃ J : H → H, (∀ u : H, J u ∈ J[(lambda • A)] u) ∧
        LipschitzWith 1 J ∧ ∀ z : H, J z = z ↔ 0 ∈ A z
```

## Statement explanation
Let $H$ be the ambient space on which the set-valued operator acts, with the algebraic and topological structure supplied by the surrounding Lean context. The declaration concerns a set-valued operator $A : H \rightrightarrows H$, a hypothesis $hA$ that $A$ is maximal monotone, a real number $\lambda$, and the hypothesis $h\lambda : 0 \lt  \lambda$.

The operator $`A.\mathrm{identityAddScaled}\,\lambda`$, written mathematically as$I+\lambda A$, is defined by

```math
(I+\lambda A)(z)=\{\, z+\lambda a \mid a\in A(z) \,\}.
```

Its resolvent is the inverse of $I+\lambda A$; in the Lean statement this resolvent is denoted by the resolvent notation `J[(lambda • A)]`, i.e. the resolvent of the operator $\lambda A$.

The theorem concludes the conjunction of two statements.

First, for every $u\in H$, there is a unique $z\in H$ such that

$$
u\in (I+\lambda A)(z).
$$

Equivalently, the resolvent equation $u\in z+\lambda A(z)$ has a unique solution $z$ for every right-hand side $u$. This is the unique solvability of the resolvent of $\lambda A$.

Second, there exists a single-valued map $J:H\to H$ such that:

- for every $u\in H$, $J(u)$ lies in the resolvent of $\lambda A$ at $u$, written in Lean as $J u\in J[(\lambda\cdot A)]u$. By definition of the resolvent, this means

$$
u\in (I+\lambda A)(J(u)),
$$

  or equivalently $u\in J(u)+\lambda A(J(u))$. Thus $J$ is a selection of the resolvent.
- $J$ is $1$-Lipschitz, i.e. nonexpansive: the Lean assertion $`\mathrm{LipschitzWith}\,1\,J`$means that the usual Lipschitz condition with constant$1$holds for$J$.
- the fixed points of $J$ are exactly the zeros of $A$:

$$
\forall z\in H,\qquad J(z)=z \iff 0\in A(z).
$$

So the declaration says that for a maximal monotone operator $A$ and a positive step size $\lambda$, the resolvent of $\lambda A$ is single-valued and uniquely defined, and it admits a nonexpansive selection whose fixed points are precisely the points $z$ with $0\in A(z)$.

## Lean proof
```lean
by
  classical
  have hunique : ∀ u : H, ∃! z : H, u ∈ A.identityAddScaled lambda z :=
    fun u => identityAddScaled_existsUnique_of_maximal_monotone A hA hlambda u
  let J : H → H := fun u => Classical.choose (hunique u)
  have hJ_identity : ∀ u : H, u ∈ A.identityAddScaled lambda (J u) := by
    intro u
    exact (Classical.choose_spec (hunique u)).1
  have hJ : ∀ u : H, J u ∈ J[(lambda • A)] u := by
    intro u
    exact (mem_resolvent_smul_iff A lambda u (J u)).mpr (hJ_identity u)
  refine ⟨hunique, J, hJ, resolvent_selection_lipschitz A hA hlambda J hJ, ?_⟩
  intro z
  constructor
  · intro hfix
    rcases hJ_identity z with ⟨a, ha, hza⟩
    have hscaled : lambda • a = 0 := by
      rw [hfix] at hza ha
      apply add_left_cancel (a := z)
      simpa using hza.symm
    have ha_zero : a = 0 := (smul_eq_zero.mp hscaled).resolve_left hlambda.ne'
    simpa [hfix, ha_zero] using ha
  · intro hzero
    have hz : z ∈ A.identityAddScaled lambda z := ⟨0, hzero, by simp⟩
    exact (hunique z).unique (hJ_identity z) hz
```

## Proof explanation
The proof begins with `classical`, because it uses classical choice to select the unique solution of each resolvent equation.

First, the proof invokes the cited result `identityAddScaled_existsUnique_of_maximal_monotone`. Its mathematical content is the following: if $A$ is maximal monotone and $\lambda\gt 0$, then for every $u\in H$ there exists a unique $z\in H$ such that

```math
u\in A.\mathrm{identityAddScaled}\,\lambda\,z,
```

i.e. $u\in (I+\lambda A)(z)$. The proof applies this result to the given $A$, $hA$, $\lambda$, $h\lambda$, and to an arbitrary $u$, obtaining exactly

$$
\forall u\in H,\ \exists! z\in H,\ u\in (I+\lambda A)(z).
$$

This is recorded as `hunique` and is precisely the first conjunct of the theorem.

Next, the proof defines a function $J:H\to H$ by choosing, for each $u$, the unique element supplied by `hunique u`:

$$
J(u)=\text{the unique }z\text{ such that }u\in (I+\lambda A)(z).
$$

In Lean this is done by `Classical.choose (hunique u)`. The proof then records the defining property of the chosen element:

$$
\forall u\in H,\qquad u\in (I+\lambda A)(J(u)).
$$

This is `hJ_identity`. It follows from `Classical.choose_spec (hunique u)`: the specification of classical choice says that the chosen element satisfies the property used in the existence proof, and the first component of that specification gives the membership statement.

To show that $J$ is a selection of the resolvent of $\lambda A$, the proof uses `mem_resolvent_smul_iff`. That lemma states that for any set-valued operator $A$, any scalar $\rho$, and any $x,y\in H$,

```math
y\in J[(\rho\cdot A)]x \iff x\in A.\mathrm{identityAddScaled}\,\rho\,y.
```

In other words, $y$ belongs to the resolvent of $\rho A$ at $x$ exactly when $x\in (I+\rho A)(y)$. Taking $\rho=\lambda$, $x=u$, and $y=J(u)$, the right-hand side is exactly `hJ_identity u`, namely $u\in (I+\lambda A)(J(u))$. The `.mpr` direction of the equivalence therefore gives

$$
J(u)\in J[(\lambda\cdot A)]u
$$

for every $u$. This is recorded as `hJ`. Thus $J$ is a single-valued selection of the resolvent.

The proof then assembles the existential part of the theorem with `refine`. The witness for the existential quantifier is the function $J$. The first property required is `hJ`, which says that $J$ is a resolvent selection. The second property, $1$-Lipschitzness, is supplied by the cited theorem `resolvent_selection_lipschitz`. Its content is: if $A$ is maximal monotone, $\lambda\gt 0$, and $J:H\to H$ satisfies $J(u)\in J[(\lambda\cdot A)]u$ for every $u$, then $J$ is $1$-Lipschitz. Applied to the present $A$, $hA$, $h\lambda$, $J$, and `hJ`, it gives $`\mathrm{LipschitzWith}\,1\,J`$. Mathematically, this is the nonexpansiveness of the resolvent selection.

Only the fixed-point characterization remains. The proof fixes an arbitrary $z\in H$ with `intro z` and splits the biconditional into two implications using `constructor`.

For the forward direction, assume $J(z)=z$, recorded as `hfix`. From `hJ_identity z`, we know

$$
z\in (I+\lambda A)(J(z)).
$$

Unfolding the definition of $I+\lambda A$, this means that there exists some $a\in A(J(z))$ and an equality expressing that $J(z)+\lambda a=z$ (equivalently $z=J(z)+\lambda a$). The proof extracts such an $a$ and the equality by `rcases hJ_identity z with ⟨a, ha, hza⟩`. Then it rewrites $J(z)$ to $z$ in both the equality and the membership, using `rw [hfix] at hza ha`. After this substitution, one has $a\in A(z)$ and an equality between $z+\lambda a$ and $z$ (up to symmetry).

The proof then cancels $z$. It uses `apply add_left_cancel (a := z)`, which reduces the goal $\lambda a=0$ to an equality with $z$ added on both sides. The resulting equality is closed by `simpa` using the rewritten equality. Hence

$$
\lambda a=0.
$$

The proof now applies `smul_eq_zero.mp hscaled`. This theorem says that in a vector space, $\lambda a=0$ implies $\lambda=0$ or $a=0$. Since $h\lambda$ gives $0\lt \lambda$, in particular $\lambda\neq 0$, the disjunct $\lambda=0$ is impossible. The tactic `resolve_left` uses this to conclude $a=0$. Therefore the earlier membership $a\in A(z)$ becomes $0\in A(z)$. The final `simpa [hfix, ha_zero] using ha` rewrites the extracted membership into the desired conclusion.

For the backward direction, assume $0\in A(z)$, recorded as `hzero`. The proof constructs the membership

$$
z\in (I+\lambda A)(z)
$$

by taking the witness $0$. Indeed, $0\in A(z)$ is exactly `hzero`, and the required equality $z+\lambda\cdot 0=z$ is discharged by `simp`. This is recorded as `hz`.

Now observe that $J(z)$ also satisfies the same resolvent equation for the same input $z$, by `hJ_identity z`:

$$
z\in (I+\lambda A)(J(z)).
$$

Meanwhile `hz` gives

$$
z\in (I+\lambda A)(z).
$$

But `hunique z` states that there is a unique solution $w$ to the equation $z\in (I+\lambda A)(w)$. Since both $J(z)$ and $z$ are such solutions, uniqueness forces them to be equal. The proof invokes `(hunique z).unique (hJ_identity z) hz`, which yields $J(z)=z$. This completes the fixed-point equivalence and therefore the whole theorem.

