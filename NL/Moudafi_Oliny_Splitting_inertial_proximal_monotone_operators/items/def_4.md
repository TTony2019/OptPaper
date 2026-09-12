## Source file
`Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators/items/def_4.lean`

## Lean statement
```lean
theorem enlargement_monotone (T : SetValuedOperator H H) {ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂) (x : H) : enlargement T ε₁ x ⊆ enlargement T ε₂ x
```

## Statement explanation
The theorem `enlargement_monotone` states a monotonicity property of the \(\epsilon\)-enlargement of a set-valued operator. Here \(H\) is the ambient real inner-product space in which the real inner product
\[
\langle \cdot , \cdot \rangle_{\mathbb R}
\]
is defined, and \(T\) is a set-valued operator from \(H\) to \(H\): for each \(y \in H\), the value \(T y\) is a subset of \(H\). For a real parameter \(\epsilon\), the enlargement is defined by
\[
(\operatorname{enlargement} T \epsilon)(x)
=
\left\{
v \in H :
\forall y,\ \forall u \in T y,\ 
-\epsilon \le \langle u-v, y-x\rangle_{\mathbb R}
\right\}.
\]
Thus \((\operatorname{enlargement} T \epsilon)(x)\) is the set of all vectors \(v\) such that, for every point \(y\) and every \(u\) in the value \(T y\), the real inner product \(\langle u-v, y-x\rangle_{\mathbb R}\) is bounded below by \(-\epsilon\). The declaration takes real numbers \(\epsilon_1,\epsilon_2\) satisfying
\[
\epsilon_1 \le \epsilon_2
\]
and an arbitrary point \(x \in H\), and concludes
\[
(\operatorname{enlargement} T \epsilon_1)(x)
\subseteq
(\operatorname{enlargement} T \epsilon_2)(x).
\]
In words: if \(\epsilon_1\) is no larger than \(\epsilon_2\), then the \(\epsilon_1\)-enlargement at any point is contained in the \(\epsilon_2\)-enlargement at that same point. The reason is that increasing \(\epsilon\) makes the lower bound \(-\epsilon\) smaller, hence makes the defining inequality weaker, so the corresponding enlargement set can only grow. No monotonicity assumption on \(T\) itself is needed for this statement.

## Lean proof
```lean
by
  intro v hv
  rw [enlargement, Set.mem_setOf_eq] at hv ⊢
  intro y u hu
  have h := hv y u hu
  linarith
```

## Proof explanation
The proof begins with `intro v hv`. Since the goal is a subset inclusion
\[
(\operatorname{enlargement} T \epsilon_1)(x)
\subseteq
(\operatorname{enlargement} T \epsilon_2)(x),
\]
Lean expands this as a universal statement over elements of \(H\). The command introduces an arbitrary \(v\) and assumes
\[
hv : v \in (\operatorname{enlargement} T \epsilon_1)(x).
\]
The goal is now to show
\[
v \in (\operatorname{enlargement} T \epsilon_2)(x).
\]

Next, `rw [enlargement, Set.mem_setOf_eq] at hv ⊢` unfolds the definition of `enlargement` and converts membership in a set-builder into the corresponding predicate, both in the hypothesis `hv` and in the current goal. After this rewrite, `hv` says
\[
\forall y,\ \forall u \in T y,\ 
-\epsilon_1 \le \langle u-v, y-x\rangle_{\mathbb R},
\]
while the goal says
\[
\forall y,\ \forall u \in T y,\ 
-\epsilon_2 \le \langle u-v, y-x\rangle_{\mathbb R}.
\]
The lemma `Set.mem_setOf_eq` is the standard set-membership equivalence
\[
v \in \{w \mid P(w)\} \longleftrightarrow P(v).
\]
Here it turns membership in the enlargement set into the explicit universal inequality that defines that set.

The command `intro y u hu` then fixes arbitrary \(y\), arbitrary \(u\), and assumes
\[
hu : u \in T y.
\]
The goal has now become the single inequality
\[
-\epsilon_2 \le \langle u-v, y-x\rangle_{\mathbb R}.
\]

The line `have h := hv y u hu` applies the hypothesis `hv` to these same \(y\), \(u\), and \(hu\). Since `hv` is universal over all \(y\) and all \(u \in T y\), it yields
\[
h : -\epsilon_1 \le \langle u-v, y-x\rangle_{\mathbb R}.
\]

Finally, `linarith` proves the desired inequality by linear arithmetic over the real numbers. It uses the hypothesis
\[
h\epsilon : \epsilon_1 \le \epsilon_2
\]
and the inequality
\[
h : -\epsilon_1 \le \langle u-v, y-x\rangle_{\mathbb R}.
\]
Negating \(\epsilon_1 \le \epsilon_2\) gives
\[
-\epsilon_2 \le -\epsilon_1,
\]
and combining this with \(-\epsilon_1 \le \langle u-v, y-x\rangle_{\mathbb R}\) gives
\[
-\epsilon_2 \le \langle u-v, y-x\rangle_{\mathbb R}.
\]
The inner-product expression is treated as an opaque real number for the purposes of this linear arithmetic step. Since \(y\) and \(u \in T y\) were arbitrary, the universal goal is proved, so \(v\) belongs to \((\operatorname{enlargement} T \epsilon_2)(x)\). Since \(v\) was an arbitrary element of \((\operatorname{enlargement} T \epsilon_1)(x)\), the desired subset inclusion follows.

