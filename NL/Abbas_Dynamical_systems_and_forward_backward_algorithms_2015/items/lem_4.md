## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_4.lean`

## Lean statement
```lean
theorem operator_constant_on_solution_set {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (beta : ℝ) (S : Set H)
    (hbeta : 0 < beta)
    (hcoco : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (hBmax : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator)
    (hS : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∀ z ∈ S, ∀ w ∈ S, B z = B w
```

## Statement explanation
The declaration is a theorem about a real inner product space $H$. It assumes $H$ is a normed additive commutative group equipped with a real inner product. The function $\Phi$ has type $H \to \mathrm{Set.Ioi}(\bot:\mathrm{EReal})$, so its values are extended real numbers strictly larger than $-\infty$; equivalently, $\Phi$ takes values in $(-\infty,+\infty]$. The hypothesis that $\Phi$ belongs to `ERealFunction.gammaZero H`, written here as $\Phi \in \Gamma_0(H)$, places $\Phi$ in the $\Gamma_0$ class. The cited result `isProper_of_mem_gammaZero` will be used to conclude that the coerced function

$$
x \mapsto (\Phi(x):\mathrm{EReal})
$$

is proper.

The theorem also assumes a single-valued operator $B:H\to H$, a real number $\beta$ with $0<\beta$, and a subset $S\subseteq H$. The hypothesis `hcoco` says that $B$ is $\beta$-cocoercive on all of $H$, i.e. on `Set.univ`. The concrete consequence used in the proof is that for arbitrary $z,w\in H$, after commuting the real inner product, one has

$$
\beta\,\|B z-B w\|^2 \le \langle B z-B w,z-w\rangle .
$$

The hypothesis `hBmax` says that the set-valued operator induced by $B$, namely $x\mapsto\{B x\}$, is maximal monotone. This assumption is present in the statement, but it is not invoked anywhere in the displayed proof.

The set $S$ is characterized by

$$
z\in S \quad\Longleftrightarrow\quad -B z\in \partial \Phi(z),
$$

where $\partial \Phi(z)$ is the subdifferential of the coerced extended-real function $x\mapsto(\Phi(x):\mathrm{EReal})$. Concretely, $u\in\partial \Phi(z)$ means that for every $y\in H$,

$$
\langle y-z,u\rangle+\Phi(z)\le \Phi(y),
$$

with the inequality interpreted in $\mathrm{EReal}$. Thus $S$ is the solution set of the inclusion

$$
0\in B z+\partial \Phi(z).
$$

The conclusion of the theorem is that $B$ is constant on this solution set: for every $z\in S$ and every $w\in S$, one has $B z=B w$.

## Lean proof
```lean
by
  intro z hz w hw
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := (hS z).1 hz
  have hwsub : -B w ∈ ERealFunction.subdifferential Phi w := (hS w).1 hw
  have hmono := ERealFunction.isMonotone_subdifferential
    (fun x : H => (Phi x : EReal))
    (ERealFunction.isProper_of_mem_gammaZero hPhi)
    (-B z) hzsub (-B w) hwsub
  have hsubmono : inner ℝ (B z - B w) (z - w) ≤ 0 := by
    rw [show (-B z) - (-B w) = -(B z - B w) by abel, inner_neg_left] at hmono
    linarith
  have hc := hcoco.ineq
    (⟨z, Set.mem_univ z⟩ : Set.univ)
    (⟨w, Set.mem_univ w⟩ : Set.univ)
  have hcobound : beta * ‖B z - B w‖ ^ 2 ≤
      inner ℝ (B z - B w) (z - w) := by
    simpa [real_inner_comm] using hc
  have hnonneg : 0 ≤ beta * ‖B z - B w‖ ^ 2 :=
    mul_nonneg hbeta.le (sq_nonneg _)
  have hprodzero : beta * ‖B z - B w‖ ^ 2 = 0 :=
    le_antisymm (hcobound.trans hsubmono) hnonneg
  have hnormzero : ‖B z - B w‖ = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hprodzero).resolve_left hbeta.ne')
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
```

## Proof explanation
The proof begins with `intro z hz w hw`. This starts the proof of the universally quantified conclusion by fixing an arbitrary $z\in S$ with hypothesis $hz$, and an arbitrary $w\in S$ with hypothesis $hw$. The goal is now to prove $B z=B w$.

Next, the proof uses the characterization of $S$ to obtain the two subgradient inclusions

$$
-B z\in \partial \Phi(z),\qquad -B w\in \partial \Phi(w).
$$

The lines `have hzsub ... := (hS z).1 hz` and `have hwsub ... := (hS w).1 hw` extract these from the forward implications of the equivalence in `hS`.

The proof then invokes the cited theorem `isMonotone_subdifferential`. That theorem states that if $F:H\to\mathrm{EReal}$ is proper, then its subdifferential operator $\partial F$ is monotone. In concrete terms, whenever $u\in\partial F(x)$ and $v\in\partial F(y)$, monotonicity gives

$$
0\le \langle u-v,x-y\rangle .
$$

Here the theorem is applied to the coerced function

$$
F(x)=(\Phi(x):\mathrm{EReal}).
$$

The properness hypothesis required by `isMonotone_subdifferential` is supplied by the cited lemma `isProper_of_mem_gammaZero`, which says that membership of $\Phi$ in $\Gamma_0(H)$ implies that the coerced function $x\mapsto(\Phi(x):\mathrm{EReal})$ is proper. Applying the monotonicity theorem to

$$
x=z,\qquad y=w,\qquad u=-B z,\qquad v=-B w
$$

gives

$$
0\le \left\langle (-B z)-(-B w),\, z-w\right\rangle .
$$

The proof next simplifies the left-hand difference. The command `rw [show ... by abel, inner_neg_left] at hmono` first rewrites

$$
(-B z)-(-B w)=-(B z-B w)
$$

using the algebraic identity proved by `abel`, and then applies `inner_neg_left`, which says

$$
\langle -a,b\rangle=-\langle a,b\rangle .
$$

Thus the monotonicity inequality becomes

$$
0\le -\langle B z-B w,z-w\rangle .
$$

The tactic `linarith` then rearranges this to

$$
\langle B z-B w,z-w\rangle\le 0 .
$$

This is the inequality `hsubmono`.

Next, the proof uses the cocoercivity hypothesis `hcoco`. The expression `hcoco.ineq` applies the cocoercivity condition to the two points of the subtype `Set.univ` corresponding to $z$ and $w$. Since `Set.univ` contains every point of $H$, this is the cocoercivity inequality for $z$ and $w$. The command `simpa [real_inner_comm] using hc` converts it into the form

$$
\beta\,\|B z-B w\|^2 \le \langle B z-B w,z-w\rangle .
$$

Here `real_inner_comm` is the symmetry of the real inner product,

$$
\langle a,b\rangle=\langle b,a\rangle,
$$

which allows the order of the two inner-product arguments to be swapped.

The proof then records that

$$
0\le \beta\,\|B z-B w\|^2 .
$$

This is proved by `mul_nonneg hbeta.le (sq_nonneg _)`: the positivity hypothesis $0<\beta$ gives $0\le\beta$, and the square $\|B z-B w\|^2$ is nonnegative.

Now the two inequalities are combined. The term `hcobound.trans hsubmono` chains

$$
\beta\,\|B z-B w\|^2
\le \langle B z-B w,z-w\rangle
\le 0 .
$$

Together with the previously established reverse inequality

$$
0\le \beta\,\|B z-B w\|^2,
$$

the command `le_antisymm` yields

$$
\beta\,\|B z-B w\|^2=0 .
$$

From this product being zero, the proof extracts $\|B z-B w\|^2=0$. The command `mul_eq_zero.mp hprodzero` says that a product is zero only if one of its factors is zero, so either $\beta=0$ or $\|B z-B w\|^2=0$. The factor $\beta$ is nonzero because $\beta>0$, and `resolve_left hbeta.ne'` rules out the possibility $\beta=0$. Hence

$$
\|B z-B w\|^2=0.
$$

Then `sq_eq_zero_iff.mp` converts a squared real number equal to zero into the number itself being zero, so

$$
\|B z-B w\|=0.
$$

Finally, `norm_eq_zero.mp` converts zero norm into the vector being zero:

$$
B z-B w=0.
$$

Then `sub_eq_zero.mp` converts this difference equality into

$$
B z=B w.
$$

The final `exact` closes the goal with this equality. The maximal monotonicity hypothesis `hBmax` is not used in this proof; the argument relies only on the monotonicity of the subdifferential of the proper convex function $x\mapsto(\Phi(x):\mathrm{EReal})$ and on the cocoercivity of $B$.

