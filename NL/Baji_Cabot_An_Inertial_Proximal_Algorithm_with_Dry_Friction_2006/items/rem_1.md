## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/rem_1.lean`

## Lean statement
```lean
theorem rem_2_1 (g : H → ℝ) (hg_conv : ConvexOn ℝ Set.univ g) (hg_lsc : LowerSemicontinuous g) :
    ∀ x,
      PhiA (subderivative fun y => (g y : EReal)) x ≥
        ((g x - g 0 : ℝ) : EReal) ∧
      ((g x - g 0 : ℝ) : EReal) ≥
        supportFunction ((subderivative fun y => (g y : EReal)) (0 : H)) x
```

## Statement explanation
The declaration `rem_2_1` is stated for an ambient type $H$, a real-valued function $g:H\to\mathbb R$, a hypothesis `hg_conv` saying that $g$ is convex over $\mathbb R$ on the whole space, and a hypothesis `hg_lsc` saying that $g$ is lower semicontinuous. Convexity on `Set.univ` means the usual inequality

$$
g(tx+(1-t)y)\le t g(x)+(1-t)g(y)
$$

for all $x,y\in H$ and $t\in[0,1]$. Lower semicontinuity means that, for example, every superlevel set $\{x:g(x)>a\}$ is open, equivalently every sublevel set $\{x:g(x)\le a\}$ is closed.

The conclusion is that for every $x\in H$, two inequalities hold. Let

$$
f:H\to\overline{\mathbb R},\qquad f(y)=(g(y):\overline{\mathbb R}),
$$

be the extended-real-valued version of $g$, and let

$$
A=\partial f
$$

be its subderivative operator. The expression `subderivative fun y => (g y : EReal)` is exactly this operator $A$, and `(subderivative ... ) (0 : H)` is the set $A(0)=\partial f(0)$ of subgradients at the origin. The support function of a set $S$ is written $\sigma_S$, so

$$
\sigma_{A(0)}(x)
$$

is the support function of the subdifferential at $0$, evaluated at $x$.

The first conjunct states

$$
((g(x)-g(0)):\overline{\mathbb R}) \le \Phi_A(x),
$$

where $\Phi_A$ is the operator-level function named `PhiA` in the library. The second conjunct states

$$
\sigma_{A(0)}(x) \le ((g(x)-g(0)):\overline{\mathbb R}).
$$

Thus, taken together, the theorem says that the real increment $g(x)-g(0)$, coerced into the extended reals, is sandwiched between the support function of the subdifferential at $0$ and the $\Phi_A$-value of the whole subdifferential operator at $x$:

$$
\sigma_{\partial f(0)}(x)
\le ((g(x)-g(0)):\overline{\mathbb R})
\le \Phi_{\partial f}(x).
$$

The convexity and lower-semicontinuity hypotheses are part of the statement, but the proof body does not use them: the two helper lemmas invoked are stated for arbitrary $g:H\to\mathbb R$ and arbitrary $x:H$.

## Lean proof
```lean
by
  intro x
  constructor
  · exact rem21_subderivative_phi_lower g x
  · exact rem21_support_subderivative_zero_upper g x
```

## Proof explanation
The proof is a short structural argument.

1. The goal after the theorem statement is

$$
\forall x,\; P(x)\land Q(x),
$$

where $P(x)$ is the first inequality and $Q(x)$ is the second inequality. The tactic `intro x` introduces an arbitrary $x:H$ and reduces the goal to proving the conjunction $P(x)\land Q(x)$ for that fixed $x$.

2. The tactic `constructor` splits the conjunction $P(x)\land Q(x)$ into two separate goals: first prove $P(x)$, then prove $Q(x)$.

3. For the first conjunct, the goal is

$$
\Phi_A(x)\ge ((g(x)-g(0)):\overline{\mathbb R}),
$$

where $A=\partial f$ and $f(y)=(g(y):\overline{\mathbb R})$. In Lean, $a\ge b$ is notation for $b\le a$, so this goal is the same as

$$
((g(x)-g(0)):\overline{\mathbb R})\le \Phi_A(x).
$$

The proof then uses

$$
\texttt{rem21\_subderivative\_phi\_lower }g\ x.
$$

Specialized to the current $g$ and $x$, that helper lemma says exactly

$$
((g(x)-g(0)):\overline{\mathbb R})
\le
\Phi_A(x),
$$

where $A$ is the subderivative of $y\mapsto (g(y):\overline{\mathbb R})$. This lemma is stated without any convexity or lower-semicontinuity assumption on $g$. It supplies the lower bound for $\Phi_A(x)$ by the increment $g(x)-g(0)$. The tactic `exact` closes the first goal because the lemma’s conclusion is precisely the required inequality, with the only difference being the notation $\ge$ for the reversed order.

4. For the second conjunct, the goal is

$$
((g(x)-g(0)):\overline{\mathbb R})
\ge
\sigma_{A(0)}(x).
$$

Again, $\ge$ is notation for the reverse order, so this goal is

$$
\sigma_{A(0)}(x)
\le
((g(x)-g(0)):\overline{\mathbb R}).
$$

The proof uses

$$
\texttt{rem21\_support\_subderivative\_zero\_upper }g\ x.
$$

Specialized to the current $g$ and $x$, this helper lemma states

$$
\sigma_{A(0)}(x)
\le
((g(x)-g(0)):\overline{\mathbb R}),
$$

where $A(0)=\partial f(0)$ is the subdifferential at the origin of the extended-real function $f(y)=(g(y):\overline{\mathbb R})$. Mathematically, this is the usual subgradient estimate at $0$: if $\xi\in\partial f(0)$, then the subgradient inequality at $0$ gives

$$
g(x)\ge g(0)+\langle \xi,x\rangle,
$$

hence

$$
\langle \xi,x\rangle\le g(x)-g(0).
$$

Taking the supremum over all $\xi\in\partial f(0)$ yields the stated support-function inequality. The helper lemma records exactly this upper bound, again without needing convexity or lower semicontinuity. The tactic `exact` closes the second goal because the lemma’s conclusion is exactly the required inequality after rewriting $\ge$ as $\le$.

No `rw`, `simp`, or `linarith` is used. The hypotheses `hg_conv` and `hg_lsc` are not referenced in the proof body; the two inequalities are obtained directly from the two private helper lemmas, which are more general than the theorem’s stated assumptions.

