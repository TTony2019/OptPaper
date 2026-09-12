## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_thm_5.lean`

## Lean statement
```lean
abbrev ext_thm_5 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X) (L : ℝ) (hL : 0 < L) (hlip : ∀ x y : X, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (x₀ : X) :
    ∃! x : ℝ → X, (Differentiable ℝ x ∧ Continuous (deriv x) ∧
      ∀ t : ℝ, deriv x t = F (x t) ∧ x 0 = x₀) :=
  exists_unique_global_solution_of_lipschitz F L hL hlip x₀
```

## Statement explanation
The declaration `ext_thm_5` is an abbreviation. It has an implicit type parameter $X$ together with the typeclass assumptions `NormedAddCommGroup X`, `NormedSpace ℝ X`, and `CompleteSpace X`. These make $X$ a complete real normed vector space, i.e. a real Banach space. It then takes:

- a map $F : X \to X$;
- a real number $L$, with hypothesis $hL : 0 < L$;
- a global Lipschitz hypothesis

  $$
  hlip : \forall x,y \in X,\quad \|F(x)-F(y)\| \le L\,\|x-y\|;
  $$

- an initial point $x_0 \in X$.

The conclusion is the unique existence of a function $x : \mathbb{R} \to X$ such that $x$ is differentiable, its derivative is continuous, and for every real $t$,

$$
\operatorname{deriv} x(t) = F(x(t)) \quad\text{and}\quad x(0)=x_0.
$$

More precisely, the Lean statement is

$$
\exists! x : \mathbb{R} \to X,\quad
\operatorname{Differentiable}_{\mathbb{R}}(x)
\ \wedge\
\operatorname{Continuous}(\operatorname{deriv} x)
\ \wedge\
\forall t \in \mathbb{R},\ 
\operatorname{deriv} x(t)=F(x(t)) \ \wedge\ x(0)=x_0 .
$$

As written, the second conjunct $x(0)=x_0$ lies inside the scope of the universal quantifier over $t$. Since it does not depend on $t$, this is equivalent to requiring the differential equation for all $t \in \mathbb{R}$ together with the single initial condition $x(0)=x_0$.

Thus, mathematically, the declaration states that for a globally Lipschitz vector field $F$ with positive Lipschitz constant $L$ on a complete real normed space $X$, there exists exactly one globally defined $C^1$ curve $x : \mathbb{R} \to X$ solving the ordinary differential equation

$$
x'(t)=F(x(t))
$$

with initial condition $x(0)=x_0$. “Global” here means the solution is defined on all of $\mathbb{R}$, not merely on a local interval.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate tactic proof. The declaration is an `abbrev`, and its body is the single term

$$
\texttt{exists\_unique\_global\_solution\_of\_lipschitz } F\ L\ hL\ hlip\ x_0 .
$$

That is, the claimed unique-existence statement is obtained by applying the imported result `exists_unique_global_solution_of_lipschitz` to the vector field $F$, the constant $L$, the proof $hL$ that $L>0$, the proof $hlip$ that $F$ is globally Lipschitz with constant $L$, and the initial point $x_0$.

The visible consequence of that imported result, specialized to these arguments, is exactly the displayed unique existence of a differentiable function $x : \mathbb{R} \to X$ whose derivative is continuous and which satisfies

$$
\operatorname{deriv} x(t)=F(x(t))
$$

for all $t \in \mathbb{R}$, together with $x(0)=x_0$. The hypotheses $hL$ and $hlip$ supply precisely the positivity and Lipschitz assumptions required for that result to produce this conclusion. No `intro`, `rw`, `simp`, `exact`, `linarith`, or other tactic steps occur, because there is no proof script to analyze. Since `ext_thm_5` is an abbreviation, it is definitionally transparent: using it unfolds to the imported theorem applied to $F,L,hL,hlip,x_0$, so it adds no new assumptions and no new conclusions beyond that unique global solution property.

