## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_def_1.lean`

## Lean statement
```lean
def IsCriticalPoint {H : Type*} [Zero H] (gradΦ : H → H) (a : H) : Prop := gradΦ a = 0
```

## Statement explanation
The declaration introduces a predicate named `IsCriticalPoint`. It is parameterized by an arbitrary type $H$ carrying a distinguished zero element, supplied by the typeclass `Zero H`; by a function

$$
\mathrm{grad}\Phi : H \to H,
$$

named `gradΦ`; and by a point

$$
a : H.
$$

The definition returns a proposition, so for fixed $\mathrm{grad}\Phi$ and $a$, the statement

$$
\mathrm{IsCriticalPoint}(\mathrm{grad}\Phi,a)
$$

is defined to mean

$$
\mathrm{grad}\Phi(a) = 0_H,
$$

where $0_H$ is the zero element of $H$.

Mathematically, the definition says that $a$ is a critical point of the map $\mathrm{grad}\Phi$ exactly when the value of that map at $a$ is zero. The name `gradΦ` suggests the intended reading that $\mathrm{grad}\Phi$ is the gradient of a function $\Phi$, so that the condition is the usual vanishing-gradient condition

$$
\nabla \Phi(a)=0.
$$

Formally, however, the Lean definition only requires $\mathrm{grad}\Phi$ to be an arbitrary function $H \to H$; it does not assume that $\mathrm{grad}\Phi$ comes from a potential, nor does it assert that any critical point exists. It only defines when a given point $a$ has that property.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration kind is `def`, so Lean is not proving a proposition but introducing the name `IsCriticalPoint` and defining it to be the equality

$$
\mathrm{grad}\Phi(a)=0_H.
$$

Thus the entire mathematical content is definitional: the expression

$$
\mathrm{IsCriticalPoint}(\mathrm{grad}\Phi,a)
$$

is definitionally equal to

$$
\mathrm{grad}\Phi(a)=0_H.
$$

Later arguments using this definition can unfold or rewrite `IsCriticalPoint gradΦ a` into the equality `gradΦ a = 0`, or conversely use that equality to conclude `IsCriticalPoint gradΦ a`.

No named theorem, lemma, local result, or imported fact is invoked. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, because there is no proof script. The only role of the typeclass assumption `Zero H` is to provide the symbol $0_H$ appearing on the right-hand side of the defining equality.

