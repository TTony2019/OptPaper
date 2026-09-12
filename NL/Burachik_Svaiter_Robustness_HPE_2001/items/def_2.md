## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/def_2.lean`

## Lean statement
```lean
def extragradientStep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) (k : ℕ) : H :=
  A.x k - A.c k • A.v k
```

## Statement explanation
The declaration defines a function named `extragradientStep`. Its inputs are a type $H$, a set-valued operator $T$, an object $A$ of type `HPEIterates H T`, and a natural number $k$. The type $H$ is assumed to be a normed additive commutative group and a real inner product space, so it has addition, subtraction, a norm, real scalar multiplication, and an inner product. The operator $T$ is a set-valued operator from $H$ to $H$, and $A$ is iteration data associated with $T$. The natural number $k$ is an index.

The definition uses three components of $A$, written $A.x$, $A.c$, and $A.v$. Evaluated at $k$, these give $A.x(k)$, $A.c(k)$, and $A.v(k)$. Writing

$$
x_k=A.x(k),\qquad c_k=A.c(k),\qquad v_k=A.v(k),
$$

the definition says

$$
\operatorname{extragradientStep}(A,k)=x_k-c_kv_k.
$$

Here $c_kv_k$ is the scalar multiplication of the vector $v_k$ by the scalar $c_k$, which in this real inner product-space setting is a real scalar. The result is therefore an element of $H$. Mathematically, the extragradient step is the vector obtained from the $k$-th $x$-iterate by subtracting the $k$-th $v$-iterate scaled by the $k$-th coefficient $c$. The declaration asserts no property of $T$, no feasibility or convergence condition, and no relation among the iterates; it is purely a definition of this derived vector.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. A `def` in Lean introduces a new constant by giving its value, and the only checking required is that the right-hand side has the declared type $H$. Here the body $A.x(k)-A.c(k)A.v(k)$ is type-correct because $A.x(k)$ and the scalar multiple $A.c(k)A.v(k)$ are elements of $H$, and $H$ has subtraction from its additive group structure. The scalar multiplication is the real scalar action supplied by the real inner product-space structure on $H$.

No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or lemma is invoked. The source itself says `-- No separate proof part.` Thus the mathematical content is exhausted by the definitional equality: for every $A$ of type `HPEIterates H T` and every $k\in\mathbb{N}$, unfolding `extragradientStep` gives exactly

$$
A.x(k)-A.c(k)A.v(k).
$$

