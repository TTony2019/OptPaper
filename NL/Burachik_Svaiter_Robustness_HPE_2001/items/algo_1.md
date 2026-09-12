## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/algo_1.lean`

## Lean statement
```lean
structure HPEIterates (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) where
  x : ℕ → H
  y : ℕ → H
  v : ℕ → H
  c : ℕ → ℝ
  δ : ℕ → ℝ
  σ : ℕ → ℝ
  α : ℕ → ℝ
  ε : ℕ → ℝ
  c_pos : ∀ k, 0 < c k
  δ_nonneg : ∀ k, 0 ≤ δ k
  σ_nonneg : ∀ k, 0 ≤ σ k
  α_nonneg : ∀ k, 0 ≤ α k
  ε_nonneg : ∀ k, 0 ≤ ε k
  enlargement_mem : ∀ k, v k ∈ epsilonEnlargement T (ε k) (ε_nonneg k) (y k)
  residual_bound : ∀ k,
    ‖c k • v k + y k - x k‖ ^ 2 + 2 * c k * ε k ≤
      δ k + (σ k) ^ 2 * ‖y k - x k‖ ^ 2
  update_error : ∀ k, ‖x (k + 1) - (x k - c k • v k)‖ ≤ α k
  summable_delta : Summable δ
  summable_alpha : Summable α
  sigma_bound : ∃ σbar, 0 < σbar ∧ σbar < 1 ∧ ∀ k, 0 < σ k ∧ σ k ≤ σbar
  c_lower_bound : ∃ cbar, 0 < cbar ∧ ∀ k, cbar ≤ c k
```

## Statement explanation
The declaration introduces a structure named `HPEIterates`. It has two parameters: a type $H$, equipped with a normed additive commutative group structure and with the structure of a real inner product space, and a term $T$ of type `SetValuedOperator H H`. The source does not define `SetValuedOperator` here, so the declaration treats $T$ as a set-valued operator from $H$ to $H$ to which an epsilon-enlargement is applied. Because $H$ is a real inner product space and a normed group, it supports addition, subtraction, real scalar multiplication, and the norm $`\|\cdot\|`$.

An inhabitant of `HPEIterates H T` consists of eight sequences:

$$
x : \mathbb N \to H,\qquad y : \mathbb N \to H,\qquad v : \mathbb N \to H,
$$

and

$$
c : \mathbb N \to \mathbb R,\qquad \delta : \mathbb N \to \mathbb R,\qquad
\sigma : \mathbb N \to \mathbb R,\qquad \alpha : \mathbb N \to \mathbb R,\qquad
\varepsilon : \mathbb N \to \mathbb R.
$$

Thus $x_k$, $y_k$, and $v_k$ are vectors in $H$, while $c_k$, $\delta_k$, $\sigma_k$, $\alpha_k$, and $\varepsilon_k$ are real numbers.

The structure also requires the following properties.

- Positivity and nonnegativity for every index $k$:

$$
c_k > 0,\qquad \delta_k \ge 0,\qquad \sigma_k \ge 0,\qquad
\alpha_k \ge 0,\qquad \varepsilon_k \ge 0.
$$

- Enlargement membership:

$$
v_k \in \text{the epsilon-enlargement of } T
\text{ with parameter } \varepsilon_k \text{ at } y_k.
$$

In Lean this is the set denoted by `epsilonEnlargement T (ε k) (ε_nonneg k) (y k)`, where the argument `ε_nonneg k` is the proof that $\varepsilon_k \ge 0$.

- The residual inequality, for every $k$:

```math
\left\|c_k v_k + y_k - x_k\right\|^2 + 2 c_k \varepsilon_k
\le
\delta_k + \sigma_k^2 \left\|y_k - x_k\right\|^2.
```

Here $c_k v_k$ is real scalar multiplication in $H$. This inequality controls a residual-like quantity $c_k v_k + y_k - x_k$ together with the term $2 c_k \varepsilon_k$, bounding it by $\delta_k$ plus a $\sigma_k^2$-multiple of the squared distance between $y_k$ and $x_k$.

- The update-error inequality, for every $k$:

```math
\left\|x_{k+1} - (x_k - c_k v_k)\right\| \le \alpha_k.
```

This says that the next iterate $x_{k+1}$ is close, within tolerance $\alpha_k$, to the vector $x_k - c_k v_k$.

- Summability of the error and residual sequences:

$$
\sum_{k=0}^{\infty} \delta_k \quad\text{converges},\qquad
\sum_{k=0}^{\infty} \alpha_k \quad\text{converges}.
$$

In Lean these are the fields `summable_delta : Summable δ` and `summable_alpha : Summable α`.

- A uniform bound for $\sigma$:

$$
\exists \bar\sigma,\quad 0 < \bar\sigma < 1
\quad\text{and}\quad
\forall k,\quad 0 < \sigma_k \le \bar\sigma.
$$

So all $\sigma_k$ are positive and are bounded above by a single number $\bar\sigma$ strictly smaller than $1$.

- A uniform positive lower bound for $c$:

$$
\exists \bar c,\quad 0 < \bar c
\quad\text{and}\quad
\forall k,\quad \bar c \le c_k.
$$

So the step-size parameters $c_k$ are uniformly bounded away from $0$.

Taken together, `HPEIterates H T` is a specification of all data and assumptions for a hybrid proximal extragradient type iteration: it packages the sequences $x,y,v$, the real parameter sequences $c,\delta,\sigma,\alpha,\varepsilon$, membership of $v_k$ in an epsilon-enlargement of $T$, a residual bound, an inexact-update bound, summability of the error parameters $\delta$ and $\alpha$, a contraction-type upper bound on $\sigma$, and a positive lower bound on $c$. It does not assert that such iterates exist; it defines the type of records satisfying these properties.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, not a theorem, so Lean does not prove any proposition here. Instead, Lean creates a record type whose fields are either data or proof obligations. To construct an inhabitant of `HPEIterates H T`, one must supply the eight sequences $x,y,v,c,\delta,\sigma,\alpha,\varepsilon$ and then prove each propositional field: `c_pos`, `δ_nonneg`, `σ_nonneg`, `α_nonneg`, `ε_nonneg`, `enlargement_mem`, `residual_bound`, `update_error`, `summable_delta`, `summable_alpha`, `sigma_bound`, and `c_lower_bound`.

No named theorem or lemma is invoked, and no tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` appears. The field `enlargement_mem` depends on the earlier field `ε_nonneg`, because the Lean expression `epsilonEnlargement T (ε k) (ε_nonneg k) (y k)` uses `ε_nonneg k` as the proof that $\varepsilon_k \ge 0$. Apart from that field dependency, the mathematical content is exactly the list of assumptions described in the first section.

