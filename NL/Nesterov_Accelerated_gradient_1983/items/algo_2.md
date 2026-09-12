## Source file
`Nesterov_Accelerated_gradient_1983/items/algo_2.lean`

## Lean statement
```lean
structure CompositeAcceleratedMethod {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : ExtremalProblem m E) (T : E → ℝ → E) where
  y : ℕ → E
  x : ℕ → E
  A : ℕ → ℝ
  weight : ℕ → ℝ
  y0 : E
  y_zero : y 0 = y0
  x_neg_one : E
  initialA : ℝ
  initialL : EuclideanSpace ℝ (Fin m)
  z : E
  z_ne_y0 : z ≠ y0
  x_neg_one_eq_y0 : x_neg_one = y0
  initialL_eq : ∀ i, initialL i = ‖gradient (P.f i) y0 - gradient (P.f i) z‖ / ‖y0 - z‖
  initialA_eq : initialA = P.F initialL
  T_is_auxiliary_minimizer : ∀ y A, T y A ∈ auxiliaryMinimizers P y A
  weight_zero : weight 0 = 1
  searchIndex : ℕ → ℕ
  A_eq_doubling_previous : ∀ k, A k = (2 : ℝ) ^ (searchIndex k : ℤ) *
    if k = 0 then initialA else A (k - 1)
  accepted : ∀ k, P.F (fbar P (T (y k) (A k))) ≤ auxiliaryValue P (y k) (A k)
  minimal_searchIndex : ∀ k j, j < searchIndex k →
    auxiliaryValue P (y k) ((2 : ℝ) ^ (j : ℤ) *
      (if k = 0 then initialA else A (k - 1))) <
    P.F (fbar P (T (y k) ((2 : ℝ) ^ (j : ℤ) *
      (if k = 0 then initialA else A (k - 1)))))
  update_x : ∀ k, x k = T (y k) (A k)
  update_weight : ∀ k, weight (k + 1) = (1 + Real.sqrt (4 * weight k ^ 2 + 1)) / 2
  update_y : ∀ k, y (k + 1) = x k + ((weight k - 1) / weight (k + 1)) •
    (x k - if k = 0 then x_neg_one else x (k - 1))
```

## Statement explanation
The declaration defines a structure named `CompositeAcceleratedMethod`. It is parameterized by a natural number $m$, a type $E$ satisfying typeclass assumptions making $E$ a complete real inner product space, a problem $P : \mathrm{ExtremalProblem} m E$, and a map $T : E \to \mathbb R \to E$. The structure does not assert that such an object exists; rather, it specifies what data and constraints an inhabitant of this type must contain.

An inhabitant consists first of the following data: sequences

$$
y : \mathbb N \to E,\qquad x : \mathbb N \to E,\qquad A : \mathbb N \to \mathbb R,\qquad w : \mathbb N \to \mathbb R,
$$

where $w$ is the field named `weight`, together with an initial point $y_0 \in E$, an auxiliary previous point $x_{-1}\in E$, a real scalar $A_{\rm init}\in \mathbb R$, a vector of initial estimates $L_{\rm init}\in \mathbb R^m$, a second point $z\in E$, and a search-index function $s:\mathbb N\to\mathbb N$. Here $L_{\rm init}$ is the field `initialL`, $A_{\rm init}$ is `initialA`, $x_{-1}$ is `x_neg_one`, and $s$ is `searchIndex`. Write $F_P := P.F$, $f_i := P.f_i$, and $\bar f_P := \mathrm{fbar}_P$ for the problem components appearing in the statement.

The structure then requires the following properties. The sequence $y$ starts at $y_0$, so $y(0)=y_0$; the previous iterate is set to the initial point, so $x_{-1}=y_0$; and the two points used in the finite-difference estimate are distinct, so $z\ne y_0$. For every coordinate $i\in \mathrm{Fin} m$, the initial vector $L_{\rm init}$ is given by the finite-difference quotient of the gradients of the component functions:

$$
L_{\rm init}(i)
=
\frac{\left\|\nabla f_i(y_0)-\nabla f_i(z)\right\|}{\|y_0-z\|}.
$$

Since $z\ne y_0$, the denominator $\|y_0-z\|$ is nonzero in the normed space $E$. The scalar $A_{\rm init}$ is defined from $L_{\rm init}$ by

$$
A_{\rm init}=F_P(L_{\rm init}).
$$

The map $T$ is required to select auxiliary minimizers: for every $y\in E$ and every scalar $a\in\mathbb R$,

$$
T(y,a)\in \mathrm{auxiliaryMinimizers}(P,y,a).
$$

The weight sequence starts at $w(0)=1$. The scalar sequence $A$ is obtained from the previous scalar, or from $A_{\rm init}$ at the first step, by doubling according to the search index:

$$
A(k)=2^{s(k)}\cdot
\begin{cases}
A_{\rm init},& k=0,\\
A(k-1),& k>0.
\end{cases}
$$

The exponent is an integer power in Lean, but since $s(k)\in\mathbb N$, it is the usual nonnegative power of $2$. The acceptance condition says that, at the chosen parameter $A(k)$,

$$
F_P\!\left(\bar f_P\!\left(T(y(k),A(k))\right)\right)
\le
\mathrm{auxiliaryValue}(P,y(k),A(k)).
$$

The minimality condition says that every smaller search exponent fails in the strict sense: for every $k$ and every $j<s(k)$,

$$
\mathrm{auxiliaryValue}\!\left(P,y(k),2^j\cdot
\begin{cases}
A_{\rm init},& k=0,\\
A(k-1),& k>0
\end{cases}\right)
<
F_P\!\left(\bar f_P\!\left(T\!\left(y(k),2^j\cdot
\begin{cases}
A_{\rm init},& k=0,\\
A(k-1),& k>0
\end{cases}\right)\right)\right).
$$

Thus $s(k)$ is the first exponent at which the acceptance inequality holds. The sequence $x$ is defined by applying $T$ at the current pair $(y(k),A(k))$:

$$
x(k)=T(y(k),A(k)).
$$

Because $T$ always returns an auxiliary minimizer, this also means that $x(k)$ is an auxiliary minimizer for the auxiliary problem at $(y(k),A(k))$. The weights satisfy the recurrence

$$
w(k+1)=\frac{1+\sqrt{4w(k)^2+1}}{2},
$$

which is the standard positive square-root recurrence; equivalently, $w(k+1)^2-w(k+1)=w(k)^2$. Finally, the sequence $y$ is updated by the momentum rule

$$
y(k+1)=x(k)+\frac{w(k)-1}{w(k+1)}
\left(x(k)-
\begin{cases}
x_{-1},& k=0,\\
x(k-1),& k>0
\end{cases}
\right).
$$

At $k=0$, since $w(0)=1$ and $x_{-1}=y_0$, this gives $y(1)=x(0)$. Overall, the declaration packages the initial data, the search rule for the scalar $A(k)$, the auxiliary-minimizer rule for $x(k)$, the weight recurrence, and the accelerated extrapolation rule for $y(k+1)$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The provided source contains only the structure declaration and the comment `-- No separate proof part.` A structure declaration in Lean introduces a type together with projections for its fields; it does not have a tactic proof body. Therefore there are no commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no named theorem or lemma is invoked.

The proof-relevant content is instead the collection of proposition-valued fields that any inhabitant must supply: the equalities $y(0)=y_0$, $x_{-1}=y_0$, $A_{\rm init}=F_P(L_{\rm init})$, the recurrence for $A$, the update equations for $x$, $w$, and $y$; the disequality $z\ne y_0$; the coordinate formula for $L_{\rm init}$; the membership condition $T(y,a)\in \mathrm{auxiliaryMinimizers}(P,y,a)$; the acceptance inequality; and the minimality inequality for smaller search exponents. These fields are exactly the defining constraints of the proposed composite accelerated method. Since no proof body is present, there is no step-by-step derivation to analyze.

