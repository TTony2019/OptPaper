## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/rem_1.lean`

## Lean statement
```lean
theorem remark_1_INE_reduces_to_Nash {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (β μ : ℝ) (xbar : X) (ybar : Y) :
    IsINE f g h k c 0 β μ 0 xbar ybar ↔
    ((∀ (ξ : X), f xbar + β * c xbar ybar ≤ f ξ + β * c ξ ybar) ∧
     (∀ (η : Y), g ybar + μ * c xbar ybar ≤ g η + μ * c xbar η))
```

## Statement explanation
For arbitrary types \(X\) and \(Y\), the theorem fixes functions
\[
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,\qquad
h:X\to X\to\mathbb R,\qquad k:Y\to Y\to\mathbb R,\qquad
c:X\to Y\to\mathbb R,
\]
real parameters \(\beta,\mu\in\mathbb R\), and points \(\bar x\in X\), \(\bar y\in Y\). There are no additional hypotheses on any of these objects. The predicate `IsINE` is defined by a conjunction of two inequalities:
\[
\operatorname{IsINE}(f,g,h,k,c,\alpha,\beta,\mu,\nu,\bar x,\bar y)
\]
means
\[
\Bigl(\forall \xi\in X,\,
f(\bar x)+\beta c(\bar x,\bar y)+\alpha h(\bar x,\bar x)
\le f(\xi)+\beta c(\xi,\bar y)+\alpha h(\bar x,\xi)\Bigr)
\]
and
\[
\Bigl(\forall \eta\in Y,\,
g(\bar y)+\mu c(\bar x,\bar y)+\nu k(\bar y,\bar y)
\le g(\eta)+\mu c(\bar x,\eta)+\nu k(\bar y,\eta)\Bigr).
\]
The theorem specializes this definition to \(\alpha=0\) and \(\nu=0\), keeping \(\beta\) and \(\mu\) as they are. The statement asserts that
\[
\operatorname{IsINE}(f,g,h,k,c,0,\beta,\mu,0,\bar x,\bar y)
\]
is equivalent to the pair of inequalities
\[
\Bigl(\forall \xi\in X,\,
f(\bar x)+\beta c(\bar x,\bar y)\le f(\xi)+\beta c(\xi,\bar y)\Bigr)
\]
and
\[
\Bigl(\forall \eta\in Y,\,
g(\bar y)+\mu c(\bar x,\bar y)\le g(\eta)+\mu c(\bar x,\eta)\Bigr).
\]
Thus, when the coefficients of \(h\) and \(k\) are zero, those terms disappear and the INE condition becomes exactly the two unilateral equilibrium inequalities for the functions
\[
F(\xi,\eta)=f(\xi)+\beta c(\xi,\eta),\qquad
G(\xi,\eta)=g(\eta)+\mu c(\xi,\eta).
\]
The first inequality says that, with \(\eta=\bar y\) fixed, the value \(F(\bar x,\bar y)\) is no larger than \(F(\xi,\bar y)\) for every \(\xi\in X\). The second says that, with \(\xi=\bar x\) fixed, the value \(G(\bar x,\bar y)\) is no larger than \(G(\bar x,\eta)\) for every \(\eta\in Y\). This is the sense in which INE reduces to the classical Nash equilibrium condition for those payoff functions. The functions \(h\) and \(k\) remain in the statement only as parameters of `IsINE`, but under \(\alpha=0\) and \(\nu=0\) they have no effect on the truth of the condition.

## Lean proof
```lean
by
  dsimp [IsINE]
  simp
```

## Proof explanation
The proof is a direct definitional and arithmetic simplification; it does not use `intro`, `rw`, `exact`, or `linarith`. The tactic `dsimp [IsINE]` unfolds the definition of `IsINE` at the occurrence on the left side of the biconditional. After this unfolding, the goal compares
\[
\Bigl(\forall \xi,\,
f(\bar x)+\beta c(\bar x,\bar y)+0\cdot h(\bar x,\bar x)
\le f(\xi)+\beta c(\xi,\bar y)+0\cdot h(\bar x,\xi)\Bigr)
\]
together with
\[
\Bigl(\forall \eta,\,
g(\bar y)+\mu c(\bar x,\bar y)+0\cdot k(\bar y,\bar y)
\le g(\eta)+\mu c(\bar x,\eta)+0\cdot k(\bar y,\eta)\Bigr)
\]
against the two displayed inequalities from the theorem statement. The tactic `simp` then simplifies both sides. In \(\mathbb R\), multiplication by zero gives \(0\cdot h(\bar x,\bar x)=0\), \(0\cdot h(\bar x,\xi)=0\), \(0\cdot k(\bar y,\bar y)=0\), and \(0\cdot k(\bar y,\eta)=0\). Also, adding zero leaves a real number unchanged, so terms such as
\[
f(\bar x)+\beta c(\bar x,\bar y)+0
\]
become
\[
f(\bar x)+\beta c(\bar x,\bar y).
\]
The same simplification happens in the second inequality for \(g\), \(\mu\), and \(k\). After these rewrites, the left side and the right side of the desired biconditional are syntactically the same pair of universally quantified inequalities. Therefore the biconditional is closed by simplification. No separate proof of the forward or reverse direction is needed, because `simp` has reduced both sides to identical propositions.

