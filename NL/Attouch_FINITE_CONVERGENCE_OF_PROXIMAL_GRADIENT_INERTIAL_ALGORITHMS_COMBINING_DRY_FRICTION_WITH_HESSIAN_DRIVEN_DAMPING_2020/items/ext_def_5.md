## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/ext_def_5.lean`

## Lean statement
```lean
structure ExtremalEigenvalues (n : Type*) [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) where
  muMin : ℝ
  muMax : ℝ
  symmetric : M.IsSymm
  positive_definite : ∀ x : n → ℝ, x ≠ 0 → 0 < dotProduct x (M.mulVec x)
  muMin_pos : 0 < muMin
  ordered : muMin ≤ muMax
  muMin_isLeast : ∀ μ : ℝ, (∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ μ * v i) → muMin ≤ μ
  muMin_isEigenvalue : ∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ muMin * v i
  muMax_isGreatest : ∀ μ : ℝ, (∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ μ * v i) → μ ≤ muMax
  muMax_isEigenvalue : ∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ muMax * v i
```

## Statement explanation
The declaration introduces a structure named `ExtremalEigenvalues`. Its parameters are a finite index type \(n\), with typeclass assumptions `[Fintype n]` and `[DecidableEq n]`, and a real square matrix \(M\) of size \(n\times n\). A term of type `ExtremalEigenvalues n M` is a record collecting two real numbers, \(\mu_{\min}\) and \(\mu_{\max}\), together with proofs of the following facts.

- `symmetric`: \(M\) is symmetric, meaning \(M^\top=M\), equivalently \(M_{ij}=M_{ji}\) for all indices \(i,j\).
- `positive_definite`: for every vector \(x\colon n\to\mathbb R\), if \(x\neq 0\) as a function, then
  \[
  0<\langle x,Mx\rangle=x^\top Mx.
  \]
  Here \(Mx\) is the matrix-vector product and \(\langle\cdot,\cdot\rangle\) is the Euclidean dot product. Thus the quadratic form of \(M\) is strictly positive on every nonzero vector.
- `muMin_pos`: \(0<\mu_{\min}\).
- `ordered`: \(\mu_{\min}\le\mu_{\max}\).
- `muMin_isLeast`: for every real number \(\mu\), if there exists a nonzero vector \(v\colon n\to\mathbb R\) such that
  \[
  Mv=\mu v,
  \]
  meaning \((Mv)_i=\mu v_i\) for every coordinate \(i\), then
  \[
  \mu_{\min}\le\mu.
  \]
  So every eigenvalue of \(M\) is at least \(\mu_{\min}\).
- `muMin_isEigenvalue`: there exists a nonzero vector \(v\colon n\to\mathbb R\) such that
  \[
  Mv=\mu_{\min}v.
  \]
  Thus \(\mu_{\min}\) is actually an eigenvalue, not merely a lower bound.
- `muMax_isGreatest`: for every real number \(\mu\), if there exists a nonzero vector \(v\colon n\to\mathbb R\) with \(Mv=\mu v\), then
  \[
  \mu\le\mu_{\max}.
  \]
  So every eigenvalue of \(M\) is at most \(\mu_{\max}\).
- `muMax_isEigenvalue`: there exists a nonzero vector \(v\colon n\to\mathbb R\) such that
  \[
  Mv=\mu_{\max}v.
  \]
  Thus \(\mu_{\max}\) is actually an eigenvalue.

In ordinary language, the structure packages a certificate that \(M\) is a symmetric positive definite real matrix and that \(\mu_{\min}\) and \(\mu_{\max}\) are precisely its least and greatest eigenvalues. It records that \(\mu_{\min}>0\) and \(\mu_{\min}\le\mu_{\max}\), and it supplies nonzero eigenvectors realizing both endpoint eigenvalues. The declaration does not itself prove that such numbers exist; it specifies the data and properties that an inhabitant of the structure must contain. If such an inhabitant exists, then all eigenvalues of \(M\) lie in the interval \([\mu_{\min},\mu_{\max}]\), and both endpoints are attained.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source contains only the comment indicating that no proof follows. Since the declaration is a `structure`, Lean treats the listed fields as the components of a record type rather than as goals to be proved in sequence. To construct an element of `ExtremalEigenvalues n M`, one would supply the real numbers \(\mu_{\min}\) and \(\mu_{\max}\), then provide the proofs `symmetric`, `positive_definite`, `muMin_pos`, `ordered`, `muMin_isLeast`, `muMin_isEigenvalue`, `muMax_isGreatest`, and `muMax_isEigenvalue`. There are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no named local theorem or lemma is invoked. The mathematical content is therefore entirely contained in the statement of the structure and in the types of its fields, not in a proof argument.

