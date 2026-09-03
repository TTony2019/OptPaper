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
The theorem is stated in a real inner-product space \(H\): the type \(H\) is assumed to carry a normed additive commutative group structure and an inner product space structure over \(\mathbb{R}\).  

Let \(\Phi : H \to \{e \in EReal \mid e > \bot_{EReal}\}\) be an extended-real-valued function whose values are strictly above the bottom extended real, and assume \(hPhi : \Phi \in ERealFunction.gammaZero H\). This is a hypothesis placing \(\Phi\) in the \(\Gamma_0\)-type class of extended-real-valued functions; in the proof only its consequence that \(\Phi\) is proper is used.  

Let \(B : H \to H\) be a map, \(\beta : \mathbb{R}\) be a real number, and \(S : Set H\) be a subset of \(H\). Assume \(hbeta : 0 < \beta\). Assume \(hcoco : CocoerciveOn\ \beta\ Set.univ\ (fun x : Set.univ \mapsto B x)\), meaning that \(B\) is \(\beta\)-cocoercive on the whole space: for all \(x,y \in H\),  
\[
\beta \|Bx-By\|^2 \le \langle Bx-By,\ x-y\rangle .
\]
Also assume \(hBmax : Maximal\ SetValuedOperator.IsMonotone\ B.toSetValuedOperator\), that is, the set-valued operator \(x \mapsto \{Bx\}\) is maximal monotone.  

Finally assume \(hS : \forall z,\ z \in S \leftrightarrow -Bz \in ERealFunction.subdifferential\ \Phi z\). This means that the set \(S\) is exactly the set of points \(z\) for which \(-Bz\) is a subgradient of \(\Phi\) at \(z\).  

The conclusion is: for every \(z \in S\) and every \(w \in S\),  
\[
Bz = Bw.
\]
Thus \(B\) is constant on the set \(S\).

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
The proof begins with `intro z hz w hw`, introducing arbitrary elements \(z,w \in H\) and hypotheses \(hz : z \in S\) and \(hw : w \in S\). The goal becomes \(B z = B w\).  

Using \(hS\), the equivalences \(hS z\) and \(hS w\) give  
\[
hzsub : -Bz \in \partial \Phi(z), \qquad hwsub : -Bw \in \partial \Phi(w).
\]
The proof applies monotonicity of the subdifferential through `ERealFunction.isMonotone_subdifferential`, using the properness of \(\Phi\) obtained from \(hPhi\). With subgradients \(-Bz\) at \(z\) and \(-Bw\) at \(w\), this yields  
\[
hmono : 0 \le \langle (-Bz)-(-Bw),\ z-w\rangle .
\]
This is the standard monotonicity inequality for subgradients.

Next, the proof rewrites this inequality. The equality  
\[
(-Bz)-(-Bw) = -(Bz-Bw)
\]
is proved by `abel`, and then `inner_neg_left` rewrites the first inner-product argument after removing the minus sign:
\[
0 \le -\langle Bz-Bw,\ z-w\rangle .
\]
From this, `linarith` derives  
\[
hsubmon : \langle Bz-Bw,\ z-w\rangle \le 0.
\]

The cocoercivity assumption is then invoked via `hcoco.ineq`, applied to the two points \(z\) and \(w\) as elements of `Set.univ`. After simplification with `simpa [real_inner_comm]`, which uses commutativity of the real inner product, the proof obtains  
\[
hcobound : \beta \|Bz-Bw\|^2 \le \langle Bz-Bw,\ z-w\rangle .
\]

The proof also establishes  
\[
hnonneg : 0 \le \beta \|Bz-Bw\|^2
\]
using that \(\beta > 0\), via `mul_nonneg`, and that a square is nonnegative, via `sq_nonneg`.

Combining these inequalities gives  
\[
0 \le \beta \|Bz-Bw\|^2 \le \langle Bz-Bw,\ z-w\rangle \le 0.
\]
The Lean command `le_antisymm` is used with the two inequalities \(\beta \|Bz-Bw\|^2 \le 0\) and \(0 \le \beta \|Bz-Bw\|^2\) to conclude  
\[
hprodzero : \beta \|Bz-Bw\|^2 = 0.
\]

Since \(\beta > 0\), \(\beta \ne 0\). From \(\beta \|Bz-Bw\|^2 = 0\), the proof applies `mul_eq_zero` and then resolves the factor \(\beta \ne 0\), obtaining \(\|Bz-Bw\|^2 = 0\). Then `sq_eq_zero_iff` gives  
\[
hnormzero : \|Bz-Bw\| = 0.
\]
Finally, `norm_eq_zero` converts this into \(Bz-Bw = 0\), and `sub_eq_zero` converts that into the desired conclusion \(Bz = Bw\). The command `exact` closes the goal.

The hypothesis \(hBmax\) is not used in this proof.

