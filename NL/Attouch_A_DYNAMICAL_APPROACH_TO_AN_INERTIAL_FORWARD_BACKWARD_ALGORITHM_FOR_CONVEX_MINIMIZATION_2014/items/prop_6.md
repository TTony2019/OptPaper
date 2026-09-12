## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_6.lean`

## Lean statement
```lean
theorem proposition12 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam : ℝ) (u y : ℕ → H)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hgrad_cont : Continuous gradPsi)
    (uLimit : H) :
    ((Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
        (nhds (toWeakSpace ℝ H uLimit)) ∧ IsWeakToWeakSequentiallyContinuous gradPsi) →
      ∃ yLim : H, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (y k)) Filter.atTop
        (nhds (toWeakSpace ℝ H yLim)) ∧ gradPsi uLimit - a • uLimit + b • yLim = 0) ∧
    (Filter.Tendsto u Filter.atTop (nhds uLimit) →
      ∃ yLim : H, Filter.Tendsto y Filter.atTop (nhds yLim) ∧
        gradPsi uLimit - a • uLimit + b • yLim = 0)
```

## Statement explanation
Let $H$ be a complete real inner product space, i.e. a real Hilbert space. The theorem has two real-valued functions and one vector field: $\phi : H \to \overline{\mathbb R}$ takes values in the extended reals, $\psi : H \to \mathbb R$ is finite-valued, and $g := \mathrm{gradPsi} : H \to H$ is the map denoted `gradPsi`. It also has real parameters $a,b,\lambda$, two sequences $u=(u_k)_{k\in\mathbb N}$ and $y=(y_k)_{k\in\mathbb N}$ in $H$, a point $u_\infty \in H$, and a continuity hypothesis $g$ continuous.

The hypothesis `IsIFBTrajectory phi psi gradPsi a b lam u y` says that $(u,y)$ is an inertial forward-backward trajectory associated with $\phi,\psi,g,a,b,\lambda$. The complete definition of this predicate is not shown, but the proof uses only the following consequences of it: $b>0$, $\lambda>0$, and, for every $k$, the second update equation

$$
\frac1\lambda (y_{k+1}-y_k)+g(u_{k+1})-a u_{k+1}+b y_{k+1}=0.
$$

The ordinary continuity hypothesis is $g$ continuous.

The conclusion is a conjunction of two conditional statements.

First, if

$$
u_k \rightharpoonup u_\infty
$$

weakly, and if $g$ is weak-to-weak sequentially continuous, then there exists $y_\infty\in H$ such that

$$
y_k \rightharpoonup y_\infty
$$

weakly and

$$
g(u_\infty)-a u_\infty+b y_\infty=0.
$$

Here weak convergence $u_k\rightharpoonup u_\infty$ is encoded in Lean by convergence of `toWeakSpace ℝ H (u k)` to `toWeakSpace ℝ H uLimit`.

Second, if

$$
u_k \to u_\infty
$$

strongly, i.e. in norm, then there exists $y_\infty\in H$ such that

$$
y_k \to y_\infty
$$

strongly and the same limiting equation

$$
g(u_\infty)-a u_\infty+b y_\infty=0
$$

holds.

Thus the theorem says that either weak convergence of $u_k$ plus weak-to-weak sequential continuity of $g$, or strong convergence of $u_k$ plus ordinary continuity of $g$, forces the second sequence $y_k$ to converge in the corresponding topology, and the limit satisfies the limiting first-order condition obtained from the trajectory equation. Since $b>0$, this equation determines $y_\infty$ uniquely as

$$
y_\infty=b^{-1}\bigl(a u_\infty-g(u_\infty)\bigr).
$$

## Lean proof
```lean
by
  have hb_pos := hIFB.b_pos
  have hlam_pos := hIFB.lambda_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hden_pos : 0 < 1 + lam * b := by nlinarith [mul_pos hlam_pos hb_pos]
  have hden_ne : 1 + lam * b ≠ 0 := ne_of_gt hden_pos
  let η : ℝ := (1 + lam * b)⁻¹
  have hη : 0 < η ∧ η < 1 := by
    constructor
    · dsimp [η]
      positivity
    · dsimp [η]
      rw [inv_lt_one₀ hden_pos]
      nlinarith [mul_pos hlam_pos hb_pos]
  let yLim : H := b⁻¹ • (a • uLimit - gradPsi uLimit)
  have hyLim : gradPsi uLimit - a • uLimit + b • yLim = 0 := by
    dsimp [yLim]
    rw [smul_smul]
    field_simp [hb_ne]
    module
  let w : ℕ → H := fun k => b⁻¹ • (a • u (k + 1) - gradPsi (u (k + 1)))
  have hw : ∀ k, b • w k = a • u (k + 1) - gradPsi (u (k + 1)) := by
    intro k
    simp [w, smul_smul, hb_ne]
  have hrec : ∀ k, y (k + 1) - yLim = η • (y k - yLim) +
      (lam * b * η) • (w k - yLim) := by
    intro k
    have hs := hIFB.second_update k
    have hmiddle : gradPsi (u (k + 1)) - a • u (k + 1) = -(b • w k) := by
      rw [hw k]
      abel
    have hs' : (1 / lam) • (y (k + 1) - y k) +
        (gradPsi (u (k + 1)) - a • u (k + 1)) + b • y (k + 1) = 0 := by
      convert hs using 1; abel
    rw [hmiddle] at hs'
    have hscaled := congrArg (fun z : H => lam • z) hs'
    have hraw : (y (k + 1) - y k) + (lam * b) • (y (k + 1) - w k) = 0 := by
      convert hscaled using 1 <;>
        simp [smul_add, smul_sub, smul_smul, div_eq_mul_inv, hlam_ne]; module
    have hbase : (1 + lam * b) • y (k + 1) = y k + (lam * b) • w k := by
      have hsubbase : (1 + lam * b) • y (k + 1) - (lam * b) • w k = y k := by
        calc
        (1 + lam * b) • y (k + 1) - (lam * b) • w k =
            y k + ((y (k + 1) - y k) + (lam * b) • (y (k + 1) - w k)) := by
              simp only [add_smul, one_smul, smul_sub]
              abel
        _ = y k := by rw [hraw]; abel
      exact eq_add_of_sub_eq hsubbase
    have hlimbase : (1 + lam * b) • yLim = yLim + (lam * b) • yLim := by
      module
    have hsub : (1 + lam * b) • (y (k + 1) - yLim) =
        (y k - yLim) + (lam * b) • (w k - yLim) := by
      rw [smul_sub, hbase, hlimbase]
      module
    have hinv : η * (1 + lam * b) = 1 := by
      dsimp [η]
      field_simp
    have := congrArg (fun z : H => η • z) hsub
    change η • ((1 + lam * b) • (y (k + 1) - yLim)) =
      η • ((y k - yLim) + (lam * b) • (w k - yLim)) at this
    rw [smul_smul, hinv, one_smul] at this
    convert this using 1; rw [smul_add, smul_smul]; module
  constructor
  · rintro ⟨huweak, hww⟩
    have husucc := huweak.comp (Filter.tendsto_add_atTop_nat 1)
    have hgradsucc := hww _ _ husucc
    have hwwlim : Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (w k)) Filter.atTop
        (nhds (toWeakSpace ℝ H yLim)) := by
      apply (weakConvergence_iff_forall_tendsto_inner_right w yLim).2
      intro ξ
      have hucoord := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 husucc ξ
      have hgcoord := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 hgradsucc ξ
      simpa [w, yLim, real_inner_smul_left, inner_sub_left] using
        (hucoord.const_smul a).sub hgcoord |>.const_smul b⁻¹
    refine ⟨yLim, ?_, hyLim⟩
    apply (weakConvergence_iff_forall_tendsto_inner_right y yLim).2
    intro ξ
    let p : ℕ → ℝ := fun k => inner ℝ (y k - yLim) ξ
    let e : ℕ → ℝ := fun k => (lam * b * η) * inner ℝ (w k - yLim) ξ
    have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
      have hc := (weakConvergence_iff_forall_tendsto_inner_right w yLim).1 hwwlim ξ
      simpa [e, inner_sub_left] using
        (hc.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => inner ℝ yLim ξ)
          Filter.atTop (nhds (inner ℝ yLim ξ)))).const_mul (lam * b * η)
    have hp_rec : ∀ k, p (k + 1) = η * p k + e k := by
      intro k
      dsimp [p, e]
      have := congrArg (fun z : H => inner ℝ z ξ) (hrec k)
      simpa [inner_sub_left, inner_add_left, real_inner_smul_left] using this
    have hp0 := tendsto_zero_of_contract_eq p e η hη he hp_rec
    simpa [p, inner_sub_left] using hp0.add
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => inner ℝ yLim ξ)
        Filter.atTop (nhds (inner ℝ yLim ξ)))
  · intro hu
    have husucc := hu.comp (Filter.tendsto_add_atTop_nat 1)
    have hgradsucc := (hgrad_cont.tendsto uLimit).comp husucc
    have hwlim : Filter.Tendsto w Filter.atTop (nhds yLim) := by
      simpa [w, yLim] using ((husucc.const_smul a).sub hgradsucc).const_smul b⁻¹
    refine ⟨yLim, ?_, hyLim⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    let p : ℕ → ℝ := fun k => ‖y k - yLim‖
    let e : ℕ → ℝ := fun k => (lam * b * η) * ‖w k - yLim‖
    have hcoeff : 0 ≤ lam * b * η := by positivity
    have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
      have hz' := hwlim.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => yLim)
          Filter.atTop (nhds yLim))
      have hz : Filter.Tendsto (fun k => w k - yLim) Filter.atTop (nhds 0) := by
        simpa using hz'
      simpa [e] using hz.norm.const_mul (lam * b * η)
    have hp_rec : ∀ k, p (k + 1) ≤ η * p k + e k := by
      intro k
      dsimp [p, e]
      rw [hrec k]
      calc
        ‖η • (y k - yLim) + (lam * b * η) • (w k - yLim)‖ ≤
            ‖η • (y k - yLim)‖ + ‖(lam * b * η) • (w k - yLim)‖ := norm_add_le _ _
        _ = η * ‖y k - yLim‖ + (lam * b * η) * ‖w k - yLim‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hη.1,
            abs_of_nonneg hcoeff]
    simpa [p] using tendsto_zero_of_contract_nonneg p e η hη (fun k => norm_nonneg _) he hp_rec
```

## Proof explanation
The proof begins by extracting the positivity and recurrence information from the trajectory hypothesis. It obtains $b>0$ and $\lambda>0$, hence $b\neq 0$ and $\lambda\neq 0$. It then defines

$$
\eta=(1+\lambda b)^{-1}.
$$

Because $b>0$ and $\lambda>0$, we have $1+\lambda b>1$, so

$$
0<\eta<1.
$$

This $\eta$ is the contraction factor that will be used in the recurrence estimates. In Lean, the positivity of $1+\lambda b$ is proved by `nlinarith` from $\lambda b>0$, and the fact that $\eta<1$ is proved by rewriting with `inv_lt_one₀`.

Next the proof defines the candidate limit

$$
y_\infty=b^{-1}\bigl(a u_\infty-g(u_\infty)\bigr).
$$

It then proves the equilibrium relation

$$
g(u_\infty)-a u_\infty+b y_\infty=0.
$$

Indeed, multiplying $y_\infty$ by $b$ gives $b y_\infty=a u_\infty-g(u_\infty)$, and adding $g(u_\infty)-a u_\infty$ gives zero. In Lean this algebra is done by expanding the definition of `yLim`, rewriting scalar multiplication, clearing the denominator with `field_simp` using $b\neq 0$, and solving the resulting linear equation with `module`.

The proof then introduces an auxiliary sequence

$$
w_k=b^{-1}\bigl(a u_{k+1}-g(u_{k+1})\bigr).
$$

It immediately records that

$$
b w_k=a u_{k+1}-g(u_{k+1}),
$$

or equivalently

$$
g(u_{k+1})-a u_{k+1}=-b w_k.
$$

This $w_k$ is the vector that would be obtained from the limiting equation if $u_\infty$ were replaced by $u_{k+1}$.

The key recurrence is then derived from the second update equation. Starting from

$$
\frac1\lambda (y_{k+1}-y_k)+g(u_{k+1})-a u_{k+1}+b y_{k+1}=0
$$

and substituting $g(u_{k+1})-a u_{k+1}=-b w_k$, one obtains

$$
\frac1\lambda (y_{k+1}-y_k)-b w_k+b y_{k+1}=0.
$$

Multiplying by $\lambda$ gives

$$
y_{k+1}-y_k+\lambda b(y_{k+1}-w_k)=0,
$$

hence

$$
(1+\lambda b)y_{k+1}=y_k+\lambda b w_k.
$$

Also

$$
(1+\lambda b)y_\infty=y_\infty+\lambda b y_\infty.
$$

Subtracting these two identities and multiplying by $\eta=(1+\lambda b)^{-1}$ yields the recurrence

$$
y_{k+1}-y_\infty
=
\eta (y_k-y_\infty)+\lambda b\eta (w_k-y_\infty).
$$

This is the central estimate used in both parts of the theorem. In Lean, this is the long `have hrec` block, using `convert`, `simp`, `abel`, `field_simp`, and `module` to perform the vector-space algebra.

After this, the proof splits the conjunction with `constructor`.

In the first branch, it assumes the pair of hypotheses

$$
u_k\rightharpoonup u_\infty
$$

and that $g$ is weak-to-weak sequentially continuous. The proof first shifts the sequence: since $k\mapsto k+1$ tends to infinity, $u_{k+1}\rightharpoonup u_\infty$. This uses the lemma `Filter.tendsto_add_atTop_nat 1`. Applying the weak-to-weak sequential continuity hypothesis to this shifted weakly convergent sequence gives

$$
g(u_{k+1})\rightharpoonup g(u_\infty).
$$

The proof then shows that the auxiliary sequence $w_k$ converges weakly to $y_\infty$. It uses the characterization

$$
\xi_k\rightharpoonup \xi
\quad\Longleftrightarrow\quad
\forall v,\ \langle \xi_k,v\rangle \to \langle \xi,v\rangle,
$$

which is the content of `weakConvergence_iff_forall_tendsto_inner_right`. For every $v\in H$, the inner product $\langle u_{k+1},v\rangle$ tends to $\langle u_\infty,v\rangle$, and $\langle g(u_{k+1}),v\rangle$ tends to $\langle g(u_\infty),v\rangle$. Therefore

$$
\langle w_k,v\rangle
=
b^{-1}\bigl(a\langle u_{k+1},v\rangle-\langle g(u_{k+1}),v\rangle\bigr)
$$

tends to

$$
b^{-1}\bigl(a\langle u_\infty,v\rangle-\langle g(u_\infty),v\rangle\bigr)
=
\langle y_\infty,v\rangle.
$$

Thus, by the same weak-convergence characterization,

$$
w_k\rightharpoonup y_\infty.
$$

To prove that $y_k$ converges weakly to $y_\infty$, the proof fixes $v\in H$ and defines the scalar sequences

$$
p_k=\langle y_k-y_\infty,v\rangle,
\qquad
e_k=\lambda b\eta\langle w_k-y_\infty,v\rangle.
$$

Because $w_k\rightharpoonup y_\infty$, its inner product with $v$ converges to $\langle y_\infty,v\rangle$, so $\langle w_k-y_\infty,v\rangle\to 0$, and hence

$$
e_k\to 0.
$$

Taking the inner product of the recurrence for $y_{k+1}-y_\infty$ with $v$ gives the exact scalar recurrence

$$
p_{k+1}=\eta p_k+e_k.
$$

The cited lemma `tendsto_zero_of_contract_eq` states that if $0<\eta<1$, if $e_k\to0$, and if $p_{k+1}=\eta p_k+e_k$ for all $k$, then $p_k\to0$. Applying it gives

$$
\langle y_k-y_\infty,v\rangle\to0.
$$

Adding the constant $\langle y_\infty,v\rangle$ gives

$$
\langle y_k,v\rangle\to\langle y_\infty,v\rangle.
$$

Since this holds for every $v$, the weak-convergence characterization yields

$$
y_k\rightharpoonup y_\infty.
$$

Together with the already established equilibrium relation, this proves the first implication.

In the second branch, the proof assumes strong convergence

$$
u_k\to u_\infty.
$$

Again shifting gives $u_{k+1}\to u_\infty$. Since $g$ is continuous, ordinary continuity gives

$$
g(u_{k+1})\to g(u_\infty).
$$

Therefore

$$
w_k=b^{-1}\bigl(a u_{k+1}-g(u_{k+1})\bigr)\to
b^{-1}\bigl(a u_\infty-g(u_\infty)\bigr)=y_\infty
$$

in norm.

It remains to prove $y_k\to y_\infty$ in norm. The proof rewrites this convergence using `tendsto_iff_norm_sub_tendsto_zero`, so it is enough to show

$$
\|y_k-y_\infty\|\to0.
$$

It defines

$$
p_k=\|y_k-y_\infty\|,
\qquad
e_k=\lambda b\eta\|w_k-y_\infty\|.
$$

Since $w_k\to y_\infty$, the sequence $\|w_k-y_\infty\|$ tends to $0$, hence $e_k\to0$. Also $p_k\ge0$ for all $k$. From the recurrence

$$
y_{k+1}-y_\infty
=
\eta (y_k-y_\infty)+\lambda b\eta (w_k-y_\infty)
$$

and the triangle inequality,

$$
p_{k+1}
\le
\eta\|y_k-y_\infty\|+\lambda b\eta\|w_k-y_\infty\|
=
\eta p_k+e_k.
$$

The proof also verifies that $\lambda b\eta\ge0$, using positivity of $b,\lambda,\eta$. The cited lemma `tendsto_zero_of_contract_nonneg` states that if $0<\eta<1$, if $p_k\ge0$ for all $k$, if $e_k\to0$, and if

$$
p_{k+1}\le \eta p_k+e_k
$$

for all $k$, then $p_k\to0$. Applying it gives

$$
\|y_k-y_\infty\|\to0,
$$

which is equivalent to

$$
y_k\to y_\infty
$$

in norm. Combining this with the equilibrium relation proves the second implication.

Thus the proof constructs one explicit candidate $y_\infty=b^{-1}(a u_\infty-g(u_\infty))$, proves it always satisfies the limiting equation, and then shows that the trajectory recurrence forces $y_k$ to converge to that candidate, weakly in the first case and strongly in the second.

