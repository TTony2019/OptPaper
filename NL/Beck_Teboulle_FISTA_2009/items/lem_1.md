## Source file
`Beck_Teboulle_FISTA_2009/items/lem_1.lean`

## Lean statement
```lean
theorem quadratic_upper_bound_C11 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hf : IsC11 f Lf) {L : ℝ} (hL : Lf ≤ L)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x ≤ f y + ⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2
```

## Statement explanation
The theorem `quadratic_upper_bound_C11` states the following. For a natural number $n$, let $f:\mathbb R^n\to\mathbb R$, where $\mathbb R^n$ is the Euclidean space `EuclideanSpace ℝ (Fin n)`. Let $L_f$ and $L$ be real numbers, assume $hf:\texttt{IsC11 } f L_f$, and assume $L_f\le L$. Then for every $x,y\in\mathbb R^n$,

$$
f(x)\le f(y)+\langle \nabla f(y),x-y\rangle+\frac{L}{2}\|x-y\|^2 .
$$

The hypothesis `IsC11 f Lf` is the bundled $C^1$-with-Lipschitz-gradient assumption. In the proof it is used to supply three concrete facts: $L_f>0$, that $f$ is continuously differentiable, and that the gradient of $f$ is $L_f$-Lipschitz:

$$
\|\nabla f(u)-\nabla f(v)\|\le L_f\|u-v\|.
$$

Thus the theorem is a quadratic upper bound, or descent lemma: if the gradient is Lipschitz with constant $L_f$, then any larger constant $L\ge L_f$ gives the global upper estimate

$$
f(x)\le f(y)+\langle \nabla f(y),x-y\rangle+\frac L2\|x-y\|^2 .
$$

## Lean proof
```lean
by
  have hLf_pos : 0 < Lf := hf.hL_pos
  -- Line segment and auxiliary functions
  let φ := fun (t : ℝ) => y + t • (x - y)
  let h := fun (t : ℝ) => f (φ t)
  let g := fun (t : ℝ) => h t - h 0 - t * ⟪gradient f y, x - y⟫ - (Lf / 2) * (t ^ 2) * ‖x - y‖ ^ 2
  have hg0 : g 0 = 0 := by dsimp [g, h, φ]; simp
  -- Derivative of h at any t₀ via HasLineDerivAt + HasDerivAt.comp_add_const
  have h_deriv (t₀ : ℝ) : HasDerivAt h (⟪gradient f (φ t₀), x - y⟫) t₀ := by
    have h_diff_f : Differentiable ℝ f := by
      apply hf.contDiff.differentiable; decide
    have h_diffAt : DifferentiableAt ℝ f (φ t₀) := h_diff_f.differentiableAt
    -- HasLineDerivAt gives derivative at 0 of s ↦ f(φ(t₀) + s•(x-y)) = f(φ(t₀+s))
    have h_line_raw : HasLineDerivAt ℝ f
        (lineDeriv ℝ f (φ t₀) (x - y)) (φ t₀) (x - y) :=
      h_diffAt.lineDifferentiableAt.hasLineDerivAt
    have h_line_val : lineDeriv ℝ f (φ t₀) (x - y) = ⟪gradient f (φ t₀), x - y⟫ := by
      rw [h_diffAt.lineDeriv_eq_fderiv, inner_gradient_left h_diffAt]
    dsimp [HasLineDerivAt] at h_line_raw
    rw [h_line_val] at h_line_raw
    -- h_line_raw : HasDerivAt (λ s => f(φ t₀ + s•(x-y))) ⟨...⟩ 0
    -- Note: φ(t₀) + s•(x-y) = y + t₀•(x-y) + s•(x-y) = φ(t₀+s)
    have h_shift_eq : (fun (s : ℝ) => f (φ t₀ + s • (x - y))) =
        (fun (s : ℝ) => h (t₀ + s)) := by
      ext s; dsimp [h, φ]; simp [add_smul, add_assoc]
    rw [h_shift_eq] at h_line_raw
    -- h_line_raw : HasDerivAt (λ s => h(t₀ + s)) f' 0
    -- Shift: HasDerivAt.comp_add_const t₀ (-t₀) h_line_raw
    --   : HasDerivAt (λ s => h(t₀ + (s + (-t₀)))) f' t₀ = HasDerivAt h f' t₀
    have h_shift_back := HasDerivAt.comp_add_const t₀ (-t₀)
      (by simpa [add_neg_cancel] using h_line_raw)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h_shift_back
  -- Derivative of g: g'(t) = h'(t) - 0 - ⟨∇f(y), x-y⟩ - Lf·t·‖x-y‖²
  have hg_deriv (t : ℝ) : HasDerivAt g
      (⟪gradient f (φ t) - gradient f y, x - y⟫ - Lf * t * ‖x - y‖ ^ 2) t := by
    have h1 : HasDerivAt h (⟪gradient f (φ t), x - y⟫) t := h_deriv t
    have h2 : HasDerivAt (fun (_ : ℝ) => h 0) 0 t := hasDerivAt_const _ _
    have h3 : HasDerivAt (fun (s : ℝ) => s * ⟪gradient f y, x - y⟫)
        (⟪gradient f y, x - y⟫) t :=
      hasDerivAt_mul_const (⟪gradient f y, x - y⟫)
    have h4 : HasDerivAt (fun (s : ℝ) => (Lf / 2) * (s ^ 2) * ‖x - y‖ ^ 2)
        (Lf * t * ‖x - y‖ ^ 2) t := by
      have h_sq : HasDerivAt (fun (s : ℝ) => s ^ 2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simpa [Nat.cast_ofNat] using this
      set C := (Lf / 2) * ‖x - y‖ ^ 2 with hC
      have h_mul : HasDerivAt (fun (s : ℝ) => C * (s ^ 2)) (C * (2 * t)) t :=
        HasDerivAt.const_mul C h_sq
      have h_simp_deriv : C * (2 * t) = Lf * t * ‖x - y‖ ^ 2 := by
        dsimp [C]; ring
      have h_simp_fun : (fun (s : ℝ) => C * (s ^ 2)) = (fun (s : ℝ) => (Lf / 2) * (s ^ 2) * ‖x - y‖ ^ 2) := by
        ext s; dsimp [C]; ring
      simpa [h_simp_deriv, h_simp_fun] using h_mul
    have h_combined : HasDerivAt (fun (s : ℝ) =>
        h s - h 0 - s * ⟪gradient f y, x - y⟫ - (Lf / 2) * (s ^ 2) * ‖x - y‖ ^ 2)
        (⟪gradient f (φ t), x - y⟫ - 0 - ⟪gradient f y, x - y⟫ - Lf * t * ‖x - y‖ ^ 2) t :=
      ((h1.sub h2).sub h3).sub h4
    simpa [g, sub_sub, inner_sub_left] using h_combined
  -- g is differentiable everywhere → continuous + differentiable on intervals
  have hg_diff (t : ℝ) : DifferentiableAt ℝ g t := (hg_deriv t).differentiableAt
  have hg_cont : Continuous g :=
    continuous_iff_continuousAt.mpr (λ t => (hg_diff t).continuousAt)
  have hg_contOn : ContinuousOn g (Icc (0 : ℝ) 1) := hg_cont.continuousOn
  have hg_diffOn : DifferentiableOn ℝ g (Ioo (0 : ℝ) 1) :=
    fun x hx => (hg_diff x).differentiableWithinAt
  -- g'(t) ≤ 0 for t > 0 (Cauchy-Schwarz + Lipschitz gradient)
  have h_deriv_nonpos {t : ℝ} (ht : 0 < t) :
      ⟪gradient f (φ t) - gradient f y, x - y⟫ - Lf * t * ‖x - y‖ ^ 2 ≤ 0 := by
    have h_cauchy : ⟪gradient f (φ t) - gradient f y, x - y⟫ ≤
        ‖gradient f (φ t) - gradient f y‖ * ‖x - y‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient f (φ t) - gradient f y‖ ≤ Lf * ‖φ t - y‖ := by
      have hlip := hf.grad_lipschitz.norm_sub_le (φ t) y
      have hLf_nn : (Real.toNNReal Lf : ℝ) = Lf := Real.coe_toNNReal Lf (by linarith)
      simpa [hLf_nn] using hlip
    have h_norm_φ : ‖φ t - y‖ = t * ‖x - y‖ := by
      dsimp [φ]; simp [norm_smul, abs_of_pos ht]
    have h_inner_bound : ⟪gradient f (φ t) - gradient f y, x - y⟫ ≤ Lf * t * ‖x - y‖ ^ 2 := by
      calc
        ⟪gradient f (φ t) - gradient f y, x - y⟫ ≤
            ‖gradient f (φ t) - gradient f y‖ * ‖x - y‖ := h_cauchy
        _ ≤ (Lf * ‖φ t - y‖) * ‖x - y‖ := by
          nlinarith [h_lip, norm_nonneg (x - y)]
        _ = (Lf * (t * ‖x - y‖)) * ‖x - y‖ := by rw [h_norm_φ]
        _ = Lf * t * ‖x - y‖ ^ 2 := by ring
    linarith
  -- Mean Value Theorem on [0,1]:
  -- ∃ c ∈ (0,1) : deriv g c = (g(1) - g(0))/(1-0) = g(1) - g(0)
  have h_mvt : ∃ c ∈ Ioo (0 : ℝ) 1, deriv g c = (g 1 - g 0) / (1 - 0) :=
    exists_deriv_eq_slope g (by norm_num : (0 : ℝ) < 1) hg_contOn hg_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have hc_pos : 0 < c := hc.1
  -- deriv g c equals the HasDerivAt formula (g is differentiable at c)
  have h_deriv_c : deriv g c = ⟪gradient f (φ c) - gradient f y, x - y⟫ - Lf * c * ‖x - y‖ ^ 2 :=
    (hg_deriv c).deriv
  -- Since c > 0, g'(c) ≤ 0
  have h_deriv_c_nonpos : deriv g c ≤ 0 := by
    rw [h_deriv_c]; exact h_deriv_nonpos hc_pos
  -- From MVT: deriv g c = (g(1) - g(0))/(1-0) = g(1) - g(0), with g(0) = 0
  have h_denom : (1 : ℝ) - 0 = 1 := by norm_num
  rw [h_denom, div_one, hg0, sub_zero] at hc_eq
  -- hc_eq : deriv g c = g(1), and deriv g c ≤ 0, so g(1) ≤ 0
  have hg1_nonpos : g 1 ≤ 0 := by linarith
  -- Expand g(1) ≤ 0 to get the descent inequality
  dsimp [g, h, φ] at hg1_nonpos
  have h_simp1 : (1 : ℝ) • (x - y) = x - y := by simp
  rw [h_simp1] at hg1_nonpos
  have h_simp2 : y + (x - y) = x := by abel
  rw [h_simp2] at hg1_nonpos
  have h_simp3 : f (y + (0 : ℝ) • (x - y)) = f y := by simp
  rw [h_simp3] at hg1_nonpos
  -- hg1_nonpos : f x - f y - ⟪∇f y, x - y⟫ - (Lf/2)*‖x-y‖² ≤ 0
  -- → f x ≤ f y + ⟪∇f y, x - y⟫ + (Lf/2)*‖x-y‖²
  have h_bound_lf : f x ≤ f y + ⟪gradient f y, x - y⟫ + (Lf / 2) * ‖x - y‖ ^ 2 := by
    linarith
  -- Upgrade from Lf to L (‖x-y‖² ≥ 0 and Lf ≤ L)
  have h_L : Lf / 2 * ‖x - y‖ ^ 2 ≤ L / 2 * ‖x - y‖ ^ 2 := by
    have h_sq_nonneg : 0 ≤ ‖x - y‖ ^ 2 := pow_two_nonneg _
    nlinarith
  linarith
```

## Proof explanation
The proof begins by extracting the positivity of $L_f$:

$$
0<L_f
$$

from `hf.hL_pos`. This is used later when converting a nonnegative real Lipschitz coefficient back to the real number $L_f$.

It then defines the line segment from $y$ to $x$,

$$
\phi(t)=y+t(x-y),
$$

and the pullback functions

$$
h(t)=f(\phi(t)),
$$

and

$$
g(t)=h(t)-h(0)-t\langle \nabla f(y),x-y\rangle-\frac{L_f}{2}t^2\|x-y\|^2.
$$

At $t=0$, one has $\phi(0)=y$, hence $h(0)=f(y)$, and the definition gives $g(0)=0$. The proof checks this by unfolding the local definitions with `dsimp` and simplifying with `simp`.

Next the proof computes the derivative of $h$. For every $t_0\in\mathbb R$, it proves

$$
h'(t_0)=\langle \nabla f(\phi(t_0)),x-y\rangle .
$$

The argument is as follows. Since `hf.contDiff` says $f$ is $C^1$, $f$ is differentiable everywhere; the proof uses this to get differentiability at $\phi(t_0)$. For a differentiable function, the line derivative in direction $x-y$ is the Fréchet derivative applied to $x-y$:

$$
\operatorname{lineDeriv} f(\phi(t_0))(x-y)=Df(\phi(t_0))(x-y).
$$

The lemma `inner_gradient_left` then identifies this directional derivative with the inner product of the gradient:

$$
Df(\phi(t_0))(x-y)=\langle \nabla f(\phi(t_0)),x-y\rangle .
$$

The definition of `HasLineDerivAt` says that the function

$$
s\mapsto f(\phi(t_0)+s(x-y))
$$

has derivative equal to this inner product at $s=0$. Since

$$
\phi(t_0)+s(x-y)=y+(t_0+s)(x-y)=\phi(t_0+s),
$$

the same function is $s\mapsto h(t_0+s)$. Finally, the translation rule for derivatives, invoked through `HasDerivAt.comp_add_const`, turns the derivative at $0$ of $s\mapsto h(t_0+s)$ into the derivative at $t_0$ of $h$. Thus $h'(t_0)$ is exactly the stated inner product.

Then the proof computes the derivative of $g$. For every $t$,

$$
g'(t)=\langle \nabla f(\phi(t))-\nabla f(y),x-y\rangle-L_f\,t\,\|x-y\|^2 .
$$

This is obtained by combining four derivative facts:
- $h'(t)=\langle \nabla f(\phi(t)),x-y\rangle$, already proved;
- the derivative of the constant $h(0)$ is $0$;
- the derivative of $t\mapsto t\langle \nabla f(y),x-y\rangle$ is $\langle \nabla f(y),x-y\rangle$;
- the derivative of

  $$
  t\mapsto \frac{L_f}{2}t^2\|x-y\|^2
  $$

  is $L_f\,t\,\|x-y\|^2$.

For the last item, the proof sets $C=(L_f/2)\|x-y\|^2$ and uses the derivative of $t^2$, namely $2t$, together with the constant-multiple rule. This gives derivative $C(2t)=L_f\,t\,\|x-y\|^2$. The subtraction of these derivatives gives

$$
\langle \nabla f(\phi(t)),x-y\rangle
-\langle \nabla f(y),x-y\rangle
-L_f\,t\,\|x-y\|^2,
$$

and linearity of the inner product in its first argument rewrites the first two terms as

$$
\langle \nabla f(\phi(t))-\nabla f(y),x-y\rangle.
$$

The algebraic identities are closed by `ring`, and the final form by `simpa`.

From the explicit derivative formula, the proof knows $g$ is differentiable at every point, hence continuous at every point, hence continuous on $[0,1]$. It is also differentiable on the open interval $(0,1)$. The continuity conclusion uses `continuous_iff_continuousAt`: a function is continuous if and only if it is continuous at each point.

The central estimate is that for $t>0$,

$$
\langle \nabla f(\phi(t))-\nabla f(y),x-y\rangle-L_f\,t\,\|x-y\|^2\le 0.
$$

To prove this, the proof uses Cauchy–Schwarz for the real inner product:

$$
\langle u,v\rangle\le \|u\|\|v\|,
$$

with $u=\nabla f(\phi(t))-\nabla f(y)$ and $v=x-y$. The Lipschitz-gradient hypothesis supplies

$$
\|\nabla f(\phi(t))-\nabla f(y)\|\le L_f\|\phi(t)-y\|.
$$

Because $\phi(t)-y=t(x-y)$, and $t>0$,

$$
\|\phi(t)-y\|=\|t(x-y)\|=t\|x-y\|.
$$

Combining these inequalities gives

$$
\langle \nabla f(\phi(t))-\nabla f(y),x-y\rangle
\le L_f\,t\,\|x-y\|^2.
$$

Subtracting the same quantity on the right yields the desired nonpositivity. The proof uses `nlinarith` and `ring` here to combine the norm estimates and rewrite the final polynomial expression.

Next, the mean value theorem is applied to $g$ on $[0,1]$. The lemma `exists_deriv_eq_slope` gives a point $c\in(0,1)$ such that

$$
g'(c)=\frac{g(1)-g(0)}{1-0}.
$$

Since $g(0)=0$, this simplifies to

$$
g'(c)=g(1).
$$

Because $c>0$, the previously proved nonpositivity of the derivative at positive points gives $g'(c)\le 0$. Therefore $g(1)\le 0$.

Finally, the proof expands $g(1)\le 0$. Since

$$
\phi(1)=y+(x-y)=x,\qquad \phi(0)=y,
$$

one has $h(1)=f(x)$ and $h(0)=f(y)$. Thus

$$
g(1)=f(x)-f(y)-\langle \nabla f(y),x-y\rangle-\frac{L_f}{2}\|x-y\|^2\le 0.
$$

Rearranging gives

$$
f(x)\le f(y)+\langle \nabla f(y),x-y\rangle+\frac{L_f}{2}\|x-y\|^2.
$$

The proof uses `linarith` to perform this rearrangement.

To pass from $L_f$ to the larger constant $L$, the proof uses $L_f\le L$ and $\|x-y\|^2\ge 0$ to obtain

$$
\frac{L_f}{2}\|x-y\|^2\le \frac{L}{2}\|x-y\|^2.
$$

Combining this with the bound involving $L_f$, again by `linarith`, yields the claimed inequality with $L$:

$$
f(x)\le f(y)+\langle \nabla f(y),x-y\rangle+\frac{L}{2}\|x-y\|^2.
$$

No `intro` tactic occurs in this proof, because the variables and hypotheses are already parameters of the theorem statement and are therefore already in the context. The commands `rw`, `simp`, `dsimp`, `ring`, `nlinarith`, and `linarith` are used to rewrite definitions, simplify arithmetic, prove polynomial identities, and combine inequalities.

