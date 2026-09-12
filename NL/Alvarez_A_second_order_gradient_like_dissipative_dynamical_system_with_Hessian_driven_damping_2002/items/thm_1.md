## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_1.lean`

## Lean statement
```lean
theorem din_global_properties_part_iii {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ)
    (hΦ : AssumptionH H Φ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (x₀ v₀ : H) (x : ℝ → H)
    (hx0 : x 0 = x₀) (hv0 : deriv x 0 = v₀)
    (hforward : IsDINTrajectory H Φ α β x)
    (hxreg : ContDiff ℝ 2 x) :
    Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) →
      Bornology.IsBounded ((deriv x) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((deriv (deriv x)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧ Tendsto (deriv (deriv x)) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0)
```

## Statement explanation
This declaration concerns a second-order gradient-like dissipative dynamical system in a real Hilbert space $H$. The data are a potential $\Phi:H\to \mathbb R$, positive parameters $\alpha,\beta>0$, initial position $x_0\in H$, initial velocity $v_0\in H$, and a curve $x:\mathbb R\to H$. The hypothesis `hΦ : AssumptionH H Φ` is the standing assumption on $\Phi$ required by the theory; its internal definition is not expanded in the supplied source. The hypotheses on $x$ are that $x(0)=x_0$, that $\dot x(0)=v_0$, that $x$ is a DIN trajectory for $\Phi,\alpha,\beta$, and that $x$ is twice continuously differentiable, $x\in C^2$.

The conclusion is an implication. If the image of $x$ over nonnegative times is bounded,

$$
\mathrm{IsBounded}\bigl(x([0,\infty))\bigr),
$$

then the following seven facts hold. The velocity image, the acceleration image, the gradient image, and the Hessian image are all bounded:

$$
\mathrm{IsBounded}\bigl(\dot x([0,\infty))\bigr),\qquad
\mathrm{IsBounded}\bigl(\ddot x([0,\infty))\bigr),
$$

$$
\mathrm{IsBounded}\bigl((\nabla\Phi\circ x)([0,\infty))\bigr),\qquad
\mathrm{IsBounded}\bigl((D(\nabla\Phi)\circ x)([0,\infty))\bigr),
$$

where $D(\nabla\Phi)(x(t))$ is the Fréchet derivative of $\nabla\Phi$ at $x(t)$, i.e. the Hessian as a continuous linear map. Moreover, the velocity, acceleration, and gradient tend to zero as $t\to\infty$:

$$
\dot x(t)\to 0,\qquad \ddot x(t)\to 0,\qquad \nabla\Phi(x(t))\to 0.
$$

No conclusion is asserted about the Hessian itself tending to zero; only its boundedness is claimed.

## Lean proof
```lean
by
  intro hxbound
  have hxC2 : ContDiff ℝ (1 + 1) x := by simpa using hxreg
  have hxdata := contDiff_succ_iff_deriv.mp hxC2
  rcases din_forward_internal Φ hΦ α β hα hβ x₀ v₀ with
    ⟨xg, vg, accg, hxg0, hvg0, hforwardg, huniq, -, -, -, -, -, hboundedg, hderivg⟩
  have hsame := huniq x hx0 hv0 hforward hxreg
  have hx_eq : ∀ t, 0 ≤ t → x t = xg t := fun t ht => (hsame t ht).1
  have hv_eq : ∀ t, 0 ≤ t → deriv x t = vg t := fun t ht => (hsame t ht).2
  have hxgbound : Bornology.IsBounded (xg '' Set.Ici (0 : ℝ)) := by
    rcases isBounded_iff_forall_norm_le.mp hxbound with ⟨R, hR⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    rw [← hx_eq t ht]
    exact hR _ ⟨t, ht, rfl⟩
  rcases hboundedg hxgbound with
    ⟨hvboundg, haccboundg, hgradboundg, hhessboundg, hvlimg, hacclimg, hgradlimg⟩
  have hacc_formula : ∀ t, 0 ≤ t →
      deriv (deriv x) t = -(α • deriv x t +
        β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t)) := by
    intro t ht
    have he := hforward.2.2 t ht
    exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using he)
  have hvbound : Bornology.IsBounded ((deriv x) '' Set.Ici (0 : ℝ)) := by
    have himage : (deriv x) '' Set.Ici (0 : ℝ) = vg '' Set.Ici (0 : ℝ) :=
      Set.image_congr (fun t ht => hv_eq t ht)
    rw [himage]
    exact hvboundg
  have hgradbound : Bornology.IsBounded
      ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) := by
    have himage : (fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ) =
        (fun t => gradient Φ (xg t)) '' Set.Ici (0 : ℝ) :=
      Set.image_congr (fun t ht => by simp [hx_eq t ht])
    rw [himage]
    exact hgradboundg
  have hhessbound : Bornology.IsBounded
      ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) := by
    have himage : (fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ) =
        (fun t => fderiv ℝ (gradient Φ) (xg t)) '' Set.Ici (0 : ℝ) :=
      Set.image_congr (fun t ht => by simp [hx_eq t ht])
    rw [himage]
    exact hhessboundg
  rcases isBounded_iff_forall_norm_le.mp hhessbound with ⟨Q, hQ⟩
  have haccbound : Bornology.IsBounded ((deriv (deriv x)) '' Set.Ici (0 : ℝ)) := by
    rcases isBounded_iff_forall_norm_le.mp hvbound with ⟨V, hV⟩
    rcases isBounded_iff_forall_norm_le.mp hgradbound with ⟨G, hG⟩
    have hQnonneg : 0 ≤ Q := le_trans (norm_nonneg _) (hQ _ ⟨0, by simp, rfl⟩)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|α| * V + |β| * Q * V + G, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hv : ‖deriv x t‖ ≤ V := hV _ ⟨t, ht, rfl⟩
    have hg : ‖gradient Φ (x t)‖ ≤ G := hG _ ⟨t, ht, rfl⟩
    have hq : ‖fderiv ℝ (gradient Φ) (x t)‖ ≤ Q := hQ _ ⟨t, ht, rfl⟩
    rw [hacc_formula t ht]
    calc
      ‖-(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t))‖ ≤
        ‖α • deriv x t‖ + ‖β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ + ‖gradient Φ (x t)‖ := by
          rw [norm_neg]
          calc
            ‖α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t)‖ ≤
              ‖α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ + ‖gradient Φ (x t)‖
                := norm_add_le _ _
            _ ≤ ‖α • deriv x t‖ + ‖β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ +
              ‖gradient Φ (x t)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ |α| * V + |β| * Q * V + G := by
        rw [norm_smul, norm_smul]
        calc
          ‖α‖ * ‖deriv x t‖ + ‖β‖ * ‖(fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ +
              ‖gradient Φ (x t)‖ ≤
              ‖α‖ * V + ‖β‖ * (Q * V) + G := by
                gcongr
                exact (ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul hq hv (norm_nonneg _) hQnonneg)
          _ = |α| * V + |β| * Q * V + G := by
            simp only [Real.norm_eq_abs]
            ring
  have hvlim : Tendsto (deriv x) atTop (nhds 0) := by
    apply hvlimg.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => ht⟩] with t ht
    exact (hv_eq t ht).symm
  have hgradlim : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
    apply hgradlimg.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => ht⟩] with t ht
    simp [hx_eq t ht]
  have hacclim : Tendsto (deriv (deriv x)) atTop (nhds 0) := by
    have hvlim' : Tendsto (deriv x) atTop (nhds 0) := hvlim
    have hgradlim' : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := hgradlim
    have hesslim : Tendsto (fun t => (fderiv ℝ (gradient Φ) (x t)) (deriv x t)) atTop (nhds 0) := by
      apply bounded_clm_apply_tendsto_zero (fun t => fderiv ℝ (gradient Φ) (x t)) (deriv x) Q
      · filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => hQ _ ⟨t, ht, rfl⟩⟩] with t ht
        exact ht
      · exact hvlim'
    have hsumlim : Tendsto
        (fun t => -(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
          gradient Φ (x t))) atTop (nhds 0) := by
      simpa using (((hvlim'.const_smul α).add (hesslim.const_smul β)).add hgradlim').neg
    apply hsumlim.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hacc_formula t ht).symm
  exact ⟨hvbound, haccbound, hgradbound, hhessbound, hvlim, hacclim, hgradlim⟩
```

## Proof explanation
The proof begins with `intro hxbound`, assuming that $x([0,\infty))$ is bounded. It then rewrites $2$ as $1+1$ and applies `contDiff_succ_iff_deriv` to $hxreg$. This lemma expresses that $C^{n+1}$ differentiability is equivalent to differentiability together with $C^n$ differentiability of the derivative. Here it would give that $x$ is differentiable and $\dot x$ is $C^1$. The resulting local fact `hxdata` is not used later in the proof.

Next, the proof invokes `din_forward_internal` specialized to $\Phi,\alpha,\beta,x_0,v_0$. This theorem supplies functions $x_g,v_g,acc_g:\mathbb R\to H$ and a long conjunction. The proof destructures the relevant parts as follows. It obtains $x_g(0)=x_0$, $v_g(0)=v_0$, and that $x_g$ is a DIN trajectory. It obtains a uniqueness statement `huniq`: for any $x'$ with $x'(0)=x_0$, $\dot x'(0)=v_0$, which is a DIN trajectory and $C^2$, one has for all $t\ge0$

$$
x'(t)=x_g(t),\qquad \dot x'(t)=v_g(t).
$$

It also obtains `hboundedg`, the implication that if $x_g([0,\infty))$ is bounded, then

$$
v_g([0,\infty)),\quad acc_g([0,\infty)),\quad
(\nabla\Phi\circ x_g)([0,\infty)),\quad
(D(\nabla\Phi)\circ x_g)([0,\infty))
$$

are all bounded, and $v_g(t)\to0$, $acc_g(t)\to0$, $\nabla\Phi(x_g(t))\to0$. The parts of `din_forward_internal` discarded by underscores include energy monotonicity, $L^2$ integrability, and the limit of $\Phi(x_g(t))$; they are not needed here.

The proof then applies `huniq` to the original curve $x$, using $hx0,hv0,hforward,hxreg$. This gives `hsame`, hence for every $t\ge0$,

$$
x(t)=x_g(t),\qquad \dot x(t)=v_g(t).
$$

The first equality is named `hx_eq` and the second `hv_eq`.

To transfer boundedness from $x$ to $x_g$, the proof uses `isBounded_iff_forall_norm_le`. From boundedness of $x([0,\infty))$ it obtains a constant $R$ such that $\|z\|\le R$ for every $z\in x([0,\infty))$. To show the same $R$ bounds $x_g([0,\infty))$, take $z=x_g(t)$ with $t\ge0$. Since $x_g(t)=x(t)$, the bound for $x$ gives $\|x_g(t)\|\le R$. Thus `hxgbound` is proved.

Applying `hboundedg` to `hxgbound` yields bounds and limits for $v_g$, $acc_g$, $\nabla\Phi\circ x_g$, and $D(\nabla\Phi)\circ x_g$. The proof names these `hvboundg`, `haccboundg`, `hgradboundg`, `hhessboundg`, `hvlimg`, `hacclimg`, and `hgradlimg`. The acceleration bound and limit for $acc_g$ are not used later; the needed acceleration facts for $\ddot x$ will be derived directly from the differential equation.

The central differential relation is extracted from `hforward.2.2 t ht`. At every $t\ge0$, the trajectory condition gives the second-order equation in the form

$$
\ddot x(t)
=
-\Bigl(
\alpha\,\dot x(t)
+\beta\,\bigl(D(\nabla\Phi)(x(t))\bigr)(\dot x(t))
+\nabla\Phi(x(t))
\Bigr).
$$

This is `hacc_formula`. The proof obtains it by taking the equality supplied by `hforward.2.2 t ht`, reassociating with `add_assoc`, and applying `eq_neg_of_add_eq_zero_left`, which says that if $A+B=0$, then $B=-A$.

The velocity bound is transferred next. Using `hv_eq` on $t\ge0$, the proof identifies the images

$$
\dot x([0,\infty))=v_g([0,\infty)).
$$

The lemma `Set.image_congr` is the formal tool: pointwise equality on a set implies equality of the corresponding image sets. Therefore the boundedness of $v_g([0,\infty))$ gives boundedness of $\dot x([0,\infty))$. Similarly, using $x(t)=x_g(t)$ for $t\ge0$, the proof identifies

$$
(\nabla\Phi\circ x)([0,\infty))=(\nabla\Phi\circ x_g)([0,\infty))
$$

and

$$
(D(\nabla\Phi)\circ x)([0,\infty))=(D(\nabla\Phi)\circ x_g)([0,\infty)),
$$

so the corresponding boundedness facts transfer from $x_g$ to $x$.

To bound the acceleration, the proof extracts constants $V$, $G$, and $Q$ such that for all $t\ge0$,

$$
\|\dot x(t)\|\le V,\qquad
\|\nabla\Phi(x(t))\|\le G,\qquad
\|D(\nabla\Phi)(x(t))\|\le Q.
$$

The first comes from the velocity bound, the second from the gradient bound, and the third from the Hessian bound. The proof also checks $Q\ge0$, since $0\le \|D(\nabla\Phi)(x(0))\|\le Q$. Then, using `hacc_formula`,

$$
\|\ddot x(t)\|
\le
\|\alpha\,\dot x(t)\|
+\|\beta\,(D(\nabla\Phi)(x(t)))(\dot x(t))\|
+\|\nabla\Phi(x(t))\|.
$$

The triangle inequality is used through `norm_add_le`, and `norm_neg` removes the outer minus sign. Then `norm_smul` converts $\|\alpha y\|$ and $\|\beta y\|$ into $|\alpha|\|y\|$ and $|\beta|\|y\|$, using `Real.norm_eq_abs`. For the Hessian term, `ContinuousLinearMap.le_opNorm` gives

$$
\|(D(\nabla\Phi)(x(t)))(\dot x(t))\|
\le
\|D(\nabla\Phi)(x(t))\|\,\|\dot x(t)\|
\le QV.
$$

Together with $\|\dot x(t)\|\le V$ and $\|\nabla\Phi(x(t))\|\le G$, this yields

$$
\|\ddot x(t)\|\le |\alpha|V+|\beta|QV+G.
$$

The tactic `gcongr` handles the monotone combination of these inequalities, and `ring` normalizes the final arithmetic expression. Hence the acceleration image is bounded.

The velocity limit is transferred by eventual equality. Since $\dot x(t)=v_g(t)$ for all $t\ge0$, and $t\ge0$ holds eventually at infinity, `Tendsto.congr'` lets the limit $v_g(t)\to0$ imply $\dot x(t)\to0$. Similarly, because $\nabla\Phi(x(t))=\nabla\Phi(x_g(t))$ eventually, the limit $\nabla\Phi(x_g(t))\to0$ transfers to $\nabla\Phi(x(t))\to0$.

For the acceleration limit, the proof first shows

$$
t\mapsto (D(\nabla\Phi)(x(t)))(\dot x(t))\to 0.
$$

It uses `bounded_clm_apply_tendsto_zero`, which states that if $q(t)$ is a family of continuous linear operators eventually bounded in operator norm by a constant $C$, and $v(t)\to0$, then $q(t)(v(t))\to0$. Here $q(t)=D(\nabla\Phi)(x(t))$, $v(t)=\dot x(t)$, and $C=Q$. The eventual bound is supplied by the Hessian estimate, and the limit $\dot x(t)\to0$ was already proved.

Now $\alpha\,\dot x(t)\to0$, $\beta\,(D(\nabla\Phi)(x(t)))(\dot x(t))\to0$, and $\nabla\Phi(x(t))\to0$. The proof combines these using continuity of scalar multiplication, addition, and negation: `const_smul`, `.add`, and `.neg`. Thus

$$
-\Bigl(
\alpha\,\dot x(t)
+\beta\,(D(\nabla\Phi)(x(t)))(\dot x(t))
+\nabla\Phi(x(t))
\Bigr)\to0.
$$

Since `hacc_formula` says that this expression equals $\ddot x(t)$ for all $t\ge0$, and $t\ge0$ eventually, another application of `Tendsto.congr'` gives $\ddot x(t)\to0$.

Finally, the proof assembles the seven conclusions in the required order:

$$
\mathrm{IsBounded}(\dot x([0,\infty))),
\quad
\mathrm{IsBounded}(\ddot x([0,\infty))),
\quad
\mathrm{IsBounded}((\nabla\Phi\circ x)([0,\infty))),
$$

$$
\mathrm{IsBounded}((D(\nabla\Phi)\circ x)([0,\infty))),
\quad
\dot x(t)\to0,
\quad
\ddot x(t)\to0,
\quad
\nabla\Phi(x(t))\to0.
$$

These are exactly `hvbound`, `haccbound`, `hgradbound`, `hhessbound`, `hvlim`, `hacclim`, and `hgradlim`.

