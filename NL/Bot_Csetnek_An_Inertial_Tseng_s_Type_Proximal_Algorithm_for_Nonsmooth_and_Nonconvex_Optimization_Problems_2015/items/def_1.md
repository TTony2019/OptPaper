## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/def_1.lean`

## Lean statement
```lean
theorem limitingSubdifferential_smooth_sum_rule {m : Nat}
    (f : EuclideanSpace m -> EReal) (h : EuclideanSpace m -> Real)
    (x : EuclideanSpace m) (hf : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f) (hh : ContDiff Real 1 h) :
    limitingSubdifferential (objectiveSum f h) x =
      {v | ∃ w ∈ limitingSubdifferential f x, v = w + gradient h x}
```

## Statement explanation
Fix $m\in\mathbb N$. Let $f:\mathbb R^m\to \overline{\mathbb R}$ be an extended-real-valued function, let $h:\mathbb R^m\to \mathbb R$ be real-valued, and let $x\in\mathbb R^m$. The hypotheses are that $f$ is proper, that $f$ is lower semicontinuous, and that $h$ is continuously differentiable of order $1$, i.e. $h\in C^1$. The objective sum is the extended-real-valued function

$$
(f+h)(y)=f(y)+h(y),
$$

where the real number $h(y)$ is regarded inside $\overline{\mathbb R}$; this is the Lean definition `objectiveSum`.

Let $\partial_L$ denote the limiting, or Mordukhovich, subdifferential, and let $\hat\partial$ denote the Fréchet subdifferential. The theorem states

$$
\partial_L(f+h)(x)
=\left\{\,v\in\mathbb R^m \;\middle|\; \exists w\in \partial_L f(x),\; v=w+\nabla h(x)\,\right\}.
$$

Thus the limiting subgradients of the sum $f+h$ at $x$ are exactly the limiting subgradients of $f$ at $x$, each shifted by the gradient $\nabla h(x)$ of the smooth summand. Since $h$ is finite-valued, adding it does not change effective domains:

$$
y\in\mathrm{dom}(f+h) \iff y\in\mathrm{dom} f.
$$

The statement includes properness and lower semicontinuity of $f$, but the formal proof below does not invoke those two hypotheses.

## Lean proof
```lean
by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨hobj_eff, zs, us, hzs, hobjVal, husFrechet, hus⟩
    have hx_eff : x ∈ ERealFunction.effectiveDom f :=
      (objectiveSum_effectiveDom_iff f h x).1 hobj_eff
    have hzs_eff : ∀ n, zs n ∈ ERealFunction.effectiveDom f := by
      intro n
      exact (objectiveSum_effectiveDom_iff f h (zs n)).1 (husFrechet n).1
    have hh_tendsto : Tendsto (fun n => h (zs n)) atTop (nhds (h x)) :=
      (hh.continuous.tendsto x).comp hzs
    have hfVal : Tendsto (fun n => f (zs n)) atTop (nhds (f x)) :=
      (objectiveSum_value_tendsto_iff hzs_eff hx_eff hh_tendsto).1 hobjVal
    have hfrechet :
        ∀ n, us n - gradient h (zs n) ∈ frechetSubdifferential f (zs n) := by
      intro n
      exact frechetSubdifferential_objective_forward hh (husFrechet n)
    have hgrad : Tendsto (fun n => gradient h (zs n)) atTop
        (nhds (gradient h x)) :=
      gradient_tendsto_of_contDiff_one hh hzs
    have hsubgrad : Tendsto (fun n => us n - gradient h (zs n)) atTop
        (nhds (v - gradient h x)) :=
      hus.sub hgrad
    refine ⟨v - gradient h x, ?_, by simp⟩
    exact ⟨hx_eff, zs, fun n => us n - gradient h (zs n), hzs, hfVal,
      hfrechet, hsubgrad⟩
  · intro hv
    rcases hv with ⟨w, hw, rfl⟩
    rcases hw with ⟨hx_eff, zs, ws, hzs, hfVal, hwsFrechet, hws⟩
    have hobj_eff : x ∈ ERealFunction.effectiveDom (objectiveSum f h) :=
      (objectiveSum_effectiveDom_iff f h x).2 hx_eff
    have hzs_eff : ∀ n, zs n ∈ ERealFunction.effectiveDom f := by
      intro n
      exact (hwsFrechet n).1
    have hh_tendsto : Tendsto (fun n => h (zs n)) atTop (nhds (h x)) :=
      (hh.continuous.tendsto x).comp hzs
    have hobjVal :
        Tendsto (fun n => objectiveSum f h (zs n)) atTop
          (nhds (objectiveSum f h x)) :=
      (objectiveSum_value_tendsto_iff hzs_eff hx_eff hh_tendsto).2 hfVal
    have hfrechet :
        ∀ n, ws n + gradient h (zs n) ∈
          frechetSubdifferential (objectiveSum f h) (zs n) := by
      intro n
      exact frechetSubdifferential_objective_reverse hh (hwsFrechet n)
    have hgrad : Tendsto (fun n => gradient h (zs n)) atTop
        (nhds (gradient h x)) :=
      gradient_tendsto_of_contDiff_one hh hzs
    have hsubgrad : Tendsto (fun n => ws n + gradient h (zs n)) atTop
        (nhds (w + gradient h x)) :=
      hws.add hgrad
    exact ⟨hobj_eff, zs, fun n => ws n + gradient h (zs n), hzs, hobjVal,
      hfrechet, hsubgrad⟩
```

## Proof explanation
This declaration has a proof. It proves the set equality by extensionality. The command `ext v` reduces the goal to showing, for each vector $v$, that

$$
v\in \partial_L(f+h)(x)
\iff
\exists w\in \partial_L f(x),\; v=w+\nabla h(x).
$$

The command `constructor` splits this equivalence into two implications.

First inclusion. Assume

$$
v\in \partial_L(f+h)(x).
$$

The proof unpacks this assumption as follows: $x\in\mathrm{dom}(f+h)$, there are sequences $z_n$ and $u_n$, one has $z_n\to x$, $u_n\to v$, $(f+h)(z_n)\to (f+h)(x)$, and for every $n$,

$$
u_n\in \hat\partial(f+h)(z_n).
$$

The Lean names for these data are `hobj_eff`, `zs`, `us`, `hzs`, `hobjVal`, `husFrechet`, and `hus`.

Applying `objectiveSum_effectiveDom_iff` to $x$ gives

$$
x\in\mathrm{dom}(f+h) \iff x\in\mathrm{dom} f.
$$

Since $x\in\mathrm{dom}(f+h)$, the result is $x\in\mathrm{dom} f$. Similarly, for every $n$, because $u_n\in \hat\partial(f+h)(z_n)$, the definition of the Fréchet subdifferential includes $z_n\in\mathrm{dom}(f+h)$. Applying `objectiveSum_effectiveDom_iff` again gives

$$
z_n\in\mathrm{dom} f
$$

for every $n$.

Next, since $h$ is $C^1$, it is continuous. The command `(hh.continuous.tendsto x).comp hzs` composes the convergence $z_n\to x$ with continuity of $h$ at $x$, giving

$$
h(z_n)\to h(x).
$$

Now apply `objectiveSum_value_tendsto_iff` to the sequences $z_n$, with the facts $z_n\in\mathrm{dom} f$, $x\in\mathrm{dom} f$, and $h(z_n)\to h(x)$. That theorem states that, under these hypotheses,

$$
(f+h)(z_n)\to (f+h)(x)
\iff
f(z_n)\to f(x).
$$

Since $(f+h)(z_n)\to (f+h)(x)$, the proof obtains

$$
f(z_n)\to f(x).
$$

For each $n$, the lemma `frechetSubdifferential_objective_forward` is applied to $h$ and to the membership $u_n\in \hat\partial(f+h)(z_n)$. Its mathematical content is the Fréchet-level smooth sum rule: if $h$ is $C^1$ and $u\in \hat\partial(f+h)(y)$, then

$$
u-\nabla h(y)\in \hat\partial f(y).
$$

Specializing to $y=z_n$ and $u=u_n$, this gives

$$
u_n-\nabla h(z_n)\in \hat\partial f(z_n)
$$

for every $n$.

The lemma `gradient_tendsto_of_contDiff_one` says that a $C^1$ function has continuous gradient along convergent sequences: from $z_n\to x$ it gives

$$
\nabla h(z_n)\to \nabla h(x).
$$

Since $u_n\to v$ and $\nabla h(z_n)\to \nabla h(x)$, the continuity of subtraction in $\mathbb R^m$ yields

$$
u_n-\nabla h(z_n)\to v-\nabla h(x).
$$

The proof chooses

$$
w=v-\nabla h(x).
$$

The facts $x\in\mathrm{dom} f$, $z_n\to x$, $f(z_n)\to f(x)$, the Fréchet memberships $u_n-\nabla h(z_n)\in \hat\partial f(z_n)$, and the convergence $u_n-\nabla h(z_n)\to w$ together witness

$$
w\in \partial_L f(x).
$$

Finally, the required equality $v=w+\nabla h(x)$ is the algebraic identity

$$
v=(v-\nabla h(x))+\nabla h(x),
$$

which is discharged by `simp`. Hence $v$ belongs to the right-hand set.

Second inclusion. Assume

$$
v\in \left\{\,v \;\middle|\; \exists w\in \partial_L f(x),\; v=w+\nabla h(x)\,\right\}.
$$

The proof unpacks this as the existence of $w\in\partial_L f(x)$ such that $v=w+\nabla h(x)$. The `rfl` pattern in `rcases` uses this equality to replace $v$ by $w+\nabla h(x)$, so it remains to prove

$$
w+\nabla h(x)\in \partial_L(f+h)(x).
$$

The membership $w\in\partial_L f(x)$ is unpacked as: $x\in\mathrm{dom} f$, sequences $z_n$ and $w_n$, with $z_n\to x$, $w_n\to w$, $f(z_n)\to f(x)$, and for every $n$,

$$
w_n\in \hat\partial f(z_n).
$$

Applying `objectiveSum_effectiveDom_iff` in the reverse direction gives

$$
x\in\mathrm{dom}(f+h).
$$

For each $n$, the Fréchet membership $w_n\in \hat\partial f(z_n)$ includes $z_n\in\mathrm{dom} f$. As before, continuity of $h$ and $z_n\to x$ give

$$
h(z_n)\to h(x).
$$

Now `objectiveSum_value_tendsto_iff` is used in the reverse direction: from $f(z_n)\to f(x)$, together with the effective-domain facts and $h(z_n)\to h(x)$, it gives

$$
(f+h)(z_n)\to (f+h)(x).
$$

For each $n$, the lemma `frechetSubdifferential_objective_reverse` is applied to $h$ and to $w_n\in\hat\partial f(z_n)$. Its content is the converse Fréchet smooth sum rule: if $h$ is $C^1$ and $w\in\hat\partial f(y)$, then

$$
w+\nabla h(y)\in \hat\partial(f+h)(y).
$$

Specializing to $y=z_n$ and $w=w_n$, this gives

$$
w_n+\nabla h(z_n)\in \hat\partial(f+h)(z_n)
$$

for every $n$.

Again `gradient_tendsto_of_contDiff_one` gives

$$
\nabla h(z_n)\to \nabla h(x).
$$

Since $w_n\to w$, continuity of addition yields

$$
w_n+\nabla h(z_n)\to w+\nabla h(x).
$$

The facts $x\in\mathrm{dom}(f+h)$, $z_n\to x$, $(f+h)(z_n)\to(f+h)(x)$, the Fréchet memberships $w_n+\nabla h(z_n)\in\hat\partial(f+h)(z_n)$, and the convergence $w_n+\nabla h(z_n)\to w+\nabla h(x)$ together witness

$$
w+\nabla h(x)\in \partial_L(f+h)(x).
$$

This is exactly the goal. The final `exact` supplies the full witness tuple for membership in `limitingSubdifferential`.

Thus both inclusions hold, so the two sets are equal. The proof uses `ext`, `constructor`, `intro`, `rcases`, `have`, `refine`, `exact`, `simp`, and the sequence-continuity operations `.sub` and `.add`; it does not use `rw` or `linarith`.

