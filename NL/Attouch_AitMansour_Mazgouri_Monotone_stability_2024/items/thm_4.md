## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_4.lean`

## Lean statement
```lean
theorem thm_4 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (r T : ℝ)
    (hr : 0 < r) (hT : 0 < T)
    (hsol : ∀ μ, μ ∈ V →
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hball : ∀ μ, μ ∈ V → ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ r)
    (hdist : ∀ μ, μ ∈ V → ∀ μ', μ' ∈ V →
      let d := def_8 r hr (A μ) (A μ')
      0 ≤ d ∧ ∀ u v : H, ‖u‖ ≤ r → ‖v‖ ≤ r →
        ‖A μ u - A μ' v‖ ≤ d * ‖u - v‖) :
    ∀ μ, μ ∈ V → ∀ μ', μ' ∈ V →
      let d
```

## Statement explanation
The declaration `thm_4` is a stability estimate for a parametrized family of second-order differential equations in a real inner product space $H$. The parameter space is an arbitrary set $V\subseteq M$, where $M$ is only a normed additive commutative group. For each parameter $\mu$, the data are a position curve $x_\mu:\mathbb R\to H$, a velocity curve $dx_\mu$, an acceleration curve $ddx_\mu$, and initial position and velocity $u_0(\mu),v_0(\mu)\in H$. The map $A_\mu=A(\mu):H\to H$ is the nonlinear force, and $\gamma\in\mathbb R$ is a damping coefficient. To simplify notation, write $v_\mu(t)$ for `dx μ t` and $a_\mu(t)$ for `ddx μ t`.

The hypotheses are as follows. First, $r>0$ and $T>0$. Second, `hsol` asserts that for every $\mu\in V$, the condition `ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ)` holds. The proof does not use the full internal definition of `ext_def_2`; it unpacks it into six facts: $x_\mu$ and $v_\mu$ are absolutely continuous on intervals $[0,T]$ for every $T>0$; $x_\mu(0)=u_0(\mu)$; $v_\mu(0)=v_0(\mu)$; and almost everywhere on $[0,\infty)$, the derivative relations

$$
x_\mu'(t)=v_\mu(t),\qquad v_\mu'(t)=a_\mu(t)
$$

hold, and the second-order equation

$$
a_\mu(t)+\gamma v_\mu(t)+A_\mu(x_\mu(t))=0
$$

holds. Third, `hball` says that for each $\mu\in V$, for almost every $t$ with respect to Lebesgue measure, if $t\in[0,T]$, then

$$
\|x_\mu(t)\|\le r.
$$

Thus both trajectories remain almost everywhere in the ball of radius $r$ on the time interval. Fourth, `hdist` says that for all $\mu,\mu'\in V$, if $d$ is the value `def_8 r hr (A μ) (A μ')`, then $d\ge 0$, and for all $u,v\in H$ with $\|u\|\le r$ and $\|v\|\le r$,

$$
\|A_\mu u-A_{\mu'}v\|\le d\|u-v\|.
$$

The identifier `def_8` is only an abbreviation for `ratioDistanceOnBall r hr (A μ) (A μ')`; the proof uses only the two properties just stated, not any further formula for `ratioDistanceOnBall`.

The conclusion is that for all $\mu,\mu'\in V$, with $d$ as above and

$$
c=2\sqrt{1+2\gamma^2+2d^2},
$$

for almost every $t$, if $t\in[0,T]$, then

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}\,
e^{cT}.
$$

So the distance between two solution trajectories at time $t$ is controlled by the initial phase-space distance between their initial positions and velocities, with exponential growth factor depending on the damping $\gamma$, the radius $r$, and the local force-difference quantity $d$.

## Lean proof
```lean
def_8 r hr (A μ) (A μ')
      let c := 2 * Real.sqrt (1 + 2 * γ ^ 2 + 2 * d ^ 2)
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
            Real.exp (c * T) := by
  intro μ hμ μ' hμ'
  dsimp only
  let d := def_8 r hr (A μ) (A μ')
  let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 * d ^ 2)
  change ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
    ‖x μ t - x μ' t‖ ≤
      Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
        Real.exp ((2 * m) * T)
  obtain ⟨hd0, hdist_bound⟩ := hdist μ hμ μ' hμ'
  change 0 ≤ d at hd0
  change ∀ u v : H, ‖u‖ ≤ r → ‖v‖ ≤ r →
    ‖A μ u - A μ' v‖ ≤ d * ‖u - v‖ at hdist_bound
  obtain ⟨_, hdefμ⟩ := hsol μ hμ
  obtain ⟨_, hdefμ'⟩ := hsol μ' hμ'
  rcases hdefμ with ⟨hlacμ, hx0μ, hdx0μ, hxderivμ, hdxderivμ, hodeμ⟩
  rcases hdefμ' with
    ⟨hlacμ', hx0μ', hdx0μ', hxderivμ', hdxderivμ', hodeμ'⟩
  obtain ⟨hxACμ, hdxACμ⟩ := hlacμ T hT
  obtain ⟨hxACμ', hdxACμ'⟩ := hlacμ' T hT
  have hxderivμ_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderivμ
  have hxderivμ'_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderivμ'
  have hdxderivμ_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderivμ
  have hdxderivμ'_vol :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderivμ'
  have hodeμ_vol := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hodeμ
  have hodeμ'_vol := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hodeμ'
  let y : ℝ → H := fun t => x μ t - x μ' t
  let z : ℝ → H := fun t => dx μ t - dx μ' t
  let w : ℝ → ℝ := fun t => ‖y t‖ ^ 2 + ‖z t‖ ^ 2
  have hyAC : AbsolutelyContinuousOnInterval y 0 T := by
    simpa [y] using hxACμ.fun_sub hxACμ'
  have hzAC : AbsolutelyContinuousOnInterval z 0 T := by
    simpa [z] using hdxACμ.fun_sub hdxACμ'
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := by
    simpa [w] using (ac_norm_sq hyAC).fun_add (ac_norm_sq hzAC)
  have hw_nonneg : ∀ t, 0 ≤ w t := by
    intro t
    dsimp [w]
    positivity
  have hw0 : w 0 =
      ‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2 := by
    simp only [w, y, z, hx0μ, hx0μ', hdx0μ, hdx0μ']
  have hwDeriv : ∀ᵐ t ∂MeasureTheory.volume, 0 ≤ t →
      HasDerivAt w
        (2 * inner ℝ (y t) (z t) +
          2 * inner ℝ (z t) (ddx μ t - ddx μ' t)) t := by
    filter_upwards [hxderivμ_vol, hxderivμ'_vol, hdxderivμ_vol,
      hdxderivμ'_vol] with
      t hxμ hxμ' hdxμ hdxμ'
    intro ht
    have hyD : HasDerivAt y (z t) t := by
      simpa [y, z] using (hxμ ht).sub (hxμ' ht)
    have hzD : HasDerivAt z (ddx μ t - ddx μ' t) t := by
      simpa [z] using (hdxμ ht).sub (hdxμ' ht)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  have hm_sq : m ^ 2 = 1 + 2 * γ ^ 2 + 2 * d ^ 2 := by
    apply Real.sq_sqrt
    positivity
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hm : 0 < m := by
    have hmone : 1 ≤ m := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg γ, sq_nonneg d]
    linarith
  have hfield_bound (t : ℝ)
      (hforce : ‖A μ (x μ t) - A μ' (x μ' t)‖ ≤ d * ‖y t‖) :
      ‖z t‖ ^ 2 +
          ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
        m ^ 2 * w t := by
    have hacc :
        ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ≤
          |γ| * ‖z t‖ + d * ‖y t‖ := by
      calc
        ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ≤
            ‖-γ • z t‖ + ‖A μ (x μ t) - A μ' (x μ' t)‖ := norm_sub_le _ _
        _ ≤ |γ| * ‖z t‖ + d * ‖y t‖ := by
          simpa [norm_smul] using add_le_add_left hforce ‖-γ • z t‖
    have hsq :
        ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
          (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hacc
    have hsumSq : (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤
        2 * γ ^ 2 * ‖z t‖ ^ 2 + 2 * d ^ 2 * ‖y t‖ ^ 2 := by
      calc
        (|γ| * ‖z t‖ + d * ‖y t‖) ^ 2 ≤
            2 * (|γ| * ‖z t‖) ^ 2 + 2 * (d * ‖y t‖) ^ 2 := by
          nlinarith [sq_nonneg (|γ| * ‖z t‖ - d * ‖y t‖)]
        _ = 2 * γ ^ 2 * ‖z t‖ ^ 2 + 2 * d ^ 2 * ‖y t‖ ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
          ring
    rw [hm_sq]
    dsimp [w]
    calc
      ‖z t‖ ^ 2 +
          ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
          ‖z t‖ ^ 2 +
            (2 * γ ^ 2 * ‖z t‖ ^ 2 + 2 * d ^ 2 * ‖y t‖ ^ 2) := by
        gcongr
        exact hsq.trans hsumSq
      _ ≤ (1 + 2 * γ ^ 2 + 2 * d ^ 2) *
          (‖y t‖ ^ 2 + ‖z t‖ ^ 2) := by
        have hγ : 0 ≤ γ ^ 2 := sq_nonneg _
        have hd : 0 ≤ d ^ 2 := sq_nonneg _
        have hy : 0 ≤ ‖y t‖ ^ 2 := sq_nonneg _
        have hz : 0 ≤ ‖z t‖ ^ 2 := sq_nonneg _
        ring_nf
        nlinarith [mul_nonneg hγ hy, mul_nonneg hγ hz,
          mul_nonneg hd hy, mul_nonneg hd hz]
  have hfield_pair (t : ℝ)
      (hforce : ‖A μ (x μ t) - A μ' (x μ' t)‖ ≤ d * ‖y t‖) :
      inner ℝ (y t) (z t) +
          inner ℝ (z t) (-γ • z t - (A μ (x μ t) - A μ' (x μ' t))) ≤
        m * w t := by
    have hbound := hfield_bound t hforce
    have hpair := two_pairing_le (y t) (z t) (z t)
      (-γ • z t - (A μ (x μ t) - A μ' (x μ' t)))
    have hsqrt := Real.sqrt_le_sqrt hbound
    rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hm0] at hsqrt
    have hwrt : Real.sqrt (w t) ^ 2 = w t := Real.sq_sqrt (hw_nonneg t)
    calc
      inner ℝ (y t) (z t) +
          inner ℝ (z t) (-γ • z t - (A μ (x μ t) - A μ' (x μ' t))) ≤
          Real.sqrt (‖y t‖ ^ 2 + ‖z t‖ ^ 2) *
            Real.sqrt (‖z t‖ ^ 2 +
              ‖-γ • z t - (A μ (x μ t) - A μ' (x μ' t))‖ ^ 2) := hpair
      _ ≤ Real.sqrt (w t) * (m * Real.sqrt (w t)) := by
        simpa [w] using mul_le_mul_of_nonneg_left hsqrt
          (Real.sqrt_nonneg (‖y t‖ ^ 2 + ‖z t‖ ^ 2))
      _ = m * w t := by nlinarith [hwrt]
  have hineq : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w t ≤
        (2 * m) * w t + 0 * w t ^ (1 / 2 : ℝ) := by
    filter_upwards [hodeμ_vol, hodeμ'_vol, hwDeriv, hball μ hμ,
      hball μ' hμ'] with t htodeμ htodeμ' htderiv htballμ htballμ'
    intro htIcc
    have hddxμ : ddx μ t = -γ • dx μ t - A μ (x μ t) := by
      calc
        ddx μ t = -(γ • dx μ t + A μ (x μ t)) :=
          eq_neg_of_add_eq_zero_left (by
            simpa [add_assoc] using htodeμ htIcc.1)
        _ = -γ • dx μ t - A μ (x μ t) := by module
    have hddxμ' : ddx μ' t = -γ • dx μ' t - A μ' (x μ' t) := by
      calc
        ddx μ' t = -(γ • dx μ' t + A μ' (x μ' t)) :=
          eq_neg_of_add_eq_zero_left (by
            simpa [add_assoc] using htodeμ' htIcc.1)
        _ = -γ • dx μ' t - A μ' (x μ' t) := by module
    have hddx : ddx μ t - ddx μ' t =
        -γ • z t - (A μ (x μ t) - A μ' (x μ' t)) := by
      rw [hddxμ, hddxμ']
      dsimp [z]
      module
    have hforce : ‖A μ (x μ t) - A μ' (x μ' t)‖ ≤ d * ‖y t‖ := by
      simpa [y] using hdist_bound (x μ t) (x μ' t)
        (htballμ htIcc) (htballμ' htIcc)
    have hderiv_eq : deriv w t =
        2 * (inner ℝ (y t) (z t) +
          inner ℝ (z t) (ddx μ t - ddx μ' t)) := by
      rw [(htderiv htIcc.1).deriv]
      ring
    calc
      (1 - (1 / 2 : ℝ)) * deriv w t =
          inner ℝ (y t) (z t) +
            inner ℝ (z t)
              (-γ • z t - (A μ (x μ t) - A μ' (x μ' t))) := by
        rw [hderiv_eq, hddx]
        ring
      _ ≤ m * w t := hfield_pair t hforce
      _ ≤ (2 * m) * w t + 0 * w t ^ (1 / 2 : ℝ) := by
        norm_num
        exact mul_le_mul_of_nonneg_right (by linarith) (hw_nonneg t)
  have hgronwall := ext_lem_1 (w := w) (a := fun _ : ℝ => 2 * m)
    (b := fun _ : ℝ => 0) (t₀ := 0) (T := T) (α := (1 / 2 : ℝ))
    hT (by norm_num) (by norm_num) (by simpa using hwAC)
    (by intro t ht; exact hw_nonneg t)
    (by exact MeasureTheory.integrableOn_const (by simp [Real.volume_Icc])) (by simp)
    (Filter.Eventually.of_forall (fun t _ => by norm_num)) (by simpa using hineq)
  apply Filter.Eventually.of_forall
  intro t htIcc
  have hgr := hgronwall t htIcc.1 (by simpa using htIcc.2)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hy_le : ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := by
    change ‖y t‖ ≤ Real.sqrt (w t)
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  have hexp : Real.exp ((2 * m) * t) ≤ Real.exp ((2 * m) * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htIcc.2 (by positivity)
  have hinit : 0 ≤
      Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) :=
    Real.sqrt_nonneg _
  calc
    ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := hy_le
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
        Real.exp ((2 * m) * t) := by
      convert hgr using 1
      all_goals ring
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) *
        Real.exp ((2 * m) * T) := mul_le_mul_of_nonneg_left hexp hinit
```

## Proof explanation
The proof begins by introducing arbitrary parameters $\mu,\mu'\in V$. The commands `intro μ hμ μ' hμ'` do exactly this. Then `dsimp only` unfolds the `let` in the goal. The proof defines

$$
d=\text{the value of \texttt{def\_8 r hr (A μ) (A μ')}}
$$

and

$$
m=\sqrt{1+2\gamma^2+2d^2}.
$$

Since the statement's constant is $c=2m$, the `change` command rewrites the target inequality with $e^{(2m)T}$ in place of $e^{cT}$.

Next, `obtain ⟨hd0, hdist_bound⟩ := hdist μ hμ μ' hμ'` extracts from `hdist` that $d\ge 0$ and that the local bound

$$
\|A_\mu u-A_{\mu'}v\|\le d\|u-v\|
$$

holds whenever $\|u\|\le r$ and $\|v\|\le r$. The subsequent `change` commands align the local definition of $d$ with the expression appearing in the goal.

The proof then uses `hsol` for $\mu$ and for $\mu'$. From `ext_def_2`, it discards the first component and unpacks six facts for each parameter: absolute continuity of $x_\mu$ and $v_\mu$, the initial conditions $x_\mu(0)=u_0(\mu)$ and $v_\mu(0)=v_0(\mu)$, the derivative relations almost everywhere, and the ODE almost everywhere. The lines using `MeasureTheory.ae_restrict_iff' measurableSet_Ici` convert the almost-everywhere statements on $[0,\infty)$ into global almost-everywhere statements with the condition $0\le t$. This is a measure-theoretic rewriting: a statement almost everywhere on $[0,\infty)$ becomes a statement almost everywhere on $\mathbb R$ that is only required to hold when $0\le t$.

The proof then defines the difference variables

$$
y(t)=x_\mu(t)-x_{\mu'}(t),\qquad
z(t)=v_\mu(t)-v_{\mu'}(t),
$$

and the energy

$$
w(t)=\|y(t)\|^2+\|z(t)\|^2.
$$

The absolute continuity of $y$ follows by subtracting the two absolutely continuous position curves. The absolute continuity of $z$ follows by subtracting the two absolutely continuous velocity curves. The cited lemma `ac_norm_sq` states that if a curve $f$ is absolutely continuous on an interval, then $t\mapsto \|f(t)\|^2$ is absolutely continuous on that interval. Applying it to $y$ and $z$, and then using closure of absolute continuity under addition, gives that $w$ is absolutely continuous on $[0,T]$. Also, $w(t)\ge 0$ for every $t$, and the initial conditions give

$$
w(0)=\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2.
$$

The next step computes the derivative of $w$. Using `filter_upwards`, the proof combines the almost-everywhere derivative relations for $x_\mu,x_{\mu'},v_\mu,v_{\mu'}$ into one almost-everywhere statement. For such $t$ with $0\le t$, subtracting derivatives gives

$$
y'(t)=z(t),\qquad z'(t)=a_\mu(t)-a_{\mu'}(t).
$$

The Lean lemma used here is the derivative of the squared norm: if $f'(t)=g(t)$, then

$$
\frac{d}{dt}\|f(t)\|^2=2\langle f(t),g(t)\rangle.
$$

Applying this to $y$ and to $z$, and adding, gives almost everywhere

$$
w'(t)=2\langle y(t),z(t)\rangle
+2\langle z(t),a_\mu(t)-a_{\mu'}(t)\rangle.
$$

The proof then proves a key local bound. Let

$$
\Delta A(t)=A_\mu(x_\mu(t))-A_{\mu'}(x_{\mu'}(t)).
$$

Assuming the force bound

$$
\|\Delta A(t)\|\le d\|y(t)\|,
$$

the proof estimates

$$
\|-\gamma z(t)-\Delta A(t)\|.
$$

By the triangle inequality and $\|-\gamma z(t)\|=|\gamma|\|z(t)\|$, one has

$$
\|-\gamma z(t)-\Delta A(t)\|
\le |\gamma|\|z(t)\|+d\|y(t)\|.
$$

Squaring and using $(X+Y)^2\le 2X^2+2Y^2$ gives

$$
\|-\gamma z(t)-\Delta A(t)\|^2
\le 2\gamma^2\|z(t)\|^2+2d^2\|y(t)\|^2.
$$

Therefore

$$
\|z(t)\|^2+\|-\gamma z(t)-\Delta A(t)\|^2
\le m^2 w(t),
$$

because $m^2=1+2\gamma^2+2d^2$. This is the bound `hfield_bound`.

Using the cited inequality `two_pairing_le`, which states that for all $a,b,c,d\in H$,

$$
\langle a,c\rangle+\langle b,d\rangle
\le
\sqrt{\|a\|^2+\|b\|^2}\,\sqrt{\|c\|^2+\|d\|^2},
$$

the proof specializes it to

$$
a=y(t),\quad b=z(t),\quad c=z(t),\quad d=-\gamma z(t)-\Delta A(t).
$$

This yields

$$
\langle y(t),z(t)\rangle+\langle z(t),-\gamma z(t)-\Delta A(t)\rangle
\le
\sqrt{w(t)}\,
\sqrt{\|z(t)\|^2+\|-\gamma z(t)-\Delta A(t)\|^2}.
$$

The field bound above gives that the second square root is at most $m\sqrt{w(t)}$. Since $m\ge 0$, the product is at most $m w(t)$. This is the bound `hfield_pair`.

Now the proof derives the Gronwall differential inequality. Using `filter_upwards` again, it combines the ODEs for $\mu$ and $\mu'$ with the ball estimates from `hball`. For $t\in[0,T]$, the ODE gives

$$
a_\mu(t)=-\gamma v_\mu(t)-A_\mu(x_\mu(t)),\qquad
a_{\mu'}(t)=-\gamma v_{\mu'}(t)-A_{\mu'}(x_{\mu'}(t)).
$$

Subtracting gives

$$
a_\mu(t)-a_{\mu'}(t)
=
-\gamma z(t)-\Delta A(t).
$$

The ball estimates give $\|x_\mu(t)\|\le r$ and $\|x_{\mu'}(t)\|\le r$, so `hdist` applies and yields

$$
\|\Delta A(t)\|\le d\|y(t)\|.
$$

Combining the derivative formula for $w$ with `hfield_pair` gives almost everywhere on $[0,T]$

$$
\frac12 w'(t)
\le m w(t)
\le (2m)w(t)+0\cdot w(t)^{1/2}.
$$

The arithmetic simplifications here use `ring`, `linarith`, `norm_num`, and the nonnegativity of $w$. This is the hypothesis `hineq` needed for the nonlinear Gronwall inequality.

The proof then applies the cited result `ext_lem_1`, which is the nonlinear Gronwall inequality. In general, it says: if $T>0$, $0\le \alpha<1$, $w$ is absolutely continuous on $[t_0,t_0+T]$, $w\ge 0$, $a,b$ are integrable on that interval, $b\ge 0$ almost everywhere, and almost everywhere

$$
(1-\alpha)w'(t)\le a(t)w(t)+b(t)w(t)^\alpha,
$$

then for all $t\in[t_0,t_0+T]$,

$$
w(t)^{1-\alpha}
\le
w(t_0)^{1-\alpha}e^{\int_{t_0}^t a}
+
\int_{t_0}^t e^{\int_s^t a} b(s)\,ds.
$$

The proof specializes this with $t_0=0$, $\alpha=1/2$, $a(t)=2m$, and $b(t)=0$. The hypotheses are verified using the absolute continuity and nonnegativity of $w$, the integrability of the constant function $2m$ on $[0,T]$, and the fact that the zero function is nonnegative. The resulting bound is

$$
w(t)^{1/2}
\le
w(0)^{1/2}\exp\!\left(\int_0^t 2m\,d\tau\right)
+
\int_0^t \exp\!\left(\int_s^t 2m\,d\tau\right)\cdot 0\,ds.
$$

The second term vanishes, and $\int_0^t 2m\,d\tau=2mt$. Hence

$$
w(t)^{1/2}\le w(0)^{1/2}e^{2mt}.
$$

Rewriting $w(t)^{1/2}$ as $\sqrt{w(t)}$, rewriting $w(0)^{1/2}$, and replacing $w(0)$ by the initial-difference expression gives

$$
\sqrt{w(t)}
\le
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}\,
e^{2mt}.
$$

Finally, the proof converts this into the desired estimate. Since

$$
w(t)=\|y(t)\|^2+\|z(t)\|^2
$$

and $\|z(t)\|^2\ge 0$, one has

$$
\|x_\mu(t)-x_{\mu'}(t)\|=\|y(t)\|\le \sqrt{w(t)}.
$$

Also, for $t\in[0,T]$, since $2m\ge 0$,

$$
e^{2mt}\le e^{2mT}.
$$

Multiplying the Gronwall estimate by the nonnegative factor

$$
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
$$

therefore gives

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}\,
e^{2mT}.
$$

Since $2m=c$, this is exactly the stated bound. The final `apply Filter.Eventually.of_forall` turns the pointwise argument for arbitrary $t\in[0,T]$ into the almost-everywhere statement required by the theorem.

