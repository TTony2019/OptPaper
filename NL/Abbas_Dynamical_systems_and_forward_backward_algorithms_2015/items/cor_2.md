## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/cor_2.lean`

## Lean statement
```lean
theorem bounded_inf_compact_strong_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (x v : ℝ → H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hlam : 0 < lam) (hmu : 0 < mu)
    (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)))
    (hinfcompact : ∀ r a : ℝ,
      IsCompact (Metric.closedBall (Classical.choose hS) r ∩
        {y | (Phi y : EReal) ≤ (a : EReal)})) :
    ∃ z ∈ S, Tendsto x atTop (nhds z)
```

## Statement explanation
The theorem assumes a real Hilbert space \(H\), an extended-real-valued function \(\Phi:H\to \mathrm{Set.Ioi}(\bot:\mathrm{EReal})\), and an operator \(B:H\to H\). It also assumes a set \(S\subseteq H\), trajectories \(x,v:\mathbb R\to H\), and real parameters \(\lambda,\mu,\beta\). The hypotheses are:

- \(S\) is nonempty.
- \(0<\lambda\), \(0<\mu\), and \(\mu\lambda=1\), and \(0<\beta\).
- \(B\) is \(\beta\)-cocoercive on the whole space.
- \(x\) and \(v\) are absolutely continuous on every interval \([0,b]\) for \(b>0\).
- For every \(T>0\), \(x\) and \(v\) have derivatives \(x'(t)\) and \(v'(t)\) almost everywhere on \([0,T]\).
- For every \(t\ge 0\), \(v(t)\) belongs to the subdifferential of \(\Phi\) at \(x(t)\).
- \(v\) and \(x'\) are \(L^2\) on every bounded interval \([0,b]\).
- Almost everywhere on \([0,\infty)\), one has \(v(t)\in \partial\Phi(x(t))\) and the differential equation
  \[
  \lambda x'(t)+v'(t)+v(t)+B(x(t))=0.
  \]
- Every point \(w\in S\) is an equilibrium/stationary point in the sense that \(-B(w)\in \partial\Phi(w)\).
- The effective domain condition holds along the trajectory \(x(t)\) for \(t\ge 0\), and every point of \(S\) is in the effective domain of \(\Phi\).
- The trajectory \(x(t)\) has a weak limit point in \(S\): there exists \(x_{\inf}\in S\) such that \(x(t)\to x_{\inf}\) weakly in \(H\) as \(t\to\infty\).
- For every real \(r\) and \(a\), the intersection of the closed ball around some chosen point of \(S\) with the sublevel set \(\{y\mid \Phi(y)\le a\}\) is compact.

The conclusion is that there exists \(z\in S\) such that \(x(t)\) converges to \(z\) in the norm topology of \(H\).

## Lean proof
```lean
by
  let z0 : H := Classical.choose hS
  have hz0 : z0 ∈ S := Classical.choose_spec hS
  obtain ⟨_, _, xinf, hxinfS, hxweak, hvalue⟩ :=
    proposition_2_16 S Phi hPhi B x v z0 lam mu beta hS hz0 hlam hmu hmu_lam hbeta
      hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2 horbit hsolution hdom hweak
  obtain ⟨C, hC⟩ := cor218_eventually_norm_le_of_tendsto_weakly hxweak
  let a : ℝ := (Phi xinf : EReal).toReal + 1
  let R : ℝ := C + ‖z0‖
  let K : Set H := Metric.closedBall z0 R ∩ {y | (Phi y : EReal) ≤ (a : EReal)}
  have hK : IsCompact K := by
    dsimp [K, R, a, z0]
    exact hinfcompact (C + ‖Classical.choose hS‖) ((Phi xinf : EReal).toReal + 1)
  have hEventuallyK : ∀ᶠ t in atTop, x t ∈ K := by
    have hlt : ∀ᶠ t in atTop, (Phi (x t) : EReal).toReal < a := by
      dsimp [a]
      exact hvalue.eventually_lt_const (lt_add_one _)
    filter_upwards [hC, hlt, eventually_ge_atTop (0 : ℝ)] with t ht htv ht0
    constructor
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hsum : ‖x t‖ + ‖z0‖ ≤ C + ‖z0‖ := by linarith
      exact le_trans (norm_sub_le _ _) (by simpa [R] using hsum)
    · have hcoer : ((Phi (x t) : EReal).toReal : EReal) ≤ (a : EReal) := by
        exact_mod_cast le_of_lt htv
      exact (EReal.le_coe_toReal (ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp
        (hdom.1 t ht0)))).trans hcoer
  have hscalar : ∀ ell : H →L[ℝ] ℝ,
      Tendsto (fun t ↦ ell (x t)) atTop (nhds (ell xinf)) := by
    intro ell
    let u : H := (InnerProductSpace.toDual ℝ H).symm ell
    have hu := (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H xinf) |>.comp hxweak
    have hrepr (y : H) : ell y = inner ℝ y u := by
      calc
        ell y = inner ℝ u y := (InnerProductSpace.toDual_symm_apply).symm
        _ = inner ℝ y u := real_inner_comm _ _
    simpa only [hrepr] using hu
  exact ⟨xinf, hxinfS,
    cor218_strong_tendsto_of_eventually_compact_and_weak_scalar_convergence x xinf K hK
      hEventuallyK hscalar⟩
```

## Proof explanation
The proof begins by choosing a point \(z_0\in S\) using the nonemptiness assumption \(hS\); the choice is made with `Classical.choose`, and `Classical.choose_spec` proves \(z_0\in S\).

Next, the proof invokes the earlier result `proposition_2_16` with all the dynamical assumptions. From this it extracts a point \(x_{\inf}\in S\), a weak convergence fact \(hxweak\) for \(x(t)\to x_{\inf}\), and a value convergence fact \(hvalue\) for \(\Phi(x(t))\). The first two components of the returned proof are ignored with `_`. The fact \(hvalue\) is later used as a limit statement for the real number \((\Phi(x(t)))_{\mathrm{toReal}}\).

Then the proof obtains an eventual norm bound. Since \(x(t)\) converges weakly to \(x_{\inf}\), the lemma `cor218_eventually_norm_le_of_tendsto_weakly` gives a constant \(C\) such that eventually \(\|x(t)\|\le C\).

The proof defines a real number
\[
a=(\Phi(x_{\inf}))_{\mathrm{toReal}}+1
\]
and a radius
\[
R=C+\|z_0\|.
\]
It then defines a compact set
\[
K=\operatorname{closedBall}(z_0,R)\cap\{y\mid \Phi(y)\le a\}.
\]
The compactness of \(K\) is immediate from the hypothesis `hinfcompact` applied to \(R\) and \(a\), after unfolding the definitions of \(K,R,a,z_0\) with `dsimp`.

The proof then shows that \(x(t)\) is eventually in \(K\). First, from the value convergence \(hvalue\) and the real inequality
\[
(\Phi(x_{\inf}))_{\mathrm{toReal}}<a,
\]
it obtains that eventually
\[
(\Phi(x(t)))_{\mathrm{toReal}}<a.
\]
This is done with `hvalue.eventually_lt_const`. The proof uses `filter_upwards` to combine this with the eventual norm bound and the fact that eventually \(t\ge 0\).

For a fixed sufficiently large \(t\), membership in \(K\) is split into two parts with `constructor`. For the closed ball part, rewriting with `Metric.mem_closedBall` and `dist_eq_norm` changes the goal to a norm inequality
\[
\|x(t)-z_0\|\le R.
\]
The triangle inequality gives
\[
\|x(t)-z_0\|\le \|x(t)\|+\|z_0\|,
\]
and `linarith` combined with the eventual bound \(\|x(t)\|\le C\) gives
\[
\|x(t)\|+\|z_0\|\le C+\|z_0\|=R.
\]
Thus \(x(t)\) lies in the closed ball.

For the sublevel set part, the real inequality \((\Phi(x(t)))_{\mathrm{toReal}}<a\) is cast to the extended-real inequality
\[
((\Phi(x(t)))_{\mathrm{toReal}}:\mathrm{EReal})\le (a:\mathrm{EReal}).
\]
Since \(x(t)\) is in the effective domain of \(\Phi\), the extended-real value \(\Phi(x(t))\) is not the top element, so one may use `EReal.le_coe_toReal` to obtain
\[
\Phi(x(t))\le ((\Phi(x(t)))_{\mathrm{toReal}}:\mathrm{EReal}).
\]
Transitivity then gives \(\Phi(x(t))\le a\), so \(x(t)\) is in the sublevel set. Hence \(x(t)\in K\) eventually.

The proof next proves that every continuous real-valued linear functional on \(H\) converges along \(x\). Given a continuous linear functional \(\ell:H\to_{\mathbb R}\mathbb R\), the Riesz representation theorem identifies \(\ell\) with a vector \(u\in H\). The proof defines \(u=(\mathrm{InnerProductSpace.toDual}\,\mathbb R\,H)^{-1}(\ell)\). The map \(y\mapsto \langle y,u\rangle\) is continuous for the weak topology, so composing it with the weak convergence \(hxweak\) gives
\[
\langle x(t),u\rangle\to \langle x_{\inf},u\rangle .
\]
A local calculation `hrepr` shows that \(\ell(y)=\langle y,u\rangle\) for all \(y\), using `InnerProductSpace.toDual_symm_apply` and commutativity of the real inner product. Therefore `simpa only [hrepr]` rewrites the goal and proves
\[
\ell(x(t))\to \ell(x_{\inf}).
\]
Thus all scalar functionals of \(x(t)\) converge to their values at \(x_{\inf}\).

Finally, the proof uses the lemma
`cor218_strong_tendsto_of_eventually_compact_and_weak_scalar_convergence`
with the compact set \(K\), the eventual membership \(x(t)\in K\), and the scalar convergence just proved. This yields that \(x(t)\) converges to \(x_{\inf}\) in the strong topology of \(H\). Since \(x_{\inf}\in S\), the conclusion follows with \(z=x_{\inf}\).

