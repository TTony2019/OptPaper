## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_lem_1.lean`

## Lean statement
```lean
theorem lemma_2_1_uniformized_KL {m : Nat} (Omega : Set (EuclideanSpace m))
    (f : EuclideanSpace m -> EReal)
    (hcompact : IsCompact Omega)
    (hproper : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f)
    (hconstant : ∀ x ∈ Omega, ∀ y ∈ Omega, f x = f y)
    (hKL : ∀ x ∈ Omega, KLPropertyAt f x) :
    ∃ epsilon eta : Real, ∃ phi : Real -> Real,
      0 < epsilon ∧ 0 < eta ∧ DesingularizingFunction eta phi ∧
        ∀ xbar ∈ Omega, ∀ x : EuclideanSpace m,
          distToSet x Omega < epsilon ->
          f xbar < f x ->
          f x < erealAddReal (f xbar) eta ->
          1 <= deriv phi ((f x).toReal - (f xbar).toReal) *
            distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x)
```

## Statement explanation
The declaration `lemma_2_1_uniformized_KL` states the following. Let $m\in\mathbb N$, let $E=\mathrm{EuclideanSpace}(m)=\mathbb R^m$ with its Euclidean norm, let $\Omega\subseteq E$, and let $f:E\to\overline{\mathbb R}$ be an extended-real-valued function. The hypotheses are:

- $\Omega$ is compact.
- $f$ is proper, in the sense of `ERealFunction.IsProper`.
- $f$ is lower semicontinuous.
- $f$ is constant on $\Omega$: for all $x,y\in\Omega$, $f(x)=f(y)$.
- $f$ has the Kurdyka–Łojasiewicz property at every point of $\Omega$.

The conclusion is that there exist real numbers $\varepsilon\gt 0$, $\eta\gt 0$, and a function $\phi:\mathbb R\to\mathbb R$ such that $\phi$ is a desingularizing function for $\eta$, and such that for every $\bar x\in\Omega$ and every $x\in E$, if

$$
d(x,\Omega)<\varepsilon,\qquad f(\bar x)<f(x),\qquad f(x)<f(\bar x)+\eta,
$$

then

```math
1\le \phi'\!\left((f(x))_{\mathbb R}-(f(\bar x))_{\mathbb R}\right)\, d\!\left(0,\partial f(x)\right).
```

Here $d(x,\Omega)$ is the distance from $x$ to $\Omega$, $(f(x))_{\mathbb R}$ denotes the real value of $f(x)$ when it is finite, and $\partial f(x)$ is the limiting subdifferential of $f$ at $x$. The expression $f(\bar x)+\eta$ is extended-real addition of the real number $\eta$ to $f(\bar x)$.

A desingularizing function for $\eta$ is a function $\phi$ satisfying

$$
0<\eta,\qquad
\phi\text{ is concave on }[0,\eta],\qquad
\phi\text{ is continuous on }[0,\eta],
$$

$$
\phi\text{ is differentiable on }(0,\eta),\qquad
\phi(0)=0,\qquad
\phi'(s)>0\text{ for all }s\in(0,\eta).
$$

Thus the theorem says that, under compactness, constancy of $f$ on $\Omega$, and the local KL property at every point of $\Omega$, the KL inequality can be made uniform on a tube around $\Omega$: one positive radius $\varepsilon$, one positive height $\eta$, and one desingularizing function $\phi$ work simultaneously for all reference points $\bar x\in\Omega$ and all nearby points $x$ whose value lies strictly above and within $\eta$ above the common value on $\Omega$.

The distance $d(x,\Omega)$ is `distToSet x Omega`, defined as the metric infimum distance from $x$ to $\Omega$, namely

```math
d(x,\Omega)=\inf_{y\in\Omega}\|x-y\|.
```

The set $\partial f(x)$ is the limiting subdifferential: morally, it consists of limits of Fréchet subgradients along sequences $x_k\to x$ for which $f(x_k)\to f(x)$. The term $d(0,\partial f(x))$ is therefore the distance from the origin to that limiting subdifferential set.

The hypotheses of properness and lower semicontinuity are part of the statement, but the proof below does not explicitly invoke them; the argument uses compactness, constancy of $f$ on $\Omega$, and the local KL property.

## Lean proof
```lean
by
  classical
  by_cases hOmega_nonempty : Omega.Nonempty
  · choose etaLoc ULoc phiLoc hLoc using fun z hz => (hKL z hz).2
    have hetaLoc : ∀ z, ∀ hz : z ∈ Omega, 0 < etaLoc z hz := by
      intro z hz
      exact (hLoc z hz).1
    have hULoc : ∀ z, ∀ hz : z ∈ Omega, ULoc z hz ∈ nhds z := by
      intro z hz
      exact (hLoc z hz).2.1
    have hphiLoc :
        ∀ z, ∀ hz : z ∈ Omega,
          DesingularizingFunction (etaLoc z hz) (phiLoc z hz) := by
      intro z hz
      exact (hLoc z hz).2.2.1
    have hineqLoc :
        ∀ z, ∀ hz : z ∈ Omega, ∀ x ∈ ULoc z hz,
          f z < f x ->
          f x < erealAddReal (f z) (etaLoc z hz) ->
          1 <= deriv (phiLoc z hz) ((f x).toReal - (f z).toReal) *
            distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x) := by
      intro z hz
      exact (hLoc z hz).2.2.2
    have hball_exists :
        ∀ z, ∀ hz : z ∈ Omega,
          ∃ rho : Real, 0 < rho ∧ Metric.ball z rho ⊆ ULoc z hz := by
      intro z hz
      exact Metric.mem_nhds_iff.mp (hULoc z hz)
    choose rhoLoc hrhoLoc hballLoc using hball_exists
    let cover : EuclideanSpace m -> Set (EuclideanSpace m) :=
      fun z => if hz : z ∈ Omega then Metric.ball z (rhoLoc z hz / 2) else Set.univ
    have hcover_nhds : ∀ z ∈ Omega, cover z ∈ nhds z := by
      intro z hz
      have hpos : 0 < rhoLoc z hz / 2 := by linarith [hrhoLoc z hz]
      have hball : Metric.ball z (rhoLoc z hz / 2) ∈ nhds z :=
        Metric.ball_mem_nhds z hpos
      simpa [cover, hz] using hball
    rcases hcompact.elim_nhds_subcover cover hcover_nhds with ⟨t, htOmega, hcover⟩
    have hcover_ball :
        ∀ y ∈ Omega, ∃ i, ∃ hi : i ∈ t,
          dist y i < rhoLoc i (htOmega i hi) / 2 := by
      intro y hy
      rcases Set.mem_iUnion.mp (hcover hy) with ⟨i, hiUnion⟩
      rcases Set.mem_iUnion.mp hiUnion with ⟨hi, hycover⟩
      refine ⟨i, hi, ?_⟩
      have hiOmega : i ∈ Omega := htOmega i hi
      simpa [cover, hiOmega, Metric.mem_ball] using hycover
    have htNonempty : t.Nonempty := by
      rcases hOmega_nonempty with ⟨y0, hy0⟩
      rcases hcover_ball y0 hy0 with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    let etaI : EuclideanSpace m -> Real :=
      fun i => if hi : i ∈ t then etaLoc i (htOmega i hi) else 1
    let phiI : EuclideanSpace m -> Real -> Real :=
      fun i => if hi : i ∈ t then phiLoc i (htOmega i hi) else fun s : Real => s
    let rhoI : EuclideanSpace m -> Real :=
      fun i => if hi : i ∈ t then rhoLoc i (htOmega i hi) / 2 else 1
    have hetaI_pos : ∀ i ∈ t, 0 < etaI i := by
      intro i hi
      simp [etaI, hi, hetaLoc i (htOmega i hi)]
    have hrhoI_pos : ∀ i ∈ t, 0 < rhoI i := by
      intro i hi
      have hpos : 0 < rhoLoc i (htOmega i hi) / 2 := by
        linarith [hrhoLoc i (htOmega i hi)]
      simpa [rhoI, hi] using hpos
    have hphiI : ∀ i ∈ t, DesingularizingFunction (etaI i) (phiI i) := by
      intro i hi
      simpa [etaI, phiI, hi] using hphiLoc i (htOmega i hi)
    let epsilon : Real := t.inf' htNonempty rhoI
    let eta : Real := t.inf' htNonempty etaI
    let Phi : Real -> Real := fun s : Real => ∑ i ∈ t, phiI i s
    have hepsilon_pos : 0 < epsilon := by
      exact finset_inf'_pos htNonempty rhoI hrhoI_pos
    have heta_pos : 0 < eta := by
      exact finset_inf'_pos htNonempty etaI hetaI_pos
    have hepsilon_le : ∀ i ∈ t, epsilon <= rhoI i := by
      intro i hi
      exact Finset.inf'_le rhoI hi
    have heta_le : ∀ i ∈ t, eta <= etaI i := by
      intro i hi
      exact Finset.inf'_le etaI hi
    have hPhi_desing : DesingularizingFunction eta Phi := by
      simpa [Phi] using
        desingularizingFunction_finset_sum_restrict htNonempty eta etaI phiI
          heta_pos heta_le hphiI
    refine ⟨epsilon, eta, Phi, hepsilon_pos, heta_pos, hPhi_desing, ?_⟩
    intro xbar hxbar x hdist hlo hhi
    have hcover_rhoI : ∀ y ∈ Omega, ∃ i ∈ t, dist y i < rhoI i := by
      intro y hy
      rcases hcover_ball y hy with ⟨i, hi, hdistyi⟩
      refine ⟨i, hi, ?_⟩
      simpa [rhoI, hi] using hdistyi
    rcases tube_cover_of_infDist_lt_finset_inf htNonempty (fun i : EuclideanSpace m => i)
        rhoI hrhoI_pos hcover_rhoI epsilon hepsilon_le hOmega_nonempty x hdist with
      ⟨i, hi, hxi_two⟩
    have hiOmega : i ∈ Omega := htOmega i hi
    have hxi_rho : dist x i < rhoLoc i hiOmega := by
      have hxi' : dist x i < 2 * (rhoLoc i hiOmega / 2) := by
        simpa [rhoI, hi] using hxi_two
      nlinarith [hxi', hrhoLoc i hiOmega]
    have hxU : x ∈ ULoc i hiOmega := by
      exact hballLoc i hiOmega (by simpa [Metric.mem_ball] using hxi_rho)
    have hfxbar_i : f xbar = f i := hconstant xbar hxbar i hiOmega
    have hlo_i : f i < f x := by
      simpa [hfxbar_i] using hlo
    have hhi_eta : f x < erealAddReal (f i) eta := by
      simpa [hfxbar_i] using hhi
    have hhi_i : f x < erealAddReal (f i) (etaI i) := by
      exact lt_of_lt_of_le hhi_eta (erealAddReal_le_of_le (heta_le i hi))
    have hhi_loc : f x < erealAddReal (f i) (etaLoc i hiOmega) := by
      simpa [etaI, hi] using hhi_i
    have hlocal_loc :
        1 <= deriv (phiLoc i hiOmega) ((f x).toReal - (f i).toReal) *
          distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x) :=
      hineqLoc i hiOmega x hxU hlo_i hhi_loc
    let s : Real := (f x).toReal - (f i).toReal
    let D : Real := distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x)
    have hlocal :
        1 <= deriv (phiI i) s * D := by
      simpa [s, D, phiI, hi] using hlocal_loc
    have hfinite_i := effective_finite_of_subdifferentialDomain (hKL i hiOmega).1
    have hs_eta : s ∈ Set.Ioo 0 eta := by
      exact toReal_sub_mem_Ioo_of_ereal_window heta_pos hfinite_i.1 hfinite_i.2
        hlo_i hhi_eta
    have hs_j : ∀ j ∈ t, s ∈ Set.Ioo 0 (etaI j) := by
      intro j hj
      exact ⟨hs_eta.1, lt_of_lt_of_le hs_eta.2 (heta_le j hj)⟩
    have hdiffAt : ∀ j ∈ t, DifferentiableAt Real (phiI j) s := by
      intro j hj
      exact ((hphiI j hj).2.2.2.1).differentiableAt
        (isOpen_Ioo.mem_nhds (hs_j j hj))
    have hderiv_sum :
        deriv Phi s = ∑ j ∈ t, deriv (phiI j) s := by
      have hPhi_eq : Phi = (∑ j ∈ t, phiI j) := by
        funext r
        simp [Phi]
      rw [hPhi_eq]
      exact deriv_sum hdiffAt
    have hderiv_nonneg : ∀ j ∈ t, 0 <= deriv (phiI j) s := by
      intro j hj
      exact le_of_lt ((hphiI j hj).2.2.2.2.2 s (hs_j j hj))
    have hderiv_le : deriv (phiI i) s <= deriv Phi s := by
      rw [hderiv_sum]
      exact Finset.single_le_sum hderiv_nonneg hi
    have hD_nonneg : 0 <= D := by
      unfold D distToSet
      exact Metric.infDist_nonneg
    have hmul : deriv (phiI i) s * D <= deriv Phi s * D :=
      mul_le_mul_of_nonneg_right hderiv_le hD_nonneg
    have hchain : 1 <= deriv Phi s * D := le_trans hlocal hmul
    simpa [s, D, hfxbar_i] using hchain
  · refine ⟨1, 1, fun s : Real => s, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · exact desingularizingFunction_id
    · intro xbar hxbar
      exact False.elim (hOmega_nonempty ⟨xbar, hxbar⟩)
```

## Proof explanation
The proof begins with `classical`, putting the argument in classical logic, and then splits into two cases: $\Omega$ nonempty and $\Omega$ empty.

In the nonempty case, for each $z\in\Omega$, the local KL hypothesis $`hKL\,z\,hz`$is destructured. Its first component is later used to know that$z$belongs to the subdifferential domain of$f$. Its second component provides local data: a positive number$\eta_{\mathrm{loc}}(z)$, a neighborhood$U_{\mathrm{loc}}(z)$of$z$, and a function$\phi_{\mathrm{loc}}(z)$such that$\phi_{\mathrm{loc}}(z)$is desingularizing for$\eta_{\mathrm{loc}}(z)$, and such that for all$x\in U_{\mathrm{loc}}(z)$,

$$
f(z)<f(x),\qquad f(x)<f(z)+\eta_{\mathrm{loc}}(z)
$$

imply

```math
1\le \phi_{\mathrm{loc}}(z)'\!\left((f(x))_{\mathbb R}-(f(z))_{\mathbb R}\right)\,
   d\!\left(0,\partial f(x)\right).
```

The tactic `choose` turns these pointwise existential statements into choice functions, and the subsequent `intro` steps unpack the components: positivity of $\eta_{\mathrm{loc}}$, membership of $U_{\mathrm{loc}}$ in the neighborhood filter of $z$, the desingularizing property of $\phi_{\mathrm{loc}}$, and the local KL inequality.

Next, for each $z\in\Omega$, since $U_{\mathrm{loc}}(z)$ is a neighborhood of $z$, the metric neighborhood characterization `Metric.mem_nhds_iff` gives a radius $\rho_{\mathrm{loc}}(z)\gt 0$ such that

$$
B(z,\rho_{\mathrm{loc}}(z))\subseteq U_{\mathrm{loc}}(z).
$$

The proof then defines a cover indexed by points of $E$: for $z\in\Omega$, the covering set is the smaller ball

```math
B\!\left(z,\frac{\rho_{\mathrm{loc}}(z)}2\right),
```

and for $z\notin\Omega$ it is the whole space. For $z\in\Omega$, this smaller ball is a neighborhood of $z$ because its radius is positive. Compactness is then used through `hcompact.elim_nhds_subcover`, which extracts a finite subset $t\subseteq\Omega$ such that the sets indexed by $t$ cover $\Omega$. This is the standard finite subcover step.

From this finite cover one obtains, for every $y\in\Omega$, some $i\in t$ with

$$
d(y,i)<\frac{\rho_{\mathrm{loc}}(i)}2.
$$

Since $\Omega$ is assumed nonempty, the finite set $t$ is nonempty: choosing $y_0\in\Omega$ and an index $i\in t$ covering it gives $i\in t$.

The proof then defines, for $i\in t$, the local quantities

$$
\eta_i=\eta_{\mathrm{loc}}(i),\qquad
\phi_i=\phi_{\mathrm{loc}}(i),\qquad
\rho_i=\frac{\rho_{\mathrm{loc}}(i)}2,
$$

with irrelevant dummy values for $i\notin t$. It records that each $\eta_i$ and $\rho_i$ is positive for $i\in t$, and that each $\phi_i$ is desingularizing for $\eta_i$. It then defines

$$
\varepsilon=\min_{i\in t}\rho_i,\qquad
\eta=\min_{i\in t}\eta_i,\qquad
\Phi(s)=\sum_{i\in t}\phi_i(s).
$$

The finite infimum positivity lemma `finset_inf'_pos` shows that $\varepsilon\gt 0$ and $\eta\gt 0$, because $t$ is nonempty and all $\rho_i,\eta_i$ are positive. The standard finite infimum property `Finset.inf'_le` gives

$$
\varepsilon\le \rho_i,\qquad \eta\le \eta_i
$$

for every $i\in t$.

The finite-sum desingularizing lemma `desingularizingFunction_finset_sum_restrict` is then applied. Its mathematical content is: if $t$ is nonempty, $\eta\gt 0$, $\eta\le \eta_i$ for every $i\in t$, and each $\phi_i$ is desingularizing for $\eta_i$, then the sum

$$
\Phi(s)=\sum_{i\in t}\phi_i(s)
$$

is desingularizing for $\eta$. Indeed, on the smaller interval $[0,\eta]$, each $\phi_i$ retains concavity, continuity, differentiability on $(0,\eta)$, value zero at zero, and positive derivative; sums preserve these properties, and the derivative of the sum is the sum of the positive derivatives. Thus $\Phi$ is the desired uniform desingularizing function.

It remains to prove the uniform KL inequality. Fix $\bar x\in\Omega$ and $x\in E$ satisfying

$$
d(x,\Omega)<\varepsilon,\qquad f(\bar x)<f(x),\qquad f(x)<f(\bar x)+\eta.
$$

First, the proof shows that $\Omega$ is covered by the balls $B(i,\rho_i)$. This was already obtained from the finite subcover: for every $y\in\Omega$, there is $i\in t$ with $d(y,i)\lt \rho_i$. Then it applies `tube_cover_of_infDist_lt_finset_inf`. That lemma says: if $\Omega$ is covered by balls $B(c_i,r_i)$, all radii $r_i$ are positive, $\varepsilon\le r_i$ for all $i$, and $d(x,\Omega)\lt \varepsilon$, then $x$ lies in some doubled ball $B(c_i,2r_i)$. Here the centers are $c_i=i$, the radii are $r_i=\rho_i$, and the conclusion gives some $i\in t$ with

$$
d(x,i)<2\rho_i=\rho_{\mathrm{loc}}(i).
$$

Thus $x\in B(i,\rho_{\mathrm{loc}}(i))$. Since $B(i,\rho_{\mathrm{loc}}(i))\subseteq U_{\mathrm{loc}}(i)$, we get

$$
x\in U_{\mathrm{loc}}(i).
$$

The arithmetic step $d(x,i)\lt \rho_{\mathrm{loc}}(i)$ from $d(x,i)\lt 2(\rho_{\mathrm{loc}}(i)/2)$ is discharged by `nlinarith`.

Now use the constancy of $f$ on $\Omega$. Since $\bar x\in\Omega$ and $i\in t\subseteq\Omega$, we have

$$
f(\bar x)=f(i).
$$

Therefore the hypotheses $f(\bar x)\lt f(x)$ and $f(x)\lt f(\bar x)+\eta$ become

$$
f(i)<f(x),\qquad f(x)<f(i)+\eta.
$$

Because $\eta\le \eta_i$, the lemma `erealAddReal_le_of_le` gives

$$
f(i)+\eta\le f(i)+\eta_i
$$

in the extended-real sense. Hence

$$
f(x)<f(i)+\eta_i.
$$

Thus the local KL inequality at $i$ applies to $x$, yielding

```math
1\le \phi_i'\!\left((f(x))_{\mathbb R}-(f(i))_{\mathbb R}\right)\,
   d\!\left(0,\partial f(x)\right).
```

The proof sets

```math
s=(f(x))_{\mathbb R}-(f(i))_{\mathbb R},\qquad
D=d\!\left(0,\partial f(x)\right),
```

so the local inequality reads

$$
1\le \phi_i'(s)D.
$$

Next, the proof needs finiteness of $f(i)$. It uses `(hKL i hi).1` to know that $i$ lies in the subdifferential domain of $f$, and then applies `effective_finite_of_subdifferentialDomain`. That lemma says that if $z$ belongs to the subdifferential domain of $f$, then $f(z)\neq +\infty$ and $f(z)\neq -\infty$, i.e. $f(z)$ is finite. Specialized here, it gives that $f(i)$ is neither $+\infty$ nor $-\infty$.

With that finiteness, the theorem `toReal_sub_mem_Ioo_of_ereal_window` applies. Its content is: if $0\lt \eta$, $a$ is finite, $a\lt b$, and $b\lt a+\eta$ in extended reals, then

$$
b_{\mathbb R}-a_{\mathbb R}\in(0,\eta).
$$

Taking $a=f(i)$ and $b=f(x)$, the hypotheses $f(i)\lt f(x)$ and $f(x)\lt f(i)+\eta$ give

$$
s=(f(x))_{\mathbb R}-(f(i))_{\mathbb R}\in(0,\eta).
$$

Since $\eta\le \eta_j$ for every $j\in t$, it follows that

$$
s\in(0,\eta_j)
$$

for every $j\in t$.

Now each $\phi_j$ is differentiable on $(0,\eta_j)$. Since $s\in(0,\eta_j)$, and $(0,\eta_j)$ is open, `DifferentiableOn.differentiableAt` gives that $\phi_j$ is differentiable at $s$. Therefore the derivative of the finite sum $\Phi$ can be computed by `deriv_sum`:

$$
\Phi'(s)=\sum_{j\in t}\phi_j'(s).
$$

Moreover, each derivative $\phi_j'(s)$ is positive, because $\phi_j$ is desingularizing and $s\in(0,\eta_j)$. Hence each $\phi_j'(s)\ge 0$. The finite-sum lemma `Finset.single_le_sum` then gives that the single term $\phi_i'(s)$ is at most the whole sum:

$$
\phi_i'(s)\le \sum_{j\in t}\phi_j'(s)=\Phi'(s).
$$

Also $D\ge 0$, because `Metric.infDist_nonneg` says distance to a set is nonnegative. Multiplying the inequality $\phi_i'(s)\le \Phi'(s)$ by the nonnegative number $D$ gives

$$
\phi_i'(s)D\le \Phi'(s)D.
$$

Combining this with the local inequality $1\le \phi_i'(s)D$ yields

$$
1\le \Phi'(s)D.
$$

Finally, rewriting $s$ and $D$ and replacing $f(i)$ by $f(\bar x)$ using $f(\bar x)=f(i)$ gives exactly the desired inequality

```math
1\le \Phi'\!\left((f(x))_{\mathbb R}-(f(\bar x))_{\mathbb R}\right)\,
   d\!\left(0,\partial f(x)\right).
```

In the empty case $\Omega=\varnothing$, the proof chooses

$$
\varepsilon=1,\qquad \eta=1,\qquad \phi(s)=s.
$$

The inequalities $0\lt 1$ are verified by `norm_num`. The lemma `desingularizingFunction_id` states that the identity function is desingularizing for $\eta=1$: it is concave and continuous on $[0,1]$, differentiable on $(0,1)$, satisfies $\phi(0)=0$, and has derivative $1\gt 0$ on $(0,1)$. The universal KL inequality is then vacuous: if $\bar x\in\Omega$ were assumed, this would contradict $\Omega=\varnothing$, so `False.elim` closes that case. Thus the theorem is proved in both cases.

