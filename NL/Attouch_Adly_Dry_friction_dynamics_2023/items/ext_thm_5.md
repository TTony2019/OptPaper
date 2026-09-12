## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_thm_5.lean`

## Lean statement
```lean
theorem gorni_conjugation_second_order {n : ℕ}
    (f fstar : EuclideanSpace ℝ (Fin n) → EReal)
    (A Ainv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (hproper : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f)
    (hconjugate : fstar = ERealFunction.conjugate f)
    (hsymm : A.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x)
    (hAinv_right : A.comp Ainv = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (hAinv_left : Ainv.comp A = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (hfinite : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin n)), f x ≠ ⊤)
    (hexpansion : Filter.Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ((f x).toReal - inner ℝ (A x) x / 2) / ‖x‖ ^ 2)
      (nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) (nhds 0)) :
    Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) =>
      ((fstar y).toReal - inner ℝ (Ainv y) y / 2) / ‖y‖ ^ 2)
      (nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) (nhds 0)
```

## Statement explanation
The theorem is stated for the Euclidean space $E=\mathbb R^n$. The objects are an extended-real-valued function $f:E\to\overline{\mathbb R}$, its putative Fenchel conjugate $f^*:E\to\overline{\mathbb R}$, and two continuous linear maps $A,A^{-1}:E\to E$.

The hypotheses say:

- $f$ has convex epigraph, so $f$ is convex as an extended-real-valued function.
- $f$ is proper; in the proof this is unpacked as $f(x)\ne -\infty$ for every $x$, together with a nonempty domain condition.
- $f$ is lower semicontinuous.
- $f^*$ is exactly the Fenchel conjugate of $f$, so

  $$
  f^*(y)=\sup_{x\in E}\bigl(\langle x,y\rangle-f(x)\bigr),
  $$

  with values in $\overline{\mathbb R}$.
- $A$ is symmetric and positive definite in the sense that

  $$
  \langle Ax,x\rangle>0
  $$

  for every $x\ne0$.
- $A^{-1}$ is a two-sided inverse of $A$:

  $$
  A\circ A^{-1}=\operatorname{id}_E,\qquad A^{-1}\circ A=\operatorname{id}_E.
  $$

- $f$ is finite near the origin: eventually, as $x\to0$, one has $f(x)\ne+\infty$. Together with properness this makes $f(x)$ a real number near $0$.
- The primal second-order expansion at the origin holds:

  $$
  \frac{(f(x))_{\mathbb R}-\frac12\langle Ax,x\rangle}{\|x\|^2}
  \longrightarrow 0
  $$

  as $x\to0$ along the punctured neighborhood $x\ne0$. Here $(f(x))_{\mathbb R}$ denotes the real value of the extended real number $f(x)$ when it is finite.

The conclusion is the dual second-order expansion for the Fenchel conjugate:

$$
\frac{(f^*(y))_{\mathbb R}-\frac12\langle A^{-1}y,y\rangle}{\|y\|^2}
\longrightarrow 0
$$

as $y\to0$ along the punctured neighborhood $y\ne0$.

Thus the theorem says that if a proper convex lower semicontinuous function has a second-order expansion at the origin with quadratic Hessian operator $A$, then its Fenchel conjugate has the corresponding second-order expansion at the origin with the inverse Hessian $A^{-1}$.

## Lean proof
```lean
by
  -- The source expansion is real-valued on a neighborhood of the origin.
  rcases hproper with ⟨hnot_bot, hdom⟩
  have hlocal_finite : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin n)),
      f x ≠ ⊤ := hfinite
  have hf_zero_ne_top : f 0 ≠ ⊤ :=
    mem_of_mem_nhds hlocal_finite
  have hf_zero_ne_bot : f 0 ≠ ⊥ := hnot_bot 0
  have hright_apply (y : EuclideanSpace ℝ (Fin n)) : A (Ainv y) = y := by
    simpa using congrArg (fun L => L y) hAinv_right
  have hleft_apply (x : EuclideanSpace ℝ (Fin n)) : Ainv (A x) = x := by
    simpa using congrArg (fun L => L x) hAinv_left
  -- The primal second-order hypothesis gives the quantitative estimate used in
  -- the Gorni ray-localization argument.
  have hlocal_remainder : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : EuclideanSpace ℝ (Fin n) in nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
        |((f x).toReal - inner ℝ (A x) x / 2) / ‖x‖ ^ 2| < ε := by
    intro ε hε
    have hmem : Set.Ioo (-ε) ε ∈ nhds (0 : ℝ) := by
      exact Ioo_mem_nhds (neg_lt_zero.mpr hε) hε
    filter_upwards [hexpansion.eventually hmem] with x hx
    exact abs_lt.mpr hx
  -- Package the punctured limit as explicit two-sided estimates on a ball.
  -- This is the real-valued input needed by the convex ray-localization step.
  have hlocal_quadratic_bounds : ∀ η : ℝ, 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ‖x‖ < r →
        f x ≠ ⊤ ∧
          inner ℝ (A x) x / 2 - η * ‖x‖ ^ 2 < (f x).toReal ∧
          (f x).toReal < inner ℝ (A x) x / 2 + η * ‖x‖ ^ 2 := by
    intro η hη
    have hfinite_within : ∀ᶠ x : EuclideanSpace ℝ (Fin n) in
        nhdsWithin 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))), f x ≠ ⊤ :=
      hlocal_finite.filter_mono nhdsWithin_le_nhds
    have hboth := (hlocal_remainder η hη).and hfinite_within
    rw [eventually_nhdsWithin_iff] at hboth
    rcases (Metric.eventually_nhds_iff.1 hboth) with ⟨r, hr, hr_ball⟩
    refine ⟨r, hr, ?_⟩
    intro x hx0 hxr
    have hx := hr_ball (by simpa [dist_zero_right] using hxr) (by simpa using hx0)
    rcases abs_lt.mp hx.1 with ⟨hlo, hup⟩
    have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    constructor
    · exact hx.2
    constructor
    · have hlo' : -η * ‖x‖ ^ 2 < (f x).toReal - inner ℝ (A x) x / 2 :=
        (lt_div_iff₀ hsq).mp hlo
      linarith
    · have hup' : (f x).toReal - inner ℝ (A x) x / 2 < η * ‖x‖ ^ 2 :=
        (div_lt_iff₀ hsq).mp hup
      linarith
  by_cases hn : n = 0
  · subst n
    have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have hempty : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) = ∅ := by
      ext y
      simp [Subsingleton.elim y 0]
    rw [hempty]
    simpa only [nhdsWithin_empty] using
      (Filter.tendsto_bot : Filter.Tendsto
        (fun y : EuclideanSpace ℝ (Fin 0) =>
          ((fstar y).toReal - inner ℝ (Ainv y) y / 2) / ‖y‖ ^ 2) ⊥ (nhds 0))
  · have hcoercive := rayleigh_coercive_of_posdef hn A hpos
    rcases hcoercive with ⟨m, hm_pos, hm⟩
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_iff_ne_zero.mpr hn)
    letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
    obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
    let η : ℝ := m / 8
    have hη : 0 < η := by
      dsimp [η]
      positivity
    have hηm : 4 * η < m := by
      dsimp [η]
      linarith
    obtain ⟨R, hR_pos, hRlocal⟩ := hlocal_quadratic_bounds η hη
    have hlocal_coercive : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖z‖ < R →
        (((m / 2 - η) * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z := by
      apply local_quadratic_coercive_lower f A hnot_bot hm hη
      intro z hz hzr
      exact ⟨(hRlocal z hz hzr).1, (hRlocal z hz hzr).2.1⟩
    have hcoercive_const : 0 < m / 2 - η := by
      dsimp [η]
      linarith
    have hf_zero_le : f 0 ≤ 0 := by
      apply value_zero_le_of_local_quadratic f A hlsc hnot_bot hlocal_finite u hu
      intro ε hε
      obtain ⟨r, hr, hlocal⟩ := hlocal_quadratic_bounds ε hε
      refine ⟨r, hr, ?_⟩
      intro x hx hxr
      exact ⟨(hlocal x hx hxr).1, (hlocal x hx hxr).2.2⟩
    have hf_zero_ge : 0 ≤ f 0 := by
      exact value_zero_ge_of_local_quadratic f A hconvex hnot_bot hlocal_finite u hu
        hlocal_quadratic_bounds
    have hf0 : f 0 = 0 := le_antisymm hf_zero_le hf_zero_ge
    let ρ : ℝ := R / 2
    have hρ : 0 < ρ := by
      dsimp [ρ]
      linarith
    have hρR : ρ < R := by
      dsimp [ρ]
      linarith
    have hray : ∀ x : EuclideanSpace ℝ (Fin n), ρ ≤ ‖x‖ →
        (((m / 2 - η) * ρ * ‖x‖ : ℝ) : EReal) ≤ f x := by
      exact convex_ray_lower_bound f hconvex hnot_bot hf0 hρ hρR hlocal_coercive
    let c : ℝ := (m / 2 - η) * ρ
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hray' : ∀ x : EuclideanSpace ℝ (Fin n), ρ ≤ ‖x‖ →
        ((c * ‖x‖ : ℝ) : EReal) ≤ f x := by
      intro x hx
      simpa [c, mul_assoc] using hray x hx
    let M : ℝ := ‖Ainv‖
    have hMnonneg : 0 ≤ M := by
      exact norm_nonneg _
    have hAinv_norm (y : EuclideanSpace ℝ (Fin n)) : ‖Ainv y‖ ≤ M * ‖y‖ := by
      simpa [M] using Ainv.le_opNorm y
    have hAinv_ne (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0) : Ainv y ≠ 0 := by
      intro hzero
      apply hy
      rw [← hright_apply y, hzero, map_zero]
    have hquad_inv_nonneg (y : EuclideanSpace ℝ (Fin n)) :
        0 ≤ inner ℝ (Ainv y) y / 2 := by
      by_cases hy : y = 0
      · simp [hy]
      · have hval : inner ℝ (Ainv y) y = inner ℝ (A (Ainv y)) (Ainv y) := by
          rw [hright_apply y]
          exact real_inner_comm _ _
        rw [hval]
        exact div_nonneg (hpos (Ainv y) (hAinv_ne y hy)).le (by norm_num)
    -- Use an error depending on the requested final neighbourhood; the fixed
    -- `η` above is retained only for the global coercive ray estimate.
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η' : ℝ := min (m / 8) (ε / (8 * (M ^ 2 + 1)))
    have hη' : 0 < η' := by
      dsimp [η']
      apply lt_min
      · positivity
      · positivity
    have hη'm : 2 * η' ≤ m / 2 := by
      have hle : η' ≤ m / 8 := min_le_left _ _
      linarith
    have hη'eps : 2 * η' * M ^ 2 < ε := by
      have hle : η' ≤ ε / (8 * (M ^ 2 + 1)) := min_le_right _ _
      have hden : 0 < M ^ 2 + 1 := by positivity
      have hsq : 0 ≤ M ^ 2 := sq_nonneg M
      have hfrac : M ^ 2 / (M ^ 2 + 1) < 1 := by
        apply (div_lt_one hden).mpr
        linarith
      calc
        2 * η' * M ^ 2 ≤ 2 * (ε / (8 * (M ^ 2 + 1))) * M ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) hsq
        _ = ε / 4 * (M ^ 2 / (M ^ 2 + 1)) := by field_simp; ring
        _ < ε / 4 * 1 := mul_lt_mul_of_pos_left hfrac (by linarith)
        _ = ε / 4 := by ring
        _ < ε := by linarith
    obtain ⟨r0, hr0pos, hlocal0⟩ := hlocal_quadratic_bounds η' hη'
    let r : ℝ := r0
    have hrpos : 0 < r := by simpa [r] using hr0pos
    have hlocal : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ‖x‖ < r →
        f x ≠ ⊤ ∧ inner ℝ (A x) x / 2 - η' * ‖x‖ ^ 2 < (f x).toReal ∧
          (f x).toReal < inner ℝ (A x) x / 2 + η' * ‖x‖ ^ 2 := by
      intro x hx hxr
      apply hlocal0 x hx
      simpa [r] using hxr
    have hlocal_coercive' : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖z‖ < r →
        (((m / 2 - η') * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z := by
      apply local_quadratic_coercive_lower f A hnot_bot hm hη'
      intro z hz hzr
      exact ⟨(hlocal z hz hzr).1, (hlocal z hz hzr).2.1⟩
    let ρ' : ℝ := r / 2
    have hρ' : 0 < ρ' := by dsimp [ρ']; linarith
    have hρ'r : ρ' < r := by dsimp [ρ']; linarith
    have hc'base : 0 < m / 2 - η' := by linarith [hη'm]
    have hray'' : ∀ x : EuclideanSpace ℝ (Fin n), ρ' ≤ ‖x‖ →
        (((m / 2 - η') * ρ' * ‖x‖ : ℝ) : EReal) ≤ f x := by
      exact convex_ray_lower_bound f hconvex hnot_bot hf0 hρ' hρ'r hlocal_coercive'
    let c' : ℝ := (m / 2 - η') * ρ'
    have hc' : 0 < c' := by dsimp [c']; positivity
    have hray''' : ∀ x : EuclideanSpace ℝ (Fin n), ρ' ≤ ‖x‖ →
        ((c' * ‖x‖ : ℝ) : EReal) ≤ f x := by
      intro x hx
      simpa [c', mul_assoc] using hray'' x hx
    let δ : ℝ := min (r / (2 * (M + 1))) (c' / 4)
    have hδ : 0 < δ := by
      dsimp [δ]
      apply lt_min <;> positivity
    simp only [dist_zero_right]
    rw [eventually_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, ?_⟩
    intro y hyδ hy0
    have hyδ' : ‖y‖ < δ := by simpa only [dist_zero_right] using hyδ
    have hy : y ≠ 0 := by simpa using hy0
    have hyc : ‖y‖ < c' / 2 := by
      have hd : δ ≤ c' / 4 := min_le_right _ _
      linarith [hyδ']
    have hyA : ‖Ainv y‖ < r := by
      have hd : δ ≤ r / (2 * (M + 1)) := min_le_left _ _
      have hbound := hAinv_norm y
      have hM : 0 ≤ M := hMnonneg
      have hyhalf : ‖y‖ < r / (2 * (M + 1)) := lt_of_lt_of_le hyδ' hd
      have hMle : M * ‖y‖ ≤ M * (r / (2 * (M + 1))) :=
        mul_le_mul_of_nonneg_left hyhalf.le hM
      calc
        ‖Ainv y‖ ≤ M * ‖y‖ := hbound
        _ ≤ M * (r / (2 * (M + 1))) := hMle
        _ < r := by
          have hden : 0 < 2 * (M + 1) := by positivity
          apply (lt_of_mul_lt_mul_right _ hden.le)
          field_simp
          nlinarith
    have hyAne : Ainv y ≠ 0 := hAinv_ne y hy
    have hyAlocal := hlocal (Ainv y) hyAne hyA
    -- First obtain the candidate lower bound in real arithmetic.
    have hA_sq : ‖Ainv y‖ ^ 2 ≤ M ^ 2 * ‖y‖ ^ 2 := by
      have := sq_le_sq₀ (norm_nonneg (Ainv y)) (mul_nonneg hMnonneg (norm_nonneg y)) |>.mpr
        (hAinv_norm y)
      nlinarith
    have hqA : inner ℝ (A (Ainv y)) (Ainv y) / 2 = inner ℝ (Ainv y) y / 2 := by
      rw [hright_apply y]
      exact congrArg (fun z : ℝ => z / 2) (real_inner_comm _ _)
    have hinnerA : inner ℝ y (Ainv y) = 2 * (inner ℝ (Ainv y) y / 2) := by
      rw [← real_inner_comm y (Ainv y), ← hright_apply y]
      ring
    have hlower_real : inner ℝ (Ainv y) y / 2 - η' * M ^ 2 * ‖y‖ ^ 2 <
        inner ℝ y (Ainv y) - (f (Ainv y)).toReal := by
      rw [hinnerA, ← hqA] at *
      nlinarith [hyAlocal.2.2]
    have hlower_e :
        ((inner ℝ (Ainv y) y / 2 - η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) <
          ((inner ℝ y (Ainv y) : ℝ) : EReal) - f (Ainv y) := by
      rw [← EReal.coe_toReal hyAlocal.1 (hnot_bot _), ← EReal.coe_sub]
      exact_mod_cast hlower_real
    have hlocal_upper : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ < r →
        ((inner ℝ y x : ℝ) : EReal) - f x ≤
          ((inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        rw [hf0]
        simp only [inner_zero_right, EReal.coe_zero, sub_zero]
        have hrest : 0 ≤ 2 * η' * M ^ 2 * ‖y‖ ^ 2 := by positivity
        exact_mod_cast (by nlinarith [hquad_inv_nonneg y] :
          0 ≤ inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2)
      have hxl := hlocal x hx0 hx
      have hreal := local_supremand_upper_real f A Ainv hsymm hAinv_right
        hη'.le hm hη'm hA_sq hxl.2.1
      rw [← EReal.coe_toReal hxl.1 (hnot_bot x), ← EReal.coe_sub]
      exact EReal.coe_le_coe hreal
    have houter_upper : ∀ x : EuclideanSpace ℝ (Fin n), ρ' ≤ ‖x‖ →
        ((inner ℝ y x : ℝ) : EReal) - f x ≤
          ((inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
      intro x hx
      by_cases hxtop : f x = ⊤
      · simp [hxtop]
      exact outer_supremand_upper f x y hnot_bot hxtop (hray''' x hx) hc' hyc
        (hquad_inv_nonneg y) hη'.le
    have hfstar_lower :
        ((inner ℝ (Ainv y) y / 2 - η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) < fstar y := by
      rw [hconjugate, ERealFunction.conjugate_apply]
      apply lt_of_lt_of_le hlower_e
      rw [real_inner_comm (Ainv y) y]
      exact le_iSup (fun x : EuclideanSpace ℝ (Fin n) =>
        ((inner ℝ x y : ℝ) : EReal) - f x) (Ainv y)
    have hfstar_upper : fstar y ≤
        ((inner ℝ (Ainv y) y / 2 + 2 * η' * M ^ 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
      rw [hconjugate, ERealFunction.conjugate_apply]
      apply iSup_le
      intro x
      by_cases hx : ‖x‖ < r
      · rw [real_inner_comm y x]
        exact hlocal_upper x hx
      · rw [real_inner_comm y x]
        apply houter_upper x
        have hrle : r ≤ ‖x‖ := le_of_not_gt hx
        have hhalf : r / 2 ≤ r := by nlinarith only [hrpos]
        change r / 2 ≤ ‖x‖
        exact hhalf.trans hrle
    have hfstar_bot : fstar y ≠ ⊥ := by
      intro hbot
      rw [hbot] at hfstar_lower
      exact (not_lt_bot) hfstar_lower
    have hfstar_top : fstar y ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hfstar_upper (by exact EReal.coe_lt_top _))
    have hynorm : (0 : ℝ) < ‖y‖ ^ 2 := norm_sq_pos_of_ne_zero y hy
    exact quotient_abs_lt_of_ereal_bounds hfstar_lower hfstar_upper hfstar_bot
      hfstar_top hynorm hη'eps
```

## Proof explanation
The proof begins by unpacking properness. From `hproper` it obtains

$$
\forall x,\ f(x)\ne -\infty
$$

and a nonempty-domain condition. It also records the hypothesis that $f$ is finite near $0$. Since the neighborhood filter at $0$ contains $0$, the proof derives

$$
f(0)\ne+\infty,
$$

and combining this with properness gives

$$
f(0)\ne-\infty.
$$

Next it uses the two inverse identities. Applying the equality of continuous linear maps $A\circ A^{-1}=\operatorname{id}$ to a vector $y$ gives

$$
A(A^{-1}y)=y.
$$

Similarly, applying $A^{-1}\circ A=\operatorname{id}$ to $x$ gives

$$
A^{-1}(Ax)=x.
$$

The later proof primarily uses the right-inverse relation $A(A^{-1}y)=y$.

The assumed second-order expansion is then converted into an absolute-error statement. For every $\varepsilon>0$, the interval $(-\varepsilon,\varepsilon)$ is a neighborhood of $0$ in $\mathbb R$. The convergence hypothesis therefore says that eventually along the punctured neighborhood of $0$,

$$
\left|
\frac{(f(x))_{\mathbb R}-\frac12\langle Ax,x\rangle}{\|x\|^2}
\right|<\varepsilon .
$$

This is the statement called `hlocal_remainder`.

From this absolute estimate, the proof obtains explicit two-sided local quadratic bounds. Given any $\eta>0$, it combines the absolute-error estimate with the eventual finiteness of $f$ near $0$. After translating “eventually on the punctured neighborhood” into “eventually near $0$ with the extra condition $x\ne0$”, the metric characterization of neighborhoods gives a radius $r>0$ such that for every $x\ne0$ with $\|x\|<r$,

$$
f(x)\ne+\infty
$$

and

$$
\left|
\frac{(f(x))_{\mathbb R}-\frac12\langle Ax,x\rangle}{\|x\|^2}
\right|<\eta .
$$

Since $x\ne0$, we have $\|x\|^2>0$. Multiplying the absolute inequality by the positive number $\|x\|^2$ gives the two real inequalities

$$
\frac12\langle Ax,x\rangle-\eta\|x\|^2
<
(f(x))_{\mathbb R}
<
\frac12\langle Ax,x\rangle+\eta\|x\|^2 .
$$

This is the lemma `hlocal_quadratic_bounds`, and it is the main real-valued local input used repeatedly later.

The proof then splits on whether $n=0$. If $n=0$, then $E=\mathbb R^0$ is a singleton, so the punctured set $\{0\}^{\complement}$ is empty. The restricted neighborhood filter is the bottom filter, and any function tends to any target filter from the bottom filter. Hence the desired limit is vacuous. This is the role of `Filter.tendsto_bot`.

Assume now $n\ne0$. The proof applies `rayleigh_coercive_of_posdef` to $A$ and the positive-definiteness hypothesis. That theorem says that in finite dimension, if $n\ne0$ and

$$
\langle Ax,x\rangle>0
$$

for every $x\ne0$, then there exists $m>0$ such that

$$
m\|x\|^2\le \langle Ax,x\rangle
$$

for every $x$. This is the coercivity constant used throughout the rest of the proof.

The proof also chooses a nonzero vector $u$, possible because $n\ne0$, and then sets

$$
\eta=\frac m8.
$$

Thus $\eta>0$ and $4\eta<m$, so in particular $m/2-\eta>0$. Using the local bounds with this $\eta$, it obtains a radius $R>0$. Then it applies `local_quadratic_coercive_lower`. That lemma says that if $f$ is never $-\infty$, $m\|x\|^2\le\langle Ax,x\rangle$, $\eta>0$, and locally for $x\ne0$, $\|x\|<R$,

$$
f(x)\ne+\infty,\qquad
\frac12\langle Ax,x\rangle-\eta\|x\|^2<(f(x))_{\mathbb R},
$$

then for every $z\ne0$ with $\|z\|<R$,

$$
\left(\left(\frac m2-\eta\right)\|z\|^2\right)_{\overline{\mathbb R}}\le f(z).
$$

So the coercivity of $A$ and the local lower quadratic estimate combine into a lower quadratic coercivity estimate for $f$ near the origin.

The proof next determines the value $f(0)$. It applies `value_zero_le_of_local_quadratic`. That result says that if $f$ is lower semicontinuous, never $-\infty$, finite near $0$, and locally satisfies upper quadratic bounds of the form

$$
(f(x))_{\mathbb R}
<
\frac12\langle Ax,x\rangle+\eta\|x\|^2
$$

for every $\eta>0$ on a sufficiently small punctured ball, then

$$
f(0)\le0.
$$

The proof supplies those upper bounds from `hlocal_quadratic_bounds`.

It then applies `value_zero_ge_of_local_quadratic`. That result says that if $f$ is convex in the epigraph sense, never $-\infty$, finite near $0$, and locally satisfies two-sided quadratic bounds

$$
\frac12\langle Ax,x\rangle-\eta\|x\|^2
<
(f(x))_{\mathbb R}
<
\frac12\langle Ax,x\rangle+\eta\|x\|^2
$$

for every $\eta>0$ on a sufficiently small punctured ball, then

$$
0\le f(0).
$$

Again `hlocal_quadratic_bounds` supplies exactly those estimates. Combining $f(0)\le0$ and $0\le f(0)$, the proof obtains

$$
f(0)=0.
$$

With this normalization, the proof applies `convex_ray_lower_bound`. This theorem says that if $f$ is convex, never $-\infty$, $f(0)=0$, $0<\rho<R$, and for every nonzero $z$ with $\|z\|<R$,

$$
((c\|z\|^2):\overline{\mathbb R})\le f(z),
$$

then for every $x$ with $\rho\le\|x\|$,

$$
((c\rho\|x\|):\overline{\mathbb R})\le f(x).
$$

In the proof one takes $\rho=R/2$ and $c=m/2-\eta$. Thus the local quadratic lower bound is converted into a global linear lower bound outside the smaller ball:

$$
\left(\left(\left(\frac m2-\eta\right)\rho\|x\|\right)_{\overline{\mathbb R}}\right)
\le f(x)
$$

whenever $\rho\le\|x\|$. This is the convex “ray-localization” step.

The proof then records several inverse-operator facts. It sets

$$
M=\|A^{-1}\|.
$$

Then $M\ge0$, and the operator norm inequality gives

$$
\|A^{-1}y\|\le M\|y\|.
$$

Also, if $y\ne0$, then $A^{-1}y\ne0$; otherwise $y=A(A^{-1}y)=A0=0$, contradiction. Finally it proves

$$
\frac12\langle A^{-1}y,y\rangle\ge0.
$$

If $y=0$, this is immediate. If $y\ne0$, then $A^{-1}y\ne0$, and using $A(A^{-1}y)=y$ together with symmetry of the real inner product,

$$
\langle A^{-1}y,y\rangle
=
\langle A(A^{-1}y),A^{-1}y\rangle
=
\langle y,A^{-1}y\rangle
>0.
$$

Thus the half-inner-product term is nonnegative.

The final epsilon-delta argument begins by rewriting the desired convergence using `Metric.tendsto_nhds`. Given $\varepsilon>0$, the proof chooses

$$
\eta'=\min\left(\frac m8,\frac{\varepsilon}{8(M^2+1)}\right).
$$

This is positive. Because $\eta'\le m/8$, it satisfies

$$
2\eta'\le \frac m2.
$$

Also the choice gives

$$
2\eta' M^2<\varepsilon.
$$

Indeed,

$$
2\eta' M^2
\le
2\cdot \frac{\varepsilon}{8(M^2+1)}M^2
=
\frac{\varepsilon}{4}\cdot \frac{M^2}{M^2+1}
<
\frac{\varepsilon}{4}
<
\varepsilon.
$$

The first inequality is used in `local_supremand_upper_real`; the second is used in the final quotient estimate.

Using `hlocal_quadratic_bounds` with this $\eta'$, the proof obtains a radius $r>0$ and local two-sided quadratic bounds for $f$. It then repeats the coercive lower-bound and convex-ray arguments with $\eta'$: with

$$
\rho'=\frac r2,\qquad
c'=\left(\frac m2-\eta'\right)\rho',
$$

one has $c'>0$, and for every $x$ with $\rho'\le\|x\|$,

$$
((c'\|x\|):\overline{\mathbb R})\le f(x).
$$

Finally it chooses

$$
\delta=\min\left(\frac{r}{2(M+1)},\frac{c'}4\right)>0.
$$

Take $y$ in the punctured neighborhood of $0$ with $\|y\|<\delta$. Then $\|y\|<c'/2$. Also

$$
\|A^{-1}y\|\le M\|y\|<r,
$$

by the choice of $\delta$, so $A^{-1}y$ lies in the local ball where the quadratic estimates for $f$ hold.

The lower bound for $f^*(y)$ is obtained by evaluating the Fenchel supremum at $x=A^{-1}y$. From the upper local estimate for $f$ at $A^{-1}y$,

$$
(f(A^{-1}y))_{\mathbb R}
<
\frac12\langle A(A^{-1}y),A^{-1}y\rangle+\eta'\|A^{-1}y\|^2
=
\frac12\langle y,A^{-1}y\rangle+\eta'\|A^{-1}y\|^2 .
$$

Using

$$
\|A^{-1}y\|^2\le M^2\|y\|^2
$$

and symmetry of the inner product, this rearranges to the real inequality

$$
\frac12\langle A^{-1}y,y\rangle-\eta'M^2\|y\|^2
<
\langle y,A^{-1}y\rangle-(f(A^{-1}y))_{\mathbb R}.
$$

Casting this real inequality into $\overline{\mathbb R}$ and using that $f^*(y)$ is the supremum of all terms $\langle x,y\rangle-f(x)$, the term at $x=A^{-1}y$ gives

$$
\left(\left(\frac12\langle A^{-1}y,y\rangle-\eta'M^2\|y\|^2\right)_{\overline{\mathbb R}}\right)
<
f^*(y).
$$

This is a strict lower extended-real bound for $f^*(y)$.

The upper bound for $f^*(y)$ is obtained by bounding every term in the supremum

$$
f^*(y)=\sup_x\bigl(\langle x,y\rangle-f(x)\bigr).
$$

If $\|x\|<r$ and $x\ne0$, the local lower quadratic bound for $f$ applies. The lemma `local_supremand_upper_real` is used here. It says that under the hypotheses

$$
A \text{ symmetric},\qquad A\circ A^{-1}=\operatorname{id},
$$

with $\eta'\ge0$, $m\|z\|^2\le\langle Az,z\rangle$, $2\eta'\le m/2$, and

$$
\|A^{-1}y\|^2\le M^2\|y\|^2,
$$

if at the point $x$ one has

$$
\frac12\langle Ax,x\rangle-\eta'\|x\|^2<(f(x))_{\mathbb R},
$$

then

$$
\langle y,x\rangle-(f(x))_{\mathbb R}
\le
\frac12\langle A^{-1}y,y\rangle+2\eta'M^2\|y\|^2.
$$

This is exactly the local upper estimate needed for the summand $\langle x,y\rangle-f(x)$ when $x$ is inside the ball. For $x=0$, the proof uses $f(0)=0$ and the nonnegativity of $\frac12\langle A^{-1}y,y\rangle$.

If instead $\|x\|\ge r$, then since $\rho'=r/2$, one has $\rho'\le\|x\|$. The ray lower bound gives

$$
f(x)\ge c'\|x\|.
$$

Together with $\|y\|<c'/2$, this makes $\langle y,x\rangle-f(x)$ bounded above by a nonnegative quadratic expression. More formally, the proof applies `outer_supremand_upper`. That lemma says that if $f$ is never $-\infty$, $f(x)\ne+\infty$, and

$$
((c\|x\|):\overline{\mathbb R})\le f(x),
$$

with $c>0$, $\|y\|<c/2$, and $q,\eta\ge0$, then

$$
((\langle y,x\rangle)_{\overline{\mathbb R}})-f(x)
\le
((q+2\eta M^2\|y\|^2)_{\overline{\mathbb R}}).
$$

In the proof, $c=c'$, $q=\frac12\langle A^{-1}y,y\rangle$, and $\eta=\eta'$. If $f(x)=+\infty$, the left-hand side is $-\infty$ and the inequality is trivial.

Thus every summand in the supremum defining $f^*(y)$ is bounded above by

$$
\frac12\langle A^{-1}y,y\rangle+2\eta'M^2\|y\|^2.
$$

Taking the supremum gives

$$
f^*(y)
\le
\left(\left(\frac12\langle A^{-1}y,y\rangle+2\eta'M^2\|y\|^2\right)_{\overline{\mathbb R}}\right).
$$

The proof then notes that $f^*(y)\ne-\infty$ because it is strictly larger than a real extended-real number, and $f^*(y)\ne+\infty$ because it is bounded above by a finite real extended-real number. Also, since $y\ne0$, `norm_sq_pos_of_ne_zero` gives

$$
0<\|y\|^2.
$$

Finally the proof applies `quotient_abs_lt_of_ereal_bounds`. That lemma says that if a finite extended-real number $z$ satisfies

$$
((q-\eta M^2 s):\overline{\mathbb R})<z
\le
((q+2\eta M^2 s):\overline{\mathbb R}),
$$

if $s>0$, and if

$$
2\eta M^2<\varepsilon,
$$

then

$$
\left|\frac{z_{\mathbb R}-q}{s}\right|<\varepsilon.
$$

Here one takes

$$
z=f^*(y),\qquad q=\frac12\langle A^{-1}y,y\rangle,\qquad s=\|y\|^2.
$$

The lower and upper bounds for $f^*(y)$, positivity of $s$, and the previously established inequality $2\eta'M^2<\varepsilon$ give exactly

$$
\left|
\frac{(f^*(y))_{\mathbb R}-\frac12\langle A^{-1}y,y\rangle}{\|y\|^2}
\right|<\varepsilon.
$$

Since this was proved for every $\varepsilon>0$ and for all sufficiently small nonzero $y$, the desired punctured limit

$$
\frac{(f^*(y))_{\mathbb R}-\frac12\langle A^{-1}y,y\rangle}{\|y\|^2}
\longrightarrow 0
$$

as $y\to0$, $y\ne0$, follows.

