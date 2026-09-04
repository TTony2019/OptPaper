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
The theorem states a second-order conjugation result. The variables are:

- \(n:\mathbb N\), a natural number.
- \(f, f^\star : \mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ n)\to \mathrm{EReal}\), extended-real-valued functions on the finite-dimensional real Euclidean space of dimension \(n\).
- \(A, A_{\mathrm{inv}} : \mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ n)\to_L[\mathbb R] \mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ n)\), continuous linear self-maps.

The hypotheses are:

- \(h_{\mathrm{convex}}\): the epigraph of \(f\) is convex over \(\mathbb R\), i.e. \(f\) is convex as an extended-real-valued function.
- \(h_{\mathrm{proper}}\): \(f\) is proper; in the proof this is used to get that \(f\) never takes the value \(-\infty\).
- \(h_{\mathrm{lsc}}\): \(f\) is lower semicontinuous.
- \(h_{\mathrm{conjugate}}\): \(f^\star\) is the Fenchel conjugate of \(f\), so
  \[
  f^\star(y)=\sup_x\bigl(\langle x,y\rangle - f(x)\bigr)
  \]
  in \(\mathrm{EReal}\).
- \(h_{\mathrm{symm}}\): \(A\) is symmetric.
- \(h_{\mathrm{pos}}\): for every nonzero \(x\),
  \[
  0<\langle A x,x\rangle.
  \]
  Thus \(A\) is positive definite.
- \(h_{\mathrm{Ainv\_right}}\) and \(h_{\mathrm{Ainv\_left}}\): \(A_{\mathrm{inv}}\) is a two-sided inverse of \(A\):
  \[
  A\circ A_{\mathrm{inv}}=\mathrm{id},\qquad A_{\mathrm{inv}}\circ A=\mathrm{id}.
  \]
- \(h_{\mathrm{finite}}\): eventually in a neighborhood of \(0\), \(f(x)\neq \top\), so \(f\) is finite near the origin.
- \(h_{\mathrm{expansion}}\): the normalized primal second-order remainder tends to \(0\) punctually:
  \[
  \frac{(f(x)).toReal - \frac12\langle A x,x\rangle}{\|x\|^2}
  \to 0
  \qquad\text{as }x\to 0,\ x\neq 0.
  \]

The conclusion is the corresponding second-order expansion for the conjugate:
\[
\frac{(f^\star(y)).toReal - \frac12\langle A_{\mathrm{inv}} y,y\rangle}{\|y\|^2}
\to 0
\qquad\text{as }y\to 0,\ y\neq 0.
\]

In other words, if \(f\) has second-order behavior
\[
f(x)=\frac12\langle A x,x\rangle+o(\|x\|^2)
\]
near \(0\), then its Fenchel conjugate has second-order behavior
\[
f^\star(y)=\frac12\langle A^{-1}y,y\rangle+o(\|y\|^2)
\]
near \(0\).

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
The proof begins by unpacking properness of \(f\). The command `rcases hproper` extracts the fact that \(f\) never equals \(-\infty\); this is called `hnot_bot`. The local finiteness assumption is named `hlocal_finite`, and since it holds on a neighborhood of \(0\), the command `mem_of_mem_nhds` gives `hf_zero_ne_top : f 0 ≠ ⊤`. Together with properness, one also has `hf_zero_ne_bot : f 0 ≠ ⊥`.

The inverse identities are converted to pointwise identities: for all \(y\),
\[
A(A_{\mathrm{inv}} y)=y,
\]
and for all \(x\),
\[
A_{\mathrm{inv}}(A x)=x.
\]
This is done using `congrArg` on the operator equality and then `simpa`.

The assumption `hexpansion` is turned into an explicit quantitative statement. For every \(\varepsilon>0\), on a punctured neighborhood of \(0\),
\[
\left|\frac{(f(x)).toReal - \frac12\langle A x,x\rangle}{\|x\|^2}\right|<\varepsilon.
\]
This is proved using `Ioo_mem_nhds` to say that \((-\varepsilon,\varepsilon)\) is a neighborhood of \(0\), then using `filter_upwards` and `abs_lt.mpr`.

The next block packages this into a uniform local quadratic estimate. For every \(\eta>0\), there exists \(r>0\) such that for all \(x\neq 0\) with \(\|x\|<r\),
\[
f(x)\neq \top,
\]
and
\[
\frac12\langle A x,x\rangle-\eta\|x\|^2
<
(f(x)).toReal
<
\frac12\langle A x,x\rangle+\eta\|x\|^2.
\]
This is `hlocal_quadratic_bounds`. It is obtained by intersecting the punctual limit estimate with the local finiteness assumption, rewriting `eventually_nhdsWithin_iff`, and using the metric characterization of eventual neighborhoods.

The proof then splits into two cases.

If \(n=0\), then the Euclidean space \(\mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\ 0)\) is a subsingleton; the only vector is \(0\). Hence the punctured set \(\{0\}^\complement\) is empty, so the punctured neighborhood filter is the bottom filter. The command `simpa` rewrites the limit as a limit from the bottom filter, which is always true by `Filter.tendsto_bot`.

Assume now \(n\neq 0\). Since \(A\) is positive definite and symmetric on a nonzero-dimensional space, the proof invokes `rayleigh_coercive_of_posdef` to obtain a coercivity constant \(m>0\) with
\[
m\|x\|^2\le \langle A x,x\rangle
\]
for all \(x\). The commands `letI` and `Nontrivial` provide a nonzero vector \(u\) and nontriviality.

A fixed parameter \(\eta=m/8\) is chosen. Since \(4\eta<m\), the quantity \(m/2-\eta\) is positive. The local quadratic bounds give a radius \(R>0\). Using the lemma `local_quadratic_coercive_lower`, the proof obtains a local lower bound
\[
\left(\frac m2-\eta\right)\|z\|^2\le f(z)
\]
for every nonzero \(z\) with \(\|z\|<R\). This is `hlocal_coercive`.

The proof then shows that \(f(0)=0\). It proves \(f(0)\le 0\) using lower semicontinuity and local upper quadratic bounds via `value_zero_le_of_local_quadratic`. It proves \(f(0)\ge 0\) using convexity and local quadratic bounds via `value_zero_ge_of_local_quadratic`. The command `le_antisymm` combines the two to give `hf0 : f 0 = 0`.

A radius \(\rho=R/2\) is chosen with \(0<\rho<R\). The lemma `convex_ray_lower_bound` converts the local coercive lower bound into a global linear lower bound outside the ball: for \(\rho\le \|x\|\),
\[
\left(\frac m2-\eta\right)\rho\|x\|\le f(x).
\]
This is then written more simply as \(c\|x\|\le f(x)\) with
\[
c=\left(\frac m2-\eta\right)\rho>0.
\]

Next the operator norm \(M=\|A_{\mathrm{inv}}\|\) is introduced. From norm inequalities one has
\[
\|A_{\mathrm{inv}} y\|\le M\|y\|,
\]
and if \(y\neq 0\), then \(A_{\mathrm{inv}} y\neq 0\). The proof also shows
\[
0\le \frac12\langle A_{\mathrm{inv}} y,y\rangle.
\]
This follows because
\[
\langle A_{\mathrm{inv}} y,y\rangle
=
\langle A(A_{\mathrm{inv}} y),A_{\mathrm{inv}} y\rangle,
\]
and \(A\) is positive definite.

Now the proof aims to show the metric limit for the conjugate. The command `rw [Metric.tendsto_nhds]` changes the goal to: for every \(\varepsilon>0\), eventually in the punctured neighborhood of \(0\), the normalized conjugate remainder is smaller than \(\varepsilon\).

