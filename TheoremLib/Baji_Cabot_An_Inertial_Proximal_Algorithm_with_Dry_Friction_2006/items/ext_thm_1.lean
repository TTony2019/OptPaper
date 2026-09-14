import Mathlib
import Foundation.SetValued.Basic
import Foundation.SetValued.Fitzpatrick
import Foundation.Convex.Conjugate
import Foundation.SetValued.Yosida
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_1

/-!
# Sum of maximal monotone operators (Brézis Corollary 2.7)
Let $A, B: H \Rightarrow H$ be maximal monotone operators. If
$\operatorname{int}(\operatorname{dom} A) \cap \operatorname{dom} B \neq \emptyset$,
then $A + B$ is maximal monotone.
Cited from: H. Brézis, Opérateurs maximaux monotones dans les espaces de Hilbert
et équations d'évolution, Lecture Notes 5, North Holland, Amsterdam, 1972, Corollary 2.7.
-/
open SetValuedOperator
open scoped Pointwise
open scoped Topology
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The fiberwise infimal convolution of the Fitzpatrick functions of `A` and `B`. -/
noncomputable def fitzpatrickSum (A B : SetValuedOperator H H) (x u : H) : EReal :=
  ⨅ u₁ : H, ⨅ u₂ : H, ⨅ (_ : u₁ + u₂ = u),
    fitzpatrick A x u₁ + fitzpatrick B x u₂

/-- The product-space form of `fitzpatrickSum`, as used by Fenchel conjugation. -/
noncomputable def fitzpatrickSumProd (A B : SetValuedOperator H H) : H × H → EReal :=
  fun p ↦ fitzpatrickSum A B p.1 p.2

/-- The Fenchel conjugate on `H × H`, transported through Mathlib's canonical
`WithLp 2` product Hilbert structure.  This is the transpose-conjugate form used in
the Fitzpatrick sum argument. -/
noncomputable def productConjugate (G : H × H → EReal) (p : H × H) : EReal :=
  ERealFunction.conjugate
    (fun q : WithLp 2 (H × H) ↦ G (WithLp.ofLp q))
    (WithLp.toLp 2 p)

/-- The transported product conjugate is the supremum of the componentwise
pairing defects. -/
theorem productConjugate_apply (G : H × H → EReal) (p : H × H) :
    productConjugate G p =
      ⨆ q : H × H,
        (((inner ℝ q.1 p.1 + inner ℝ q.2 p.2 : ℝ) : EReal) - G q) := by
  unfold productConjugate
  rw [ERealFunction.conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro q
    simpa [WithLp.prod_inner_apply] using
      (le_iSup
        (fun q' : H × H ↦
          (((inner ℝ q'.1 p.1 + inner ℝ q'.2 p.2 : ℝ) : EReal) - G q'))
        q.ofLp)
  · refine iSup_le ?_
    intro q
    simpa [WithLp.prod_inner_apply] using
      (le_iSup
        (fun q' : WithLp 2 (H × H) ↦
          (((inner ℝ q' (WithLp.toLp 2 p) : ℝ) : EReal) - G q'.ofLp))
        (WithLp.toLp 2 q))

/-- Transporting a pair function through the `WithLp 2` product bridge preserves
convexity of its Fenchel conjugate: the product conjugate of a convex pair
function is convex.  This is the midpoint-convexity input to the monotonicity of
the conjugate contact-set operator (Bauschke--Combettes Theorem 20.46(i)). -/
theorem productConjugate_convex (F : H × H → EReal)
    (hF : ERealFunction.IsConvex F) :
    ERealFunction.IsConvex (productConjugate F) := by
  intro p q a ha0 ha1
  rw [productConjugate]
  have hlin : WithLp.toLp 2 (a • p + (1 - a) • q)
      = a • WithLp.toLp 2 p + (1 - a) • WithLp.toLp 2 q := by
    simp
  rw [hlin]
  exact (ERealFunction.conjugate_mem_gamma
    (fun r : WithLp 2 (H × H) ↦ F (WithLp.ofLp r))).1 ha0 ha1

/-- The Fenchel conjugate of a Fitzpatrick function, with the paper's argument order. -/
noncomputable def fitzpatrickConjugate (A : SetValuedOperator H H) (u x : H) : EReal :=
  productConjugate (fitzpatrickProd A) (u, x)

/-- The split conjugate appearing in the Fitzpatrick sum theorem. -/
noncomputable def fitzpatrickSumConjugate
    (A B : SetValuedOperator H H) (u x : H) : EReal :=
  ⨅ u₁ : H, ⨅ u₂ : H, ⨅ (_ : u₁ + u₂ = u),
    fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x

/-- The fibre infimal convolution of two functions on `H × H`, sharing the
first coordinate and convolving in the second coordinate. -/
noncomputable def partialInfimalConvolution
    (φ ψ : H × H → EReal) : H × H → EReal :=
  fun p ↦ ⨅ u₁ : H, ⨅ u₂ : H, ⨅ (_ : u₁ + u₂ = p.2),
    φ (p.1, u₁) + ψ (p.1, u₂)

/-- The fibrewise sum of the product-space Fenchel conjugates of two functions
on `H × H`. -/
noncomputable def partialConjugateSum
    (φ ψ : H × H → EReal) : H × H → EReal :=
  fun p ↦ ⨅ u₁ : H, ⨅ u₂ : H, ⨅ (_ : u₁ + u₂ = p.1),
    productConjugate φ (u₁, p.2) + productConjugate ψ (u₂, p.2)

/-- The interior-domain qualification for the shared-variable infimal
convolution: `0` lies in the interior of the projection onto the shared first
coordinate of `dom φ - dom ψ`. -/
def partialInfimalQualification (φ ψ : H × H → EReal) : Prop :=
  0 ∈ interior ((fun p : H × H ↦ p.1) ''
    (ERealFunction.dom φ - ERealFunction.dom ψ))

/-- The fiberwise Fitzpatrick sum dominates the pairing, independently of the
interior-domain qualification. -/
theorem inner_le_fitzpatrickSum (A B : SetValuedOperator H H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (x u : H) :
    ((inner ℝ x u : ℝ) : EReal) ≤ fitzpatrickSum A B x u := by
  unfold fitzpatrickSum
  refine le_iInf ?_
  intro u₁
  refine le_iInf ?_
  intro u₂
  refine le_iInf ?_
  intro hsum
  have hA' := inner_le_fitzpatrick_of_maximal (A := A) hA x u₁
  have hB' := inner_le_fitzpatrick_of_maximal (A := B) hB x u₂
  have hpair : ((inner ℝ x u : ℝ) : EReal) =
      ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := by
    rw [← hsum, inner_add_right, EReal.coe_add]
  calc
    ((inner ℝ x u : ℝ) : EReal)
        = ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := hpair
    _ ≤ fitzpatrick A x u₁ + fitzpatrick B x u₂ := add_le_add hA' hB'

/-- The interior-domain qualification used in the Attouch--Brézis sum argument,
where `-` denotes the Minkowski difference of the two Fitzpatrick domains. -/
def fitzpatrickQualification (A B : SetValuedOperator H H) : Prop :=
  0 ∈ interior ((fun p : H × H ↦ p.1) ''
    (ERealFunction.dom (fitzpatrickProd A) - ERealFunction.dom (fitzpatrickProd B)))

/-- The qualification needed by the Fitzpatrick sum theorem follows from the paper's
interior-domain hypothesis. -/
theorem fitzpatrick_interior_qualification
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hdom : (interior A.dom ∩ B.dom).Nonempty) :
    fitzpatrickQualification A B := by
  rcases hdom with ⟨p, hpint, hpBdom⟩
  rcases (SetValuedOperator.mem_dom_iff B p).mp hpBdom with ⟨b, hb⟩
  rw [fitzpatrickQualification, mem_interior_iff_mem_nhds]
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hpint) with ⟨ε, hε, hballA⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) hε) ?_
  intro z hz
  rw [Set.mem_image]
  have hqz : p + z ∈ A.dom := by
    apply interior_subset
    apply hballA
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    simpa [dist_eq_norm, add_sub_cancel_left] using hz
  rcases (SetValuedOperator.mem_dom_iff A (p + z)).mp hqz with ⟨a, ha⟩
  refine ⟨((p + z, a) - (p, b)), Set.sub_mem_sub ?_ ?_, ?_⟩
  · change fitzpatrickProd A (p + z, a) < ⊤
    dsimp [fitzpatrickProd]
    rw [fitzpatrick_graph_eq_inner hA.1 ha]
    exact EReal.coe_lt_top _
  · change fitzpatrickProd B (p, b) < ⊤
    dsimp [fitzpatrickProd]
    rw [fitzpatrick_graph_eq_inner hB.1 hb]
    exact EReal.coe_lt_top _
  · simp

/-- The transpose-conjugate of the Fitzpatrick function of a maximal monotone operator
dominates the pairing, with equality exactly on the graph. -/
theorem fitzpatrick_conjugate_characterization
    {T : SetValuedOperator H H} (hT : IsMaximalMonotone T) (y v : H) :
    ((inner ℝ y v : ℝ) : EReal) ≤ fitzpatrickConjugate T v y ∧
      (fitzpatrickConjugate T v y = ((inner ℝ y v : ℝ) : EReal) ↔ v ∈ T y) := by
  have hupper (hv : v ∈ T y) :
      fitzpatrickConjugate T v y ≤ ((inner ℝ y v : ℝ) : EReal) := by
    rw [fitzpatrickConjugate, productConjugate_apply]
    refine iSup_le ?_
    rintro ⟨z, w⟩
    have hfitz :
        (((inner ℝ z v + inner ℝ y w - inner ℝ y v : ℝ) : EReal) ≤
          fitzpatrick T z w) :=
      le_sSup ⟨y, v, hv, by ring_nf⟩
    have hfitz' :
        ((((inner ℝ z v + inner ℝ w y : ℝ) : EReal) -
            ((inner ℝ y v : ℝ) : EReal)) ≤ fitzpatrick T z w) := by
      have hfitz'' :
          (((inner ℝ z v + inner ℝ w y - inner ℝ y v : ℝ) : EReal) ≤
            fitzpatrick T z w) := by
        simpa [real_inner_comm] using hfitz
      simpa [EReal.coe_sub, EReal.coe_add] using hfitz''
    have hsum :
        (((inner ℝ z v + inner ℝ w y : ℝ) : EReal) ≤
          fitzpatrick T z w + ((inner ℝ y v : ℝ) : EReal)) :=
      (EReal.sub_le_iff_le_add
        (a := (((inner ℝ z v + inner ℝ w y : ℝ) : EReal)))
        (b := ((inner ℝ y v : ℝ) : EReal))
        (c := fitzpatrick T z w)
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp hfitz'
    exact
      (EReal.sub_le_iff_le_add
        (a := (((inner ℝ z v + inner ℝ w y : ℝ) : EReal)))
        (b := fitzpatrick T z w)
        (c := ((inner ℝ y v : ℝ) : EReal))
        (Or.inl (fitzpatrick_ne_bot (A := T) hT z w))
        (Or.inr (EReal.coe_ne_bot _))).mpr (by simpa [add_comm] using hsum)
  have hviol (hv : v ∉ T y) :
      ∃ z w : H, w ∈ T z ∧ inner ℝ (v - w) (y - z) < 0 := by
    by_contra h
    push Not at h
    exact hv (mem_of_monotonically_related_to_graph hT (by
      intro z w hw
      exact h z w hw))
  have hstrict (hv : v ∉ T y) :
      ((inner ℝ y v : ℝ) : EReal) < fitzpatrickConjugate T v y := by
    rcases hviol hv with ⟨z, w, hw, hneg⟩
    rw [fitzpatrickConjugate, productConjugate_apply]
    have hgraph := fitzpatrick_graph_eq_inner hT.1 hw
    have hterm :
        ((((inner ℝ z v + inner ℝ w y : ℝ) : EReal) - fitzpatrick T z w) =
          (((inner ℝ z v + inner ℝ w y - inner ℝ z w : ℝ) : EReal))) := by
      rw [hgraph]
      exact (EReal.coe_sub _ _).symm
    have hreal :
        inner ℝ y v < inner ℝ z v + inner ℝ w y - inner ℝ z w := by
      have hd :
          inner ℝ z v + inner ℝ w y - inner ℝ z w - inner ℝ y v =
            -inner ℝ (v - w) (y - z) := by
        simp only [inner_sub_left, inner_sub_right]
        rw [real_inner_comm z v, real_inner_comm z w, real_inner_comm y v]
        ring
      nlinarith
    have hlt :
        ((inner ℝ y v : ℝ) : EReal) <
          (((inner ℝ z v + inner ℝ w y : ℝ) : EReal) - fitzpatrick T z w) := by
      rw [hterm]
      exact EReal.coe_lt_coe hreal
    exact lt_of_lt_of_le hlt
      (le_iSup
        (fun q : H × H ↦
          (((inner ℝ q.1 v + inner ℝ q.2 y : ℝ) : EReal) -
            fitzpatrick T q.1 q.2))
        (z, w))
  have hlower : ((inner ℝ y v : ℝ) : EReal) ≤ fitzpatrickConjugate T v y := by
    by_cases hv : v ∈ T y
    · rw [fitzpatrickConjugate, productConjugate_apply]
      have hgraph := fitzpatrick_graph_eq_inner hT.1 hv
      have hterm :
          ((((inner ℝ y v : ℝ) : EReal) + ((inner ℝ v y : ℝ) : EReal)) -
              fitzpatrick T y v =
            ((inner ℝ y v : ℝ) : EReal)) := by
        rw [← EReal.coe_add]
        rw [hgraph]
        rw [← EReal.coe_sub]
        exact congrArg (fun r : ℝ => (r : EReal)) (by rw [real_inner_comm v y]; ring)
      calc
        ((inner ℝ y v : ℝ) : EReal)
            = (((inner ℝ y v : ℝ) : EReal) + ((inner ℝ v y : ℝ) : EReal)) -
                fitzpatrick T y v := hterm.symm
        _ ≤ ⨆ q : H × H,
              (((inner ℝ q.1 v + inner ℝ q.2 y : ℝ) : EReal) -
                fitzpatrick T q.1 q.2) :=
            le_iSup
              (fun q : H × H ↦
                (((inner ℝ q.1 v + inner ℝ q.2 y : ℝ) : EReal) -
                  fitzpatrick T q.1 q.2))
              (y, v)
    · exact (hstrict hv).le
  refine ⟨hlower, ?_⟩
  constructor
  · intro heq
    by_contra hv
    have hgt := hstrict hv
    rw [heq] at hgt
    exact (lt_irrefl _) hgt
  · intro hv
    exact le_antisymm (hupper hv) hlower

/-- The Chapter 20 quadratic test function
`G_(z,w)(y,v) = -⟪y,v⟫ + ⟪z-y,w-v⟫ + ‖z-y‖^2/2 + ‖w-v‖^2/2` used in the
maximality argument of Bauschke--Combettes Theorem 20.46(ii). -/
noncomputable def quadraticG (z w : H) : H × H → EReal :=
  fun p ↦ (((- inner ℝ p.1 p.2 + inner ℝ (z - p.1) (w - p.2) +
      (1 / 2 : ℝ) * (‖z - p.1‖ ^ 2 + ‖w - p.2‖ ^ 2) : ℝ)) : EReal)

/-- Normal form of the quadratic test function: it is the half squared norm of the
pair minus the pairing against the diagonal `(z + w, z + w)` plus a fixed offset. -/
private lemma quadraticG_normal (z w : H) (q : H × H) :
    quadraticG z w q =
      (((1 / 2 : ℝ) * (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2)
        - (inner ℝ q.1 (z + w) + inner ℝ q.2 (z + w))
        + (1 / 2 : ℝ) * ‖z + w‖ ^ 2 : ℝ) : EReal) := by
  rw [quadraticG]
  congr 1
  have hz : ‖z - q.1‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z q.1 + ‖q.1‖ ^ 2 := by
    rw [norm_sub_sq_real]
  have hw : ‖w - q.2‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w q.2 + ‖q.2‖ ^ 2 := by
    rw [norm_sub_sq_real]
  have hzw : ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + 2 * inner ℝ z w + ‖w‖ ^ 2 := by
    rw [norm_add_sq_real]
  have hcross : inner ℝ (z - q.1) (w - q.2)
      = inner ℝ z w - inner ℝ z q.2 - inner ℝ q.1 w + inner ℝ q.1 q.2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  have hsum1 : inner ℝ q.1 (z + w) = inner ℝ q.1 z + inner ℝ q.1 w := by
    rw [inner_add_right]
  have hsum2 : inner ℝ q.2 (z + w) = inner ℝ q.2 z + inner ℝ q.2 w := by
    rw [inner_add_right]
  nlinarith [hz, hw, hzw, hcross, hsum1, hsum2, real_inner_comm z q.1,
    real_inner_comm z q.2, real_inner_comm w q.2]

/-- Adding the pairing to the quadratic test function is the half squared norm of the
translated diagonal `(x - z) + (u - w)`, hence nonnegative. -/
private lemma quadraticG_add_pairing_eq (z w : H) (p : H × H) :
    quadraticG z w p + ((inner ℝ p.1 p.2 : ℝ) : EReal)
      = (((1 / 2 : ℝ) * ‖(p.1 - z) + (p.2 - w)‖ ^ 2 : ℝ) : EReal) := by
  rw [quadraticG, ← EReal.coe_add]
  congr 1
  have hnn : ‖(p.1 - z) + (p.2 - w)‖ ^ 2 = ‖(z - p.1) + (w - p.2)‖ ^ 2 := by
    rw [show (p.1 - z) + (p.2 - w) = -((z - p.1) + (w - p.2)) by abel, norm_neg]
  rw [hnn]
  have hexp : ‖(z - p.1) + (w - p.2)‖ ^ 2
      = ‖z - p.1‖ ^ 2 + 2 * inner ℝ (z - p.1) (w - p.2) + ‖w - p.2‖ ^ 2 := by
    simpa [two_mul] using norm_add_sq_real (z - p.1) (w - p.2)
  rw [hexp]
  ring

private lemma quadraticG_add_pairing_nonneg (z w : H) (p : H × H) :
    (0 : EReal) ≤ quadraticG z w p + ((inner ℝ p.1 p.2 : ℝ) : EReal) := by
  rw [quadraticG_add_pairing_eq]
  exact EReal.coe_nonneg.mpr (by positivity)

private lemma quadraticG_add_pairing_eq_zero_iff (z w : H) (p : H × H) :
    quadraticG z w p + ((inner ℝ p.1 p.2 : ℝ) : EReal) = 0 ↔ p.1 - z = w - p.2 := by
  rw [quadraticG_add_pairing_eq]
  constructor
  · intro h
    have hcoe : ((1 / 2 : ℝ) * ‖(p.1 - z) + (p.2 - w)‖ ^ 2 : ℝ) = 0 :=
      EReal.coe_eq_coe_iff.mp (by simpa using h)
    have hsq : ‖(p.1 - z) + (p.2 - w)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(p.1 - z) + (p.2 - w)‖]
    have hzero : (p.1 - z) + (p.2 - w) = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    have := eq_neg_of_add_eq_zero_left hzero
    rw [this]
    abel
  · intro hrel
    have hzero : (p.1 - z) + (p.2 - w) = 0 := by rw [hrel]; abel
    rw [hzero]
    simp

/-- Bauschke--Combettes Lemma 20.45, in the form used by Theorem 20.46(ii): the
quadratic test function `G_(z,w)` is self-conjugate up to the swap
`(y,v) ↦ (-v,-y)`, dominates the negation of the pairing, and its zero set
together with the sign condition `⟪z-y,w-v⟫ ≥ 0` collapses to `(z,w)`. -/
theorem quadraticG_lemma (z w : H) :
    productConjugate (quadraticG z w) =
        (fun p : H × H ↦ quadraticG z w (-p.2, -p.1)) ∧
      (∀ p : H × H,
        (0 : EReal) ≤ quadraticG z w p + ((inner ℝ p.1 p.2 : ℝ) : EReal)) ∧
      (∀ p : H × H,
        quadraticG z w p + ((inner ℝ p.1 p.2 : ℝ) : EReal) = 0 ↔
          p.1 - z = w - p.2) ∧
      (∀ p : H × H,
        quadraticG z w p + ((inner ℝ p.1 p.2 : ℝ) : EReal) = 0 →
          0 ≤ inner ℝ (z - p.1) (w - p.2) → p = (z, w)) := by
  refine ⟨?_, quadraticG_add_pairing_nonneg z w, quadraticG_add_pairing_eq_zero_iff z w, ?_⟩
  · funext p
    rw [productConjugate_apply]
    apply le_antisymm
    · refine iSup_le (fun q => ?_)
      rw [quadraticG_normal z w q, quadraticG_normal z w (-p.2, -p.1), ← EReal.coe_sub]
      refine EReal.coe_le_coe_iff.mpr ?_
      have ha : (1 / 2 : ℝ) * ‖q.1 - (p.1 + (z + w))‖ ^ 2
          = (1 / 2 : ℝ) * ‖q.1‖ ^ 2 - inner ℝ q.1 (p.1 + (z + w))
            + (1 / 2 : ℝ) * ‖p.1 + (z + w)‖ ^ 2 := by
        rw [norm_sub_sq_real]; ring
      have hb : (1 / 2 : ℝ) * ‖q.2 - (p.2 + (z + w))‖ ^ 2
          = (1 / 2 : ℝ) * ‖q.2‖ ^ 2 - inner ℝ q.2 (p.2 + (z + w))
            + (1 / 2 : ℝ) * ‖p.2 + (z + w)‖ ^ 2 := by
        rw [norm_sub_sq_real]; ring
      have hp1 : ‖p.1 + (z + w)‖ ^ 2
          = ‖p.1‖ ^ 2 + 2 * inner ℝ p.1 (z + w) + ‖z + w‖ ^ 2 := by
        rw [norm_add_sq_real]
      have hp2 : ‖p.2 + (z + w)‖ ^ 2
          = ‖p.2‖ ^ 2 + 2 * inner ℝ p.2 (z + w) + ‖z + w‖ ^ 2 := by
        rw [norm_add_sq_real]
      have hi1 : inner ℝ q.1 (p.1 + (z + w)) = inner ℝ q.1 p.1 + inner ℝ q.1 (z + w) := by
        rw [inner_add_right]
      have hi2 : inner ℝ q.2 (p.2 + (z + w)) = inner ℝ q.2 p.2 + inner ℝ q.2 (z + w) := by
        rw [inner_add_right]
      have hn1 : ‖(-p.2 : H)‖ ^ 2 = ‖p.2‖ ^ 2 := by rw [norm_neg]
      have hn2 : ‖(-p.1 : H)‖ ^ 2 = ‖p.1‖ ^ 2 := by rw [norm_neg]
      have hin1 : inner ℝ (-p.2) (z + w) = -inner ℝ p.2 (z + w) := by rw [inner_neg_left]
      have hin2 : inner ℝ (-p.1) (z + w) = -inner ℝ p.1 (z + w) := by rw [inner_neg_left]
      nlinarith [sq_nonneg ‖q.1 - (p.1 + (z + w))‖,
        sq_nonneg ‖q.2 - (p.2 + (z + w))‖]
    · refine le_iSup_of_le ((p.1 + (z + w), p.2 + (z + w))) ?_
      rw [quadraticG_normal z w (p.1 + (z + w), p.2 + (z + w)),
        quadraticG_normal z w (-p.2, -p.1), ← EReal.coe_sub]
      refine EReal.coe_le_coe_iff.mpr ?_
      have hp1 : ‖p.1 + (z + w)‖ ^ 2
          = ‖p.1‖ ^ 2 + 2 * inner ℝ p.1 (z + w) + ‖z + w‖ ^ 2 := by
        rw [norm_add_sq_real]
      have hp2 : ‖p.2 + (z + w)‖ ^ 2
          = ‖p.2‖ ^ 2 + 2 * inner ℝ p.2 (z + w) + ‖z + w‖ ^ 2 := by
        rw [norm_add_sq_real]
      have hq1 : inner ℝ (p.1 + (z + w)) p.1 + inner ℝ (p.1 + (z + w)) (z + w)
          = ‖p.1 + (z + w)‖ ^ 2 := by
        rw [← inner_add_right, real_inner_self_eq_norm_sq]
      have hq2 : inner ℝ (p.2 + (z + w)) p.2 + inner ℝ (p.2 + (z + w)) (z + w)
          = ‖p.2 + (z + w)‖ ^ 2 := by
        rw [← inner_add_right, real_inner_self_eq_norm_sq]
      have hn1 : ‖(-p.2 : H)‖ ^ 2 = ‖p.2‖ ^ 2 := by rw [norm_neg]
      have hn2 : ‖(-p.1 : H)‖ ^ 2 = ‖p.1‖ ^ 2 := by rw [norm_neg]
      have hin1 : inner ℝ (-p.2) (z + w) = -inner ℝ p.2 (z + w) := by rw [inner_neg_left]
      have hin2 : inner ℝ (-p.1) (z + w) = -inner ℝ p.1 (z + w) := by rw [inner_neg_left]
      nlinarith
  · intro p hzero hcross
    have hrel : p.1 - z = w - p.2 :=
      (quadraticG_add_pairing_eq_zero_iff z w p).mp hzero
    have hz : p.1 = z := by
      have hcross' : 0 ≤ -‖p.1 - z‖ ^ 2 := by
        calc 0 ≤ inner ℝ (z - p.1) (w - p.2) := hcross
          _ = inner ℝ (z - p.1) (p.1 - z) := by rw [← hrel]
          _ = -‖p.1 - z‖ ^ 2 := by
            rw [show z - p.1 = -(p.1 - z) by abel, inner_neg_left, real_inner_self_eq_norm_sq]
      have hle : ‖p.1 - z‖ ^ 2 ≤ 0 := by linarith
      have h0 : ‖p.1 - z‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
      have hsub : p.1 - z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
      exact sub_eq_zero.mp hsub
    have hw : p.2 = w := by
      have hz0 : p.1 - z = 0 := by rw [hz]; abel
      exact (sub_eq_zero.mp (by rw [← hrel, hz0])).symm
    exact Prod.ext hz hw

/-- Bauschke--Combettes Theorem 20.46(i): if the conjugate of `F` is convex and
dominates the pairing, then the conjugate contact-set operator
`x ↦ {u | F*(u,x) = ⟪x,u⟫}` is monotone. -/
theorem contact_operator_monotone (F : H × H → EReal)
    (hFconjConvex : ERealFunction.IsConvex (productConjugate F))
    (hconjLower : ∀ u x : H,
      ((inner ℝ x u : ℝ) : EReal) ≤ productConjugate F (u, x)) :
    IsMonotone
      (fun x : H =>
        {u : H | productConjugate F (u, x) = ((inner ℝ x u : ℝ) : EReal)}) := by
  intro x y u hu v hv
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hhalfE :
      (1 : EReal) - (((1 : ℝ) / 2 : ℝ) : EReal) = (((1 : ℝ) / 2 : ℝ) : EReal) := by
    rw [← EReal.coe_one, ← EReal.coe_sub]
    norm_num
  have hconv := hFconjConvex (x := (u, x)) (y := (v, y))
      (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [hhalf, hhalfE] at hconv
  have hmid : (1 / 2 : ℝ) • (u, x) + (1 / 2 : ℝ) • (v, y)
      = ((1 / 2 : ℝ) • (u + v), (1 / 2 : ℝ) • (x + y)) := by
    ext <;> simp [Prod.smul_mk, smul_add]
  rw [hmid] at hconv
  have hlow := hconjLower ((1 / 2 : ℝ) • (u + v)) ((1 / 2 : ℝ) • (x + y))
  rw [hu, hv] at hconv
  have hcoe : ((1 / 2 : ℝ) : EReal) * ((inner ℝ x u : ℝ) : EReal) +
        ((1 / 2 : ℝ) : EReal) * ((inner ℝ y v : ℝ) : EReal)
      = (((1 / 2 : ℝ) * inner ℝ x u + (1 / 2 : ℝ) * inner ℝ y v : ℝ) : EReal) := by
    rw [← EReal.coe_mul (1 / 2) (inner ℝ x u), ← EReal.coe_mul (1 / 2) (inner ℝ y v),
      ← EReal.coe_add]
  have hcombined :
      ((inner ℝ ((1 / 2 : ℝ) • (x + y)) ((1 / 2 : ℝ) • (u + v)) : ℝ) : EReal)
        ≤ (((1 / 2 : ℝ) * inner ℝ x u + (1 / 2 : ℝ) * inner ℝ y v : ℝ) : EReal) := by
    calc
      ((inner ℝ ((1 / 2 : ℝ) • (x + y)) ((1 / 2 : ℝ) • (u + v)) : ℝ) : EReal)
          ≤ productConjugate F ((1 / 2 : ℝ) • (u + v), (1 / 2 : ℝ) • (x + y)) := hlow
      _ ≤ ((1 / 2 : ℝ) : EReal) * ((inner ℝ x u : ℝ) : EReal) +
            ((1 / 2 : ℝ) : EReal) * ((inner ℝ y v : ℝ) : EReal) := hconv
      _ = (((1 / 2 : ℝ) * inner ℝ x u + (1 / 2 : ℝ) * inner ℝ y v : ℝ) : EReal) := hcoe
  have hreal := EReal.coe_le_coe_iff.mp hcombined
  rw [real_inner_smul_left, real_inner_smul_right] at hreal
  have h1 : inner ℝ (x + y) (u + v)
      = inner ℝ x u + inner ℝ x v + inner ℝ y u + inner ℝ y v := by
    rw [inner_add_left, inner_add_right, inner_add_right]; ring
  have h2 : inner ℝ (u - v) (x - y)
      = inner ℝ x u + inner ℝ y v - inner ℝ x v - inner ℝ y u := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm u x,
      real_inner_comm u y, real_inner_comm v x, real_inner_comm v y]; ring
  rw [h1] at hreal
  rw [h2]
  nlinarith [hreal]

/-- The quadratic duality witness of Bauschke--Combettes Theorem 20.46(ii)
(the special Corollary 15.15 step): whenever `(z,w)` is monotonically related
to the conjugate contact-set operator of `F`, there are `y v : H` with
`F*(v,y) + G_(z,w)(y,v) ≤ 0`. -/
theorem quadratic_dual_witness
    (F : H × H → EReal)
    (hFconvex : ERealFunction.IsConvex F)
    (hFconjProper : ERealFunction.IsProper (productConjugate F))
    (hconjLower : ∀ u x : H,
      ((inner ℝ x u : ℝ) : EReal) ≤ productConjugate F (u, x))
    (hprimalLower : ∀ x u : H,
      ((inner ℝ x u : ℝ) : EReal) ≤ F (x, u))
    (z w : H)
    (hrel : ∀ y v : H,
      productConjugate F (v, y) = ((inner ℝ y v : ℝ) : EReal) →
        0 ≤ inner ℝ (w - v) (z - y)) :
    ∃ y v : H,
      productConjugate F (v, y) + quadraticG z w (y, v) ≤ (0 : EReal) := by
  sorry

/-- The fibre infimal convolution of two convex extended-real-valued functions
is convex. -/
theorem partial_infconv_convex
    (φ ψ : H × H → EReal)
    (hφconvex : ERealFunction.IsConvex φ)
    (hψconvex : ERealFunction.IsConvex ψ) :
    ERealFunction.IsConvex (partialInfimalConvolution φ ψ) := by
  sorry

/-- The fibrewise sum of the product-space conjugates of two convex
extended-real-valued functions is convex. -/
theorem partial_conjugate_sum_convex
    (φ ψ : H × H → EReal)
    (hφconvex : ERealFunction.IsConvex φ)
    (hψconvex : ERealFunction.IsConvex ψ) :
    ERealFunction.IsConvex (partialConjugateSum φ ψ) := by
  sorry

private theorem fitzpatrickProd_isConvex (A : SetValuedOperator H H) :
    ERealFunction.IsConvex (fitzpatrickProd A) := by
  intro p q a ha0 ha1
  have h := fitzpatrickProd_convex (A := A) p q a (1 - a) ha0 (by linarith) (by ring)
  simpa using h

/-- For maximal monotone `A` and `B`, the fibre convolution of their Fitzpatrick
functions dominates the pairing on the conjugate side.  This is the
Fitzpatrick-specific form of the pairing lower bound consumed by the maximality
criterion `fitzpatrick_contact_maximal`; the corresponding universal statement
fails for arbitrary proper convex functions. -/
theorem fitzpatrick_fibre_pairing_lower
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (u x : H) :
    ((inner ℝ x u : ℝ) : EReal) ≤
      productConjugate (fitzpatrickSumProd A B) (u, x) := by
  sorry

/-- The qualified shared-variable conjugacy restricted to the two Fitzpatrick
functions of maximal monotone operators: under the interior-domain
qualification, the product conjugate of the fibre convolution of `F_A` and
`F_B` is the split sum of the two Fitzpatrick conjugates, equation (25.5) of
the paper's proof.  This is the `F_A`/`F_B` replacement for the refuted
universal conjugacy statement.  The fibre convolution and the split conjugate
sum are recorded as proper, matching the interfaces of
`fitzpatrickSum_conjugate_identity` and `fitzpatrickSumConjugate_proper`; the
properness of the product conjugate itself follows from the identity. -/
theorem fitzpatrick_fibre_conjugate
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hqual : fitzpatrickQualification A B) :
    ERealFunction.IsProper (fitzpatrickSumProd A B) ∧
      ERealFunction.IsProper
        (fun p : H × H ↦ fitzpatrickSumConjugate A B p.1 p.2) ∧
      (∀ u x : H,
        productConjugate (fitzpatrickSumProd A B) (u, x) =
          fitzpatrickSumConjugate A B u x) := by
  sorry

/-- Attainment of the defining infimum of the split Fitzpatrick conjugate:
under the interior-domain qualification, every finite value of
`(F_A ⊞ F_B)*(u,x)` is attained by a split `u = u₁ + u₂`.  This is equation
(25.5)'s exactness clause, restricted to the two Fitzpatrick functions. -/
theorem fitzpatrick_fibre_attainment
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hqual : fitzpatrickQualification A B) :
    ∀ u x : H, productConjugate (fitzpatrickSumProd A B) (u, x) ≠ ⊤ →
      ∃ u₁ u₂ : H, u₁ + u₂ = u ∧
        productConjugate (fitzpatrickSumProd A B) (u, x) =
          fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x := by
  sorry

/-- Corollary 15.8 specialized to the fibre infimal convolution of the two
Fitzpatrick functions: under the interior-domain qualification the
product-space Fitzpatrick sum is convex and proper, and its conjugate is the
split conjugate of the two summands, equation (25.5) of the paper's proof. -/
theorem fitzpatrickSum_conjugate_identity
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hqual : fitzpatrickQualification A B) :
    ERealFunction.IsProper (fitzpatrickSumProd A B) ∧
      ERealFunction.IsConvex (fitzpatrickSumProd A B) ∧
      (∀ u x : H,
        productConjugate (fitzpatrickSumProd A B) (u, x) =
          fitzpatrickSumConjugate A B u x) := by
  have h := fitzpatrick_fibre_conjugate A B hA hB hqual
  have hconv : ERealFunction.IsConvex (fitzpatrickSumProd A B) := by
    have hc := partial_infconv_convex (fitzpatrickProd A) (fitzpatrickProd B)
      (fitzpatrickProd_isConvex A) (fitzpatrickProd_isConvex B)
    simpa [partialInfimalConvolution, fitzpatrickSumProd, fitzpatrickSum, fitzpatrickProd]
      using hc
  exact ⟨h.1, hconv, h.2.2⟩

/-- Theorem 20.46(ii) in the reference form used by Theorem 25.2: a convex
function whose conjugate is proper and which dominates the pairing on both the
primal and conjugate sides has maximal monotone contact-set operator.  No
primal contact hypothesis on the graph is needed, because the operator is
defined by the conjugate contact set. -/
theorem fitzpatrick_contact_maximal
    (F : H × H → EReal)
    (hFconvex : ERealFunction.IsConvex F)
    (hFconjProper : ERealFunction.IsProper (productConjugate F))
    (hconjLower : ∀ u x : H,
      ((inner ℝ x u : ℝ) : EReal) ≤ productConjugate F (u, x))
    (hprimalLower : ∀ x u : H,
      ((inner ℝ x u : ℝ) : EReal) ≤ F (x, u)) :
    IsMaximalMonotone
      (fun x : H =>
        {u : H | productConjugate F (u, x) =
          ((inner ℝ x u : ℝ) : EReal)}) := by
  refine ⟨contact_operator_monotone F (productConjugate_convex F hFconvex) hconjLower, ?_⟩
  intro A' hA' hsub
  rintro ⟨x, u⟩ huA'
  rw [SetValuedOperator.mem_graph_iff] at huA' ⊢
  have hrel : ∀ y v : H,
      productConjugate F (v, y) = ((inner ℝ y v : ℝ) : EReal) →
        0 ≤ inner ℝ (u - v) (x - y) := by
    intro y v hvT
    have hvA' : v ∈ A' y :=
      (SetValuedOperator.mem_graph_iff A' y v).mp
        (hsub ((SetValuedOperator.mem_graph_iff _ y v).mpr hvT))
    exact hA' u huA' v hvA'
  obtain ⟨y, v, hwit⟩ :=
    quadratic_dual_witness F hFconvex hFconjProper hconjLower hprimalLower x u hrel
  have hlow2 : ((inner ℝ y v : ℝ) : EReal) ≤ productConjugate F (v, y) := hconjLower v y
  have hnonneg : (0 : EReal) ≤ quadraticG x u (y, v) + ((inner ℝ y v : ℝ) : EReal) :=
    (quadraticG_lemma x u).2.1 (y, v)
  have heq : productConjugate F (v, y) + quadraticG x u (y, v) = 0 := by
    refine le_antisymm hwit ?_
    calc (0 : EReal) ≤ quadraticG x u (y, v) + ((inner ℝ y v : ℝ) : EReal) := hnonneg
      _ ≤ quadraticG x u (y, v) + productConjugate F (v, y) := add_le_add le_rfl hlow2
      _ = productConjugate F (v, y) + quadraticG x u (y, v) := add_comm _ _
  have hGzero : quadraticG x u (y, v) + ((inner ℝ y v : ℝ) : EReal) = 0 := by
    refine le_antisymm ?_ hnonneg
    calc quadraticG x u (y, v) + ((inner ℝ y v : ℝ) : EReal)
        ≤ quadraticG x u (y, v) + productConjugate F (v, y) := add_le_add le_rfl hlow2
      _ = productConjugate F (v, y) + quadraticG x u (y, v) := add_comm _ _
      _ = 0 := heq
  have hPeq : productConjugate F (v, y) = ((inner ℝ y v : ℝ) : EReal) := by
    calc productConjugate F (v, y)
        = productConjugate F (v, y) + 0 := (add_zero _).symm
      _ = productConjugate F (v, y)
            + (quadraticG x u (y, v) + ((inner ℝ y v : ℝ) : EReal)) := by rw [hGzero]
      _ = (productConjugate F (v, y) + quadraticG x u (y, v))
            + ((inner ℝ y v : ℝ) : EReal) := by rw [add_assoc]
      _ = 0 + ((inner ℝ y v : ℝ) : EReal) := by rw [heq]
      _ = ((inner ℝ y v : ℝ) : EReal) := by rw [zero_add]
  have hzero_rel : y - x = u - v := ((quadraticG_lemma x u).2.2.1 (y, v)).mp hGzero
  have hrel2 : 0 ≤ inner ℝ (y - x) (x - y) := by
    have := hrel y v hPeq
    rwa [← hzero_rel] at this
  have hyx : y = x := by
    have hinner : inner ℝ (y - x) (x - y) = -‖y - x‖ ^ 2 := by
      rw [show x - y = -(y - x) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
    rw [hinner] at hrel2
    have hle : ‖y - x‖ ^ 2 ≤ 0 := by linarith
    have h0 : ‖y - x‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    have hsub0 : y - x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
    exact sub_eq_zero.mp hsub0
  have huv : u = v := by
    have h : u - v = 0 := by
      rw [hzero_rel.symm, hyx]
      abel
    exact sub_eq_zero.mp h
  show productConjugate F (u, x) = ((inner ℝ x u : ℝ) : EReal)
  rw [huv, ← hyx]
  exact hPeq

/-- The split conjugate of the Fitzpatrick functions of two maximal monotone
operators is proper.  This supplies the proper-conjugate hypothesis of the
abstract maximality criterion `fitzpatrick_contact_maximal`.  The interior-domain
qualification `fitzpatrickQualification A B` is required: maximal monotone
operators with disjoint domains make the split conjugate identically `⊤`, so
without it the statement is not derivable. -/
theorem fitzpatrickSumConjugate_proper
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hqual : fitzpatrickQualification A B) :
    ERealFunction.IsProper
      (fun p : H × H ↦ fitzpatrickSumConjugate A B p.1 p.2) := by
  exact (fitzpatrick_fibre_conjugate A B hA hB hqual).2.1

/-- Bauschke--Combettes Corollary 15.8 and equations (25.3)--(25.5): under the
interior-domain qualification the defining infimum of the split conjugate is
exact, i.e. whenever the contact value is finite it is attained by a split
`u = u₁ + u₂`.  Properness, convexity, and the conjugate identity itself are
already recorded in `fitzpatrickSum_conjugate_identity`. -/
theorem qc_infimal_conjugate
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hqual : fitzpatrickQualification A B) :
    ∀ u x : H, productConjugate (fitzpatrickSumProd A B) (u, x) ≠ ⊤ →
      ∃ u₁ u₂ : H, u₁ + u₂ = u ∧
        productConjugate (fitzpatrickSumProd A B) (u, x) =
          fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x := by
  exact fitzpatrick_fibre_attainment A B hA hB hqual

/-- Theorem 25.2, equation (25.6): under the hypotheses of the conjugate
identity, the pairing-contact set of the conjugate of the Fitzpatrick sum is
exactly the graph of `A + B`. -/
theorem fitzpatrickSum_contact_set
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hqual : fitzpatrickQualification A B) :
    ∀ u x : H,
      productConjugate (fitzpatrickSumProd A B) (u, x) =
          ((inner ℝ x u : ℝ) : EReal) ↔
        u ∈ (A + B) x := by
  intro u x
  constructor
  · intro hcontact
    have hne : productConjugate (fitzpatrickSumProd A B) (u, x) ≠ ⊤ := by
      rw [hcontact]
      exact EReal.coe_ne_top _
    obtain ⟨u₁, u₂, hsum, hval⟩ :=
      qc_infimal_conjugate A B hA hB hqual u x hne
    have hsplit : ((inner ℝ x u : ℝ) : EReal) =
        ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := by
      rw [← hsum, inner_add_right, EReal.coe_add]
    have hsumval : fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x =
        ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := by
      rw [← hval, hcontact, hsplit]
    have hAlow : ((inner ℝ x u₁ : ℝ) : EReal) ≤ fitzpatrickConjugate A u₁ x :=
      (fitzpatrick_conjugate_characterization hA x u₁).1
    have hBlow : ((inner ℝ x u₂ : ℝ) : EReal) ≤ fitzpatrickConjugate B u₂ x :=
      (fitzpatrick_conjugate_characterization hB x u₂).1
    have hAle : fitzpatrickConjugate A u₁ x ≤ ((inner ℝ x u₁ : ℝ) : EReal) := by
      have hle : fitzpatrickConjugate A u₁ x + ((inner ℝ x u₂ : ℝ) : EReal) ≤
          ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := by
        calc
          fitzpatrickConjugate A u₁ x + ((inner ℝ x u₂ : ℝ) : EReal)
              ≤ fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x :=
                add_le_add le_rfl hBlow
          _ = ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := hsumval
      exact (EReal.addLECancellable_coe (inner ℝ x u₂)).add_le_add_iff_right.mp hle
    have hBle : fitzpatrickConjugate B u₂ x ≤ ((inner ℝ x u₂ : ℝ) : EReal) := by
      have hle : ((inner ℝ x u₁ : ℝ) : EReal) + fitzpatrickConjugate B u₂ x ≤
          ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := by
        calc
          ((inner ℝ x u₁ : ℝ) : EReal) + fitzpatrickConjugate B u₂ x
              ≤ fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x :=
                add_le_add hAlow le_rfl
          _ = ((inner ℝ x u₁ : ℝ) : EReal) + ((inner ℝ x u₂ : ℝ) : EReal) := hsumval
      exact (EReal.addLECancellable_coe (inner ℝ x u₁)).add_le_add_iff_left.mp hle
    have hAeq : fitzpatrickConjugate A u₁ x = ((inner ℝ x u₁ : ℝ) : EReal) :=
      le_antisymm hAle hAlow
    have hBeq : fitzpatrickConjugate B u₂ x = ((inner ℝ x u₂ : ℝ) : EReal) :=
      le_antisymm hBle hBlow
    have hu₁ : u₁ ∈ A x := (fitzpatrick_conjugate_characterization hA x u₁).2.mp hAeq
    have hu₂ : u₂ ∈ B x := (fitzpatrick_conjugate_characterization hB x u₂).2.mp hBeq
    have hmem : u ∈ A x + B x :=
      Set.mem_add.mpr ⟨u₁, hu₁, u₂, hu₂, hsum⟩
    simpa only [Pi.add_apply] using hmem
  · intro hu
    have hu' : u ∈ A x + B x := by
      simpa only [Pi.add_apply] using hu
    rcases Set.mem_add.mp hu' with ⟨u₁, hu₁, u₂, hu₂, hsum⟩
    rw [← hsum]
    rw [(fitzpatrickSum_conjugate_identity A B hA hB hqual).2.2 (u₁ + u₂) x]
    have hge : ((inner ℝ x (u₁ + u₂) : ℝ) : EReal) ≤
        fitzpatrickSumConjugate A B (u₁ + u₂) x := by
      unfold fitzpatrickSumConjugate
      refine le_iInf ?_
      intro v₁
      refine le_iInf ?_
      intro v₂
      refine le_iInf ?_
      intro hv
      have h1 : ((inner ℝ x v₁ : ℝ) : EReal) ≤ fitzpatrickConjugate A v₁ x :=
        (fitzpatrick_conjugate_characterization hA x v₁).1
      have h2 : ((inner ℝ x v₂ : ℝ) : EReal) ≤ fitzpatrickConjugate B v₂ x :=
        (fitzpatrick_conjugate_characterization hB x v₂).1
      calc
        ((inner ℝ x (u₁ + u₂) : ℝ) : EReal)
            = ((inner ℝ x v₁ : ℝ) : EReal) + ((inner ℝ x v₂ : ℝ) : EReal) := by
              rw [← hv, inner_add_right, EReal.coe_add]
        _ ≤ fitzpatrickConjugate A v₁ x + fitzpatrickConjugate B v₂ x := add_le_add h1 h2
    have hle : fitzpatrickSumConjugate A B (u₁ + u₂) x ≤
        ((inner ℝ x (u₁ + u₂) : ℝ) : EReal) := by
      have hfeas : fitzpatrickSumConjugate A B (u₁ + u₂) x ≤
          fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x := by
        unfold fitzpatrickSumConjugate
        exact iInf_le_of_le u₁ (iInf_le_of_le u₂ (iInf_le_of_le rfl le_rfl))
      have hval : fitzpatrickConjugate A u₁ x + fitzpatrickConjugate B u₂ x =
          ((inner ℝ x (u₁ + u₂) : ℝ) : EReal) := by
        rw [((fitzpatrick_conjugate_characterization hA x u₁).2).mpr hu₁,
          ((fitzpatrick_conjugate_characterization hB x u₂).2).mpr hu₂,
          inner_add_right, ← EReal.coe_add]
      exact hfeas.trans_eq hval
    exact le_antisymm hle hge

/-- The pointwise sum of two monotone set-valued operators is monotone. -/
theorem sum_monotone {A B : SetValuedOperator H H}
    (hA : IsMonotone A) (hB : IsMonotone B) :
    IsMonotone (A + B) := by
  intro x y w hw w' hw'
  rcases hw with ⟨u, hu, v, hv, rfl⟩
  rcases hw' with ⟨u', hu', v', hv', rfl⟩
  rw [show (u + v) - (u' + v') = (u - u') + (v - v') by abel, inner_add_left]
  exact add_nonneg (hA u hu u' hu') (hB v hv v' hv')

/-- Strong--weak sequential closedness of a maximal monotone graph: strong
convergence of the base points together with weak convergence of the values
passes graph membership to the limit. -/
theorem maximal_monotone_graph_strong_weak_closed
    {T : SetValuedOperator H H} (hT : IsMaximalMonotone T)
    (x v : ℕ → H) (x0 v0 : H)
    (hx : Filter.Tendsto x Filter.atTop (𝓝 x0))
    (hv : Filter.Tendsto (fun n => toWeakSpace ℝ H (v n)) Filter.atTop
      (𝓝 (toWeakSpace ℝ H v0)))
    (hmem : ∀ n, v n ∈ T (x n)) : v0 ∈ T x0 := by
  classical
  apply mem_of_monotonically_related_to_graph hT
  intro y w hw
  have hmono : ∀ n : ℕ, 0 ≤ inner ℝ (v n - w) (x n - y) :=
    fun n => hT.1 (v n) (hmem n) w hw
  have hv_inner : ∀ u : H, Filter.Tendsto (fun n : ℕ => inner ℝ (v n) u) Filter.atTop
      (𝓝 (inner ℝ v0 u)) :=
    (weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) v v0).mp hv
  have hvbdd : Bornology.IsBounded (Set.range v) :=
    bounded_range_of_tendsto_weakly hv
  rcases isBounded_iff_forall_norm_le.mp hvbdd with ⟨M, hM⟩
  let N : ℝ := max M 0
  have hNM : ∀ n : ℕ, ‖v n‖ ≤ N := fun n =>
    le_trans (hM (v n) (Set.mem_range_self n)) (le_max_left _ _)
  have hxsub : Filter.Tendsto (fun n : ℕ => x n - x0) Filter.atTop (𝓝 0) := by
    simpa using hx.sub (tendsto_const_nhds (x := x0))
  have hcross : Filter.Tendsto (fun n : ℕ => inner ℝ (v n) (x n - x0)) Filter.atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ n : ℕ, ‖inner ℝ (v n) (x n - x0)‖ ≤ N * ‖x n - x0‖ := by
      intro n
      calc
        ‖inner ℝ (v n) (x n - x0)‖ ≤ ‖v n‖ * ‖x n - x0‖ := norm_inner_le_norm _ _
        _ ≤ N * ‖x n - x0‖ := mul_le_mul_of_nonneg_right (hNM n) (norm_nonneg _)
    have hmajor : Filter.Tendsto (fun n : ℕ => N * ‖x n - x0‖) Filter.atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := N)).mul hxsub.norm
    exact squeeze_zero (fun n => norm_nonneg _) hbound hmajor
  have hxy : Filter.Tendsto (fun n : ℕ => x n - y) Filter.atTop (𝓝 (x0 - y)) :=
    hx.sub (tendsto_const_nhds (x := y))
  have hvx0 : Filter.Tendsto (fun n : ℕ => inner ℝ (v n) (x0 - y)) Filter.atTop
      (𝓝 (inner ℝ v0 (x0 - y))) := hv_inner (x0 - y)
  have hwxy : Filter.Tendsto (fun n : ℕ => inner ℝ w (x n - y)) Filter.atTop
      (𝓝 (inner ℝ w (x0 - y))) :=
    (tendsto_const_nhds (x := w)).inner hxy
  have hmain : Filter.Tendsto (fun n : ℕ => inner ℝ (v n) (x n - y)) Filter.atTop
      (𝓝 (inner ℝ v0 (x0 - y))) := by
    have h := hvx0.add hcross
    convert h using 1
    · ext n
      rw [← inner_add_right]
      congr 1
      abel
    · simp
  have hfull : Filter.Tendsto (fun n : ℕ => inner ℝ (v n - w) (x n - y)) Filter.atTop
      (𝓝 (inner ℝ (v0 - w) (x0 - y))) := by
    simpa [inner_sub_left] using hmain.sub hwxy
  exact ge_of_tendsto hfull (Filter.Eventually.of_forall hmono)

/-- Brézis's interior-domain stability estimate: approximate solutions of
`0 ∈ x + A_mu x + B x`, for `mu ∈ (0, 1]`, remain bounded together with the
Yosida term and a selection from `B`. -/
theorem approximating_solution_bounded
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B)
    (hdom : (interior A.dom ∩ B.dom).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (mu : ℝ) (hmu : 0 < mu), mu ≤ 1 → ∀ x b : H,
        b ∈ B x →
        0 = x + yosidaRegularization A hA mu hmu x + b →
        ‖x‖ ≤ C ∧ ‖yosidaRegularization A hA mu hmu x‖ ≤ C ∧ ‖b‖ ≤ C := by
  sorry

/-- The uniform bounds on approximate solutions `0 = x n + a n + b n` with
`a n ∈ A (x n - mu n • a n)` and `b n ∈ B (x n)`, together with `mu n → 0`,
make the base sequence `x n` Cauchy.  This is the monotonicity computation of
the paper's proof of Corollary 2.7, separated from the limit passage. -/
theorem approximate_solutions_cauchy
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B)
    (mu : ℕ → ℝ) (x a b : ℕ → H) (C : ℝ) (hC : 0 ≤ C)
    (hmu_pos : ∀ n, 0 < mu n)
    (hmu_zero : Filter.Tendsto mu Filter.atTop (𝓝 0))
    (hx_le : ∀ n, ‖x n‖ ≤ C) (ha_le : ∀ n, ‖a n‖ ≤ C) (hb_le : ∀ n, ‖b n‖ ≤ C)
    (ha_mem : ∀ n, a n ∈ A (x n - mu n • a n))
    (hb_mem : ∀ n, b n ∈ B (x n))
    (hsol : ∀ n, 0 = x n + a n + b n) :
    CauchySeq x := by
  classical
  have hkey : ∀ n m : ℕ,
      ‖x n - x m‖ ^ 2 ≤ - inner ℝ (a n - a m) (mu n • a n - mu m • a m) := by
    intro n m
    have hAineq : 0 ≤ inner ℝ (a n - a m)
        ((x n - mu n • a n) - (x m - mu m • a m)) :=
      hA.1 (a n) (ha_mem n) (a m) (ha_mem m)
    have hBineq : 0 ≤ inner ℝ (b n - b m) (x n - x m) :=
      hB.1 (b n) (hb_mem n) (b m) (hb_mem m)
    have hbn : b n = - x n - a n := by
      have h : x n + a n + b n = 0 := (hsol n).symm
      calc
        b n = (x n + a n + b n) - x n - a n := by abel
        _ = 0 - x n - a n := by rw [h]
        _ = - x n - a n := by simp
    have hbm : b m = - x m - a m := by
      have h : x m + a m + b m = 0 := (hsol m).symm
      calc
        b m = (x m + a m + b m) - x m - a m := by abel
        _ = 0 - x m - a m := by rw [h]
        _ = - x m - a m := by simp
    have hJ : (x n - mu n • a n) - (x m - mu m • a m) =
        (x n - x m) - (mu n • a n - mu m • a m) := by abel
    have hA' : 0 ≤ inner ℝ (a n - a m) (x n - x m) -
        inner ℝ (a n - a m) (mu n • a n - mu m • a m) := by
      rw [hJ, inner_sub_right] at hAineq
      exact hAineq
    have hB' : 0 ≤ - ‖x n - x m‖ ^ 2 - inner ℝ (a n - a m) (x n - x m) := by
      have hdb : b n - b m = -(x n - x m) - (a n - a m) := by
        rw [hbn, hbm]
        abel
      rw [hdb, inner_sub_left, inner_neg_left, real_inner_self_eq_norm_sq] at hBineq
      exact hBineq
    have hsum : 0 ≤ (inner ℝ (a n - a m) (x n - x m) -
        inner ℝ (a n - a m) (mu n • a n - mu m • a m)) +
        (- ‖x n - x m‖ ^ 2 - inner ℝ (a n - a m) (x n - x m)) :=
      add_nonneg hA' hB'
    linarith
  have hbound : ∀ n m : ℕ,
      ‖x n - x m‖ ^ 2 ≤ 2 * C ^ 2 * (mu n + mu m) := by
    intro n m
    have h1 : - inner ℝ (a n - a m) (mu n • a n - mu m • a m) ≤
        ‖a n - a m‖ * ‖mu n • a n - mu m • a m‖ := by
      have h := norm_inner_le_norm (𝕜 := ℝ) (a n - a m) (mu n • a n - mu m • a m)
      rw [Real.norm_eq_abs] at h
      exact le_trans (neg_le_abs _) h
    have h2 : ‖a n - a m‖ ≤ 2 * C := by
      calc
        ‖a n - a m‖ ≤ ‖a n‖ + ‖a m‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (ha_le n) (ha_le m)
        _ = 2 * C := by ring
    have h3 : ‖mu n • a n - mu m • a m‖ ≤ C * mu n + C * mu m := by
      calc
        ‖mu n • a n - mu m • a m‖ ≤ ‖mu n • a n‖ + ‖mu m • a m‖ := norm_sub_le _ _
        _ = mu n * ‖a n‖ + mu m * ‖a m‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (hmu_pos n), abs_of_pos (hmu_pos m)]
        _ ≤ C * mu n + C * mu m := by
          have h1 : mu n * ‖a n‖ ≤ mu n * C :=
            mul_le_mul_of_nonneg_left (ha_le n) (hmu_pos n).le
          have h2 : mu m * ‖a m‖ ≤ mu m * C :=
            mul_le_mul_of_nonneg_left (ha_le m) (hmu_pos m).le
          linarith
    calc
      ‖x n - x m‖ ^ 2 ≤
          - inner ℝ (a n - a m) (mu n • a n - mu m • a m) := hkey n m
      _ ≤ ‖a n - a m‖ * ‖mu n • a n - mu m • a m‖ := h1
      _ ≤ (2 * C) * (C * mu n + C * mu m) :=
          mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = 2 * C ^ 2 * (mu n + mu m) := by ring
  rw [Metric.cauchySeq_iff]
  intro ε hε
  by_cases hC0 : C = 0
  · refine ⟨0, ?_⟩
    intro m hm n hn
    have hxm : x m = 0 := by
      have : ‖x m‖ ≤ 0 := by simpa [hC0] using hx_le m
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    have hxn : x n = 0 := by
      have : ‖x n‖ ≤ 0 := by simpa [hC0] using hx_le n
      exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    have hdist : dist (x m) (x n) = 0 := by simp [hxm, hxn]
    rw [hdist]
    exact hε
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hCne : C ≠ 0 := ne_of_gt hCpos
    let δ : ℝ := ε ^ 2 / (8 * C ^ 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hev : ∀ᶠ n in Filter.atTop, mu n < δ :=
      hmu_zero.eventually (Iio_mem_nhds hδpos)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hmn : ‖x n - x m‖ ^ 2 < ε ^ 2 := by
      have h := hbound n m
      have hmun := hN n hn
      have hmum := hN m hm
      have hmu_sum : mu n + mu m < δ + δ := add_lt_add hmun hmum
      have hmul : 2 * C ^ 2 * (mu n + mu m) < 2 * C ^ 2 * (δ + δ) :=
        mul_lt_mul_of_pos_left hmu_sum (by positivity)
      have hδval : 2 * C ^ 2 * (δ + δ) = ε ^ 2 / 2 := by
        dsimp [δ]
        field_simp
        ring
      nlinarith [h, hmul, hδval, hε]
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [norm_nonneg (x n - x m), hmn, hε]

/-- Along any sequence `mu_n → 0⁺` of approximate solutions in the sense of
`approximating_solution_bounded`, a weakly convergent subsequence has a limit
`x` which is an exact zero of `x + A x + B x`. -/
theorem zero_membership_in_limit
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B)
    (hdom : (interior A.dom ∩ B.dom).Nonempty)
    (mu : ℕ → ℝ) (x b : ℕ → H)
    (hmu_pos : ∀ n, 0 < mu n) (hmu_le_one : ∀ n, mu n ≤ 1)
    (hmu_zero : Filter.Tendsto mu Filter.atTop (𝓝 0))
    (hb : ∀ n, b n ∈ B (x n))
    (hsol : ∀ n,
      0 = x n + yosidaRegularization A hA (mu n) (hmu_pos n) (x n) + b n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x0 : H,
      Filter.Tendsto (fun n => toWeakSpace ℝ H (x (φ n))) Filter.atTop
          (𝓝 (toWeakSpace ℝ H x0)) ∧
        ∃ a0 ∈ A x0, ∃ b0 ∈ B x0, 0 = x0 + a0 + b0 := by
  classical
  obtain ⟨C, hC, hbound⟩ := approximating_solution_bounded A B hA hB hdom
  let a : ℕ → H := fun n => yosidaRegularization A hA (mu n) (hmu_pos n) (x n)
  have hx_le : ∀ n, ‖x n‖ ≤ C := by
    intro n
    exact (hbound (mu n) (hmu_pos n) (hmu_le_one n) (x n) (b n) (hb n) (hsol n)).1
  have ha_le : ∀ n, ‖a n‖ ≤ C := by
    intro n
    exact (hbound (mu n) (hmu_pos n) (hmu_le_one n) (x n) (b n) (hb n) (hsol n)).2.1
  have hb_le : ∀ n, ‖b n‖ ≤ C := by
    intro n
    exact (hbound (mu n) (hmu_pos n) (hmu_le_one n) (x n) (b n) (hb n) (hsol n)).2.2
  have ha_mem : ∀ n, a n ∈ A (x n - mu n • a n) := by
    intro n
    simpa [a] using yosida_selection_mem_original_rem6 A hA (mu n) (hmu_pos n) (x n)
  have hsol' : ∀ n, 0 = x n + a n + b n := by
    intro n
    simpa [a] using hsol n
  have hcauchy : CauchySeq x :=
    approximate_solutions_cauchy A B hA hB mu x a b C hC hmu_pos hmu_zero
      hx_le ha_le hb_le ha_mem hb hsol'
  obtain ⟨x0, hx0⟩ := cauchySeq_tendsto_of_complete hcauchy
  have ha_bdd : Bornology.IsBounded (Set.range a) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro z ⟨n, hn⟩
    rw [← hn]
    exact ha_le n
  obtain ⟨a0, ψ, hψ, haweak⟩ :=
    bounded_sequence_has_weakly_convergent_subsequence a ha_bdd
  have hxψ : Filter.Tendsto (fun k => x (ψ k)) Filter.atTop (𝓝 x0) :=
    hx0.comp hψ.tendsto_atTop
  have hxψ_weak : Filter.Tendsto (fun k => toWeakSpace ℝ H (x (ψ k))) Filter.atTop
      (𝓝 (toWeakSpace ℝ H x0)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto x0).comp hxψ
  have hsmul_tendsto : Filter.Tendsto (fun k => mu (ψ k) • a (ψ k)) Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound' : ∀ k, ‖mu (ψ k) • a (ψ k)‖ ≤ C * mu (ψ k) := by
      intro k
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hmu_pos (ψ k))]
      calc
        mu (ψ k) * ‖a (ψ k)‖ ≤ mu (ψ k) * C :=
          mul_le_mul_of_nonneg_left (ha_le (ψ k)) (hmu_pos (ψ k)).le
        _ = C * mu (ψ k) := by ring
    have hmajor : Filter.Tendsto (fun k => C * mu (ψ k)) Filter.atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := C)).mul (hmu_zero.comp hψ.tendsto_atTop)
    exact squeeze_zero (fun k => norm_nonneg _) hbound' hmajor
  have hJ : Filter.Tendsto (fun k => x (ψ k) - mu (ψ k) • a (ψ k)) Filter.atTop (𝓝 x0) := by
    simpa using hxψ.sub hsmul_tendsto
  have ha0A : a0 ∈ A x0 :=
    maximal_monotone_graph_strong_weak_closed hA
      (fun k => x (ψ k) - mu (ψ k) • a (ψ k)) (fun k => a (ψ k)) x0 a0 hJ haweak
      (fun k => ha_mem (ψ k))
  let b0 : H := -x0 - a0
  have hb_eq : ∀ n, b n = - x n - a n := by
    intro n
    have h : x n + a n + b n = 0 := (hsol' n).symm
    calc
      b n = (x n + a n + b n) - x n - a n := by abel
      _ = 0 - x n - a n := by rw [h]
      _ = - x n - a n := by simp
  have hbweak : Filter.Tendsto (fun k => toWeakSpace ℝ H (b (ψ k))) Filter.atTop
      (𝓝 (toWeakSpace ℝ H b0)) := by
    have h := hxψ_weak.neg.sub haweak
    simpa [hb_eq, b0, map_sub, map_neg] using h
  have hb0B : b0 ∈ B x0 :=
    maximal_monotone_graph_strong_weak_closed hB (fun k => x (ψ k))
      (fun k => b (ψ k)) x0 b0 hxψ hbweak (fun k => hb (ψ k))
  refine ⟨ψ, hψ, x0, hxψ_weak, a0, ha0A, b0, hb0B, ?_⟩
  dsimp [b0]
  abel

/-- Homogeneous solvability of the inclusion `0 ∈ x + A x + B x` for a pair of
maximal monotone operators satisfying Brézis's interior-domain qualification.

For every `mu > 0` the Yosida approximation `A_mu` is a single-valued,
full-domain, monotone, `1 / mu`-Lipschitz perturbation of `B`, so
`maximal_monotone_add_of_monotone_lipschitz` and Minty's surjectivity give an
approximate solution `0 = x + A_mu x + b`.  `zero_membership_in_limit` passes to
the limit along `mu_n = 1 / (n + 1)`. -/
private theorem exists_zero_mem_sum
    (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hdom : (interior A.dom ∩ B.dom).Nonempty) :
    ∃ x : H, ∃ a ∈ A x, ∃ b ∈ B x, 0 = x + a + b := by
  classical
  have hexists : ∀ (mu : ℝ) (hmu : 0 < mu),
      ∃ x : H, ∃ b ∈ B x,
        0 = x + yosidaRegularization A hA mu hmu x + b := by
    intro mu hmu
    let Y : H → H := yosidaRegularization A hA mu hmu
    let P : SetValuedOperator H H := fun z => {Y z}
    have hPmono : IsMonotone P := by
      intro x y u hu v hv
      have hux : u = Y x := by simpa [P] using hu
      have hvy : v = Y y := by simpa [P] using hv
      rw [hux, hvy]
      have hc := (yosidaRegularization_properties A hA mu hmu).1 x y
      have hswap :
          inner ℝ (Y x - Y y) (x - y) = inner ℝ (Y y - Y x) (y - x) := by
        rw [show Y x - Y y = -(Y y - Y x) by abel,
          show x - y = -(y - x) by abel, inner_neg_left, inner_neg_right, neg_neg]
      rw [hswap]
      exact le_trans (mul_nonneg hmu.le (sq_nonneg _)) hc
    have hPdom : P.dom = Set.univ := by
      ext z
      simp [SetValuedOperator.dom, P]
    have hPlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y u v, u ∈ P x → v ∈ P y →
        ‖u - v‖ ≤ L * ‖x - y‖ := by
      refine ⟨1 / mu, by positivity, ?_⟩
      intro x y u v hu hv
      have hux : u = Y x := by simpa [P] using hu
      have hvy : v = Y y := by simpa [P] using hv
      rw [hux, hvy]
      simpa [Y, norm_sub_rev] using (yosidaRegularization_properties A hA mu hmu).2.1 x y
    have hmax := maximal_monotone_add_of_monotone_lipschitz B P hB hPmono hPdom hPlip
    obtain ⟨x, u, hu, hxu⟩ := minty_surjective_of_maximal_monotone hmax 0
    rcases hu with ⟨b, hb, p, hp, hbp⟩
    have hpY : p = Y x := by simpa [P] using hp
    refine ⟨x, b, hb, ?_⟩
    have hxub : 0 = x + (b + Y x) := by
      rw [← hbp, hpY] at hxu
      exact hxu
    have : x + Y x + b = 0 := by
      rw [show x + Y x + b = x + (b + Y x) by abel]
      exact hxub.symm
    simpa [Y] using this.symm
  let mu : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hmu_pos : ∀ n, 0 < mu n := by
    intro n
    simp only [mu]
    positivity
  have hmu_le_one : ∀ n, mu n ≤ 1 := by
    intro n
    simp only [mu]
    apply inv_le_one_of_one_le₀
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmu_zero : Filter.Tendsto mu Filter.atTop (𝓝 0) := by
    simpa [mu, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  choose x b hb hsol using fun n => hexists (mu n) (hmu_pos n)
  obtain ⟨φ, hφ, x0, hweak, a0, ha0, b0, hb0, hzero⟩ :=
    zero_membership_in_limit A B hA hB hdom mu x b hmu_pos hmu_le_one hmu_zero hb hsol
  exact ⟨x0, a0, ha0, b0, hb0, hzero⟩

/-- If `A` and `B` are maximal monotone and `int(dom A) ∩ dom B` is nonempty,
then `A + B` is maximal monotone (Brézis Corollary 2.7). -/
theorem sum_maximal_monotone (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hdom : (interior A.dom ∩ B.dom).Nonempty) :
    IsMaximalMonotone (A + B) := by
  refine (minty_surjective_iff_maximal_monotone (sum_monotone hA.1 hB.1)).2 ?_
  intro y
  let Ay : SetValuedOperator H H := fun z => {w : H | ∃ v, v ∈ A z ∧ w = v - y}
  have hAy : IsMaximalMonotone Ay := by
    simpa [Ay] using translate_sub_const_maximal_monotone hA y
  have hdomAy : (interior Ay.dom ∩ B.dom).Nonempty := by
    rcases hdom with ⟨p, hpint, hpB⟩
    refine ⟨p, ?_, hpB⟩
    have hdom_eq : Ay.dom = A.dom := by
      ext z
      rw [SetValuedOperator.mem_dom_iff, SetValuedOperator.mem_dom_iff]
      constructor
      · rintro ⟨w, v, hv, _⟩
        exact ⟨v, hv⟩
      · rintro ⟨v, hv⟩
        exact ⟨v - y, v, hv, rfl⟩
    rwa [hdom_eq]
  obtain ⟨x0, a0, ha0, b0, hb0, hzero⟩ := exists_zero_mem_sum Ay B hAy hB hdomAy
  rcases ha0 with ⟨a, ha, haeq⟩
  rw [haeq] at hzero
  refine ⟨x0, a + b0, ?_, ?_⟩
  · change a + b0 ∈ A x0 + B x0
    exact Set.mem_add.mpr ⟨a, ha, b0, hb0, rfl⟩
  · have hx0 : x0 + (a - y) + b0 = 0 := hzero.symm
    calc y = (x0 + (a - y) + b0) + y := by rw [hx0]; simp
      _ = x0 + (a + b0) := by abel
