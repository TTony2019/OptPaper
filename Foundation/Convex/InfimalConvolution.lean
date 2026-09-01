import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Infimal convolution and infimal postcomposition

The infimal convolution `f □ g` of two extended-real-valued functions and the
infimal postcomposition `L ▷ f` of a function along a map, together with the
exactness predicates recording when the defining infima are attained.
-/

open Set

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Definition_12_1 -/

variable [AddGroup H]

/-- Definition 12.1 (1): the infimal convolution of two `]-∞,+∞]`-valued functions. -/
noncomputable def infimalConvolution (f g : H → EReal) : H → EReal :=
  fun x ↦ ⨅ y : H, f y + g (x - y)

infixl:70 " □ " => fun f g x ↦
  ERealFunction.infimalConvolution
    (fun y ↦ (f y : EReal))
    (fun y ↦ (g y : EReal))
    x

/-- The value of the infimal convolution at `x` is the infimum of the translated sums
`y ↦ f y + g (x - y)`. -/
theorem infimalConvolution_apply (f g : H → EReal) (x : H) :
    (f □ g) x = ⨅ y : H, f y + g (x - y) := rfl

namespace infimalConvolution

/-- Definition 12.1 (2): infimal convolution is exact at `x` when some point `y` attains the
defining infimum of `(f □ g) x`. -/
def ExactAt (f g : H → Set.Ioi (⊥ : EReal)) (x : H) : Prop :=
  ∃ y : H, (f □ g) x = (f y : EReal) + (g (x - y) : EReal)

/-- Definition 12.1 (3): infimal convolution is exact when it is exact at every point of its
domain. The project records exactness by this predicate rather than by a second infimal-convolution
operator. -/
def Exact (f g : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ ⦃x : H⦄, x ∈ dom (f □ g) → ExactAt f g x

end infimalConvolution

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Definition_12_34 -/

variable [AddGroup H]

/-- The infimal postcomposition of `f` along `L` is the infimum of the values of `f` on each
fiber of `L`. -/
noncomputable def infimalPostcomposition (L : H → K) (f : H → EReal) : K → EReal :=
  fun y ↦ sInf (f '' (L ⁻¹' {y}))

infixr:70 " ▷ " => fun L f y ↦
  ERealFunction.infimalPostcomposition L (fun x ↦ (f x : EReal)) y

/-- The value of `L ▷ f` at `y` is the infimum of the values of `f` on the fiber `L ⁻¹' {y}`. -/
theorem infimalPostcomposition_apply {α : Type*} [CoeTC α EReal]
    (L : H → K) (f : H → α) (y : K) :
    (L ▷ f) y = sInf ((fun x ↦ (f x : EReal)) '' (L ⁻¹' {y})) :=
  rfl

namespace infimalPostcomposition

/-- Exactness at `y` means that `(L ▷ f) y` is attained on the fiber `L ⁻¹' {y}` by a finite value
of `f`. -/
def ExactAt (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) : Prop :=
  ∃ x : H, x ∈ effectiveDomain f ∧ L x = y ∧ (L ▷ f) y = (f x : EReal)

/-- Exactness at `y` is equivalently membership of `y` in `dom (L ▷ f)` together with a point of
the fiber `L ⁻¹' {y}` attaining `(L ▷ f) y`. -/
theorem exactAt_iff_exists_eq (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) :
    ExactAt L f y ↔ y ∈ dom (L ▷ f) ∧ ∃ x : H, L x = y ∧ (L ▷ f) y = (f x : EReal) := by
  constructor
  · rintro ⟨x, hxdom, hxLy, hxy⟩
    refine ⟨?_, ⟨x, hxLy, hxy⟩⟩
    rw [mem_dom_iff, hxy]
    simpa [effectiveDomain] using hxdom
  · rintro ⟨hy, x, hxLy, hxy⟩
    refine ⟨x, ?_, hxLy, hxy⟩
    rw [mem_dom_iff] at hy
    simpa [effectiveDomain] using (show (f x : EReal) < ⊤ by rwa [hxy] at hy)

/-- Exactness at `y` is equivalently attainment of the fiberwise infimum defining `(L ▷ f) y` by
a point of the fiber where `f` is finite. -/
theorem exactAt_iff_exists_isMinOn (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) (y : K) :
    ExactAt L f y ↔
      ∃ x ∈ L ⁻¹' {y}, x ∈ effectiveDomain f ∧ IsMinOn f.asEReal (L ⁻¹' {y}) x := by
  let fiber : Set H := L ⁻¹' {y}
  have happly : (L ▷ f) y = sInf (f.asEReal '' fiber) := by
    simpa [fiber] using (infimalPostcomposition_apply L f y)
  constructor
  · rintro ⟨x, hxdom, hxLy, hxy⟩
    have hxmem : x ∈ fiber := by
      simpa [fiber] using hxLy
    have hsInf : (f x : EReal) = sInf (f.asEReal '' fiber) := by
      rw [← hxy, happly]
    refine ⟨x, hxmem, hxdom, ?_⟩
    rw [isMinOn_iff]
    intro z hzmem
    have hsInf_le : sInf (f.asEReal '' fiber) ≤ f.asEReal z :=
      (isGLB_sInf_image f.asEReal fiber).1 ⟨z, hzmem, rfl⟩
    simpa [hsInf] using hsInf_le
  · rintro ⟨x, hxmem, hxdom, hmin⟩
    refine ⟨x, hxdom, ?_, ?_⟩
    · simpa [fiber] using hxmem
    · exact happly.trans (eq_sInf_image_of_isMinOn hxmem hmin).symm

/-- Exactness of `L ▷ f` means exactness at every point of the domain of the infimal
postcomposition. -/
def Exact (L : H → K) (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ ⦃y : K⦄, y ∈ dom (L ▷ f) → ExactAt L f y

end infimalPostcomposition

end ERealFunction
