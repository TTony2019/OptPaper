import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hilbert Basic

Hilbert-space examples, inner-product identities, weighted norm identities, hyperplanes, and finite-dimensional matrix models.
-/

open _root_.Matrix
open scoped BigOperators
open Matrix WithLp
open scoped Matrix.Norms.Frobenius
open Matrix
open MeasureTheory
open MeasureTheory.L2
open scoped MeasureTheory InnerProductSpace
open scoped MeasureTheory InnerProductSpace ProbabilityTheory
open MeasureTheory intervalIntegral
open scoped InnerProductSpace
open EuclideanGeometry
open scoped BigOperators InnerProductSpace
open Matrix OrderDual Tuple

/-! Source item: Chap02/Text_2_0_2 -/
universe u

/-- The identity operator sends every element to itself. -/
theorem identity_operator_apply {𝓗 : Type u} (x : 𝓗) :
    id x = x := rfl

/-! Source item: Chap02/Text_2_0_3 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Text 2.0.3: a vector is orthogonal to a subset of a real inner product space if and only if it
is orthogonal to the linear span of that subset. -/
theorem mem_orthogonalComplement_iff {C : Set H} {u : H} :
    u ∈ (Submodule.span ℝ C)ᗮ ↔ ∀ x ∈ C, inner ℝ x u = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hu x hx
    exact hu x (Submodule.subset_span hx)
  · intro hu x hx
    refine Submodule.span_induction
      (fun x hx ↦ hu x hx)
      (by simp)
      (fun x y _ _ hx hy ↦ by simp [inner_add_left, hx, hy])
      (fun a x _ hx ↦ by simp [inner_smul_left, hx])
      hx

/-! Source item: Chap02/Example_2_2 -/


variable {I : Type u}

/-- The standard unit vector is `1` at its defining index and `0` at every other coordinate. -/
theorem standard_unit_vector_apply [DecidableEq I] (i j : I) :
    ((lp.single 2 i (1 : ℝ) : lp (fun _ : I ↦ ℝ) 2) j = if j = i then 1 else 0) := by
  simp [lp.single_apply, Pi.single_apply, eq_comm]

-- Proof sketch: apply the canonical formula `lp.inner_eq_tsum` for the Hilbert sum `ℓ²(I, ℝ)` and
-- simplify the real inner product on each coordinate to multiplication.
/-- In real `ℓ²(I)`, the inner product is the sum of the pointwise products of the coordinates. -/
theorem l2_inner_eq_tsum_mul (ξ η : lp (fun _ : I ↦ ℝ) 2) :
    inner ℝ ξ η = ∑' j, ξ j * η j := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun j ↦ ?_
  rw [mul_comm]
  rfl

/-! Source item: Chap02/Example_2_3 -/

/-- Example 2.3: under the canonical identification
`ℓ²(Fin N, ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)`, an `ℓ²` vector and its Euclidean coordinate
function have the same entries. -/
theorem lpPiLpₗᵢ_fin_real_apply (N : ℕ) (x : lp (fun _ : Fin N ↦ ℝ) 2) :
    ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ x : EuclideanSpace ℝ (Fin N)) : Fin N → ℝ) = x :=
  rfl

/-- The inverse of the canonical identification `ℓ²(Fin N, ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)` is
also coordinatewise the identity. -/
theorem lpPiLpₗᵢ_fin_real_symm_apply (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) :
    ((((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x : lp (fun _ : Fin N ↦ ℝ) 2) :
      Fin N → ℝ)) = x :=
  rfl

/-! Source item: Chap02/Example_2_4 -/
noncomputable section


/-- Example 2.4: after identifying real `M × N` matrices with an iterated `L²` space, the inner
product is given by the trace formula `trace (Aᵀ B)`. -/
theorem matrixToHilbert_inner_eq_trace_transpose_mul
    (M N : ℕ) (A B : Matrix (Fin M) (Fin N) ℝ) :
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (fun j ↦ A i j)))
      (toLp 2 (fun i ↦ toLp 2 (fun j ↦ B i j))) = Matrix.trace (A.transpose * B) := by
  calc
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (fun j ↦ A i j)))
        (toLp 2 (fun i ↦ toLp 2 (fun j ↦ B i j)))
      = Matrix.trace (B * A.transpose) := by
          rw [PiLp.inner_apply, Matrix.trace]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using inner_matrix_row_row A B i i
    _ = Matrix.trace (A.transpose * B) := Matrix.trace_mul_comm B A.transpose

/-- Example 2.4: the canonical matrix norm on `Matrix (Fin M) (Fin N) ℝ` is the Frobenius norm,
written entrywise as the square root of the sum of the squares. -/
theorem matrixToHilbert_norm_eq_frobenius_formula
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) := by
  simp [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, sq]

end

/-! Source item: Chap02/Example_2_5 -/

/-- Example 2.5: for a strictly positive integer `N`, the real vector subspace of symmetric
`N × N` matrices is the canonical self-adjoint submodule of `Matrix (Fin N) (Fin N) ℝ`;
equivalently, membership is the library predicate `A.IsSymm`. -/
@[simp] theorem mem_selfAdjoint_submodule_iff_isSymm
    {N : ℕ+} {A : Matrix (Fin N) (Fin N) ℝ} :
    A ∈ selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ) ↔ A.IsSymm := by
  change IsSelfAdjoint A ↔ A.IsSymm
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose, Matrix.IsSymm, Matrix.conjTranspose]
  constructor <;> intro h <;> simpa using h

/-- Example 2.5 in textbook coordinates: membership in the canonical self-adjoint submodule is the
condition `Aᵀ = A`. -/
theorem mem_selfAdjoint_submodule_iff
    {N : ℕ+} {A : Matrix (Fin N) (Fin N) ℝ} :
    A ∈ selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ) ↔ Aᵀ = A := by
  rw [mem_selfAdjoint_submodule_iff_isSymm, Matrix.IsSymm]

/-! Source item: Chap02/Example_2_7 -/


variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/- The textbook real-valued `L^p(\Omega,\mathcal{F},\mu)` is the canonical mathlib space
`MeasureTheory.Lp ℝ p μ`. -/
#check MeasureTheory.Lp

-- Proof sketch: rewrite the canonical `L²` inner product using `MeasureTheory.L2.inner_def` and
-- simplify the real pointwise inner product `⟪f x, g x⟫_ℝ` to the product `f x * g x`.
/-- Example 2.7: for a real measure space, the canonical inner product on `L²` is the integral of
the pointwise product. -/
theorem real_l2_inner_eq_integral_mul (f g : α →₂[μ] ℝ) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [inner_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  change g x * star (f x) = f x * g x
  simp [mul_comm]

/-! Source item: Chap02/Example_2_8 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {T : ℝ}

/- Example 2.8: the textbook interval space `L²([0,T]; H)` is the canonical mathlib `L²` space
for the restricted Lebesgue measure on `[0, T]`. -/
#check (ℝ →₂[volume.restrict (Set.Icc 0 T)] H)

-- Proof sketch: specialize `MeasureTheory.L2.inner_def` to the restricted Lebesgue measure
-- `volume.restrict (Set.Icc 0 T)` and rewrite the resulting integral as the set integral over
-- `[0, T]`.
/-- Example 2.8: for a real inner product space `H` and `T > 0`, the interval space
`L²([0,T]; H)` carries the canonical `L²` inner product given by integrating the pointwise inner
product over `[0,T]`. In particular, this applies to the textbook separable real Hilbert-space
setting, and specializing to `H = ℝ` recovers the usual real-valued space `L²([0,T])`. -/
theorem l2_interval_inner_eq_integral_inner (_hT : 0 < T)
    (x y : ℝ →₂[volume.restrict (Set.Icc 0 T)] H) :
    ⟪x, y⟫_ℝ = ∫ t in Set.Icc 0 T, ⟪x t, y t⟫_ℝ ∂volume := by
  simpa using (inner_def x y)

/-! Source item: Chap02/Example_2_9 -/


variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

-- Proof sketch: rewrite the canonical `L²` inner product with `L2.inner_def`, expand the
-- expectation notation `P[·]`, and simplify the real pointwise inner product `⟪X ω, Y ω⟫_ℝ`
-- to the product `X ω * Y ω`.
/-- Example 2.9: on a probability space, the canonical inner product on real `L²(P)` is the
expected value of the pointwise product `XY`. -/
theorem real_probability_l2_inner_eq_expectation_mul [IsProbabilityMeasure P]
    (X Y : Ω →₂[P] ℝ) :
    ⟪X, Y⟫_ℝ = P[fun ω ↦ X ω * Y ω] := by
  rw [inner_def]
  change ∫ ω, ⟪X ω, Y ω⟫_ℝ ∂P = ∫ ω, X ω * Y ω ∂P
  refine integral_congr_ae ?_
  filter_upwards with ω
  change Y ω * star (X ω) = X ω * Y ω
  simp [mul_comm]

/-! Source item: Chap02/Example_2_10 -/

noncomputable section

section IntegralCriterion

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {T : Set.Ioi (0 : ℝ)}
/-- An `L²` derivative witness for a function `x : [0,T] → H` is an `L²([0,T]; H)` class whose
representatives satisfy the textbook integral criterion from Example 2.10. -/
def HasL2DerivativeOnIcc (T : Set.Ioi (0 : ℝ)) (x : Set.Icc (0 : ℝ) (T : ℝ) → H)
    (x' : MeasureTheory.Lp H 2 (volume : Measure (Set.Icc (0 : ℝ) (T : ℝ)))) : Prop :=
  ∃ g : Set.Icc (0 : ℝ) (T : ℝ) → H,
    ∃ hg : MemLp g 2 (volume : Measure (Set.Icc (0 : ℝ) (T : ℝ))),
    hg.toLp g = x' ∧
      ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
        x t = x ⟨0, ⟨le_rfl, le_of_lt T.2⟩⟩ + ∫ s in 0..(t : ℝ), Set.IccExtend
          (le_of_lt T.2) g s

end IntegralCriterion

section Sobolev

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {T : Set.Ioi (0 : ℝ)}

/-- Example 2.10: `W^{1,2}([0,T]; H)` consists of a continuous function on `[0,T]` together with a
canonical `L²([0,T]; H)` derivative class satisfying the textbook integral criterion through some
`L²` representative of that class. -/
structure SobolevW12 (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : Set.Ioi (0 : ℝ)) where
  toContinuousMap : C(Set.Icc (0 : ℝ) (T : ℝ), H)
  deriv : MeasureTheory.Lp H 2 (volume : Measure (Set.Icc (0 : ℝ) (T : ℝ)))
  hasL2DerivativeOnIcc : HasL2DerivativeOnIcc T toContinuousMap deriv

local notation "I" => Set.Icc (0 : ℝ) (T : ℝ)

local instance : IsFiniteMeasure (volume : Measure I) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

namespace SobolevW12

/-- The canonical `L²([0,T]; H)` class of the continuous part of a Sobolev function. -/
abbrev toLp (x : SobolevW12 H T) :
    MeasureTheory.Lp H 2 (volume : Measure I) :=
  x.toContinuousMap.toLp 2 (volume : Measure I) ℝ

/-- The integral criterion in Example 2.10 is witnessed by some representative of the derivative
class. -/
theorem exists_eq_leftEndpoint_add_intervalIntegral (x : SobolevW12 H T) :
    ∃ g : I → H, ∃ hg : MemLp g 2 (volume : Measure I),
      hg.toLp g = x.deriv ∧
        ∀ t : I,
          x.toContinuousMap t = x.toContinuousMap ⟨0, ⟨le_rfl, le_of_lt T.2⟩⟩ +
            ∫ s in 0..(t : ℝ), Set.IccExtend (le_of_lt T.2) g s := by
  simpa [HasL2DerivativeOnIcc] using x.hasL2DerivativeOnIcc

end SobolevW12

end Sobolev

section SobolevInner

attribute [local instance] Measure.Subtype.measureSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {T : Set.Ioi (0 : ℝ)}

local notation "I" => Set.Icc (0 : ℝ) (T : ℝ)

local instance : IsFiniteMeasure (volume : Measure I) := by
  refine ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

namespace SobolevW12

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Example 2.10 equips `W^{1,2}([0,T]; H)` with the scalar product given by the sum of the
canonical `L²` inner products of the function part and of the derivative class. -/
instance : Inner ℝ (SobolevW12 H T) where
  inner x y := inner ℝ x.toLp y.toLp + inner ℝ x.deriv y.deriv

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The textbook scalar product is the sum of the canonical `L²` inner products of the continuous
part and of the derivative class. -/
theorem inner_eq_L2_inner_add_L2_inner (x y : SobolevW12 H T) :
    inner ℝ x y = inner ℝ x.toLp y.toLp + inner ℝ x.deriv y.deriv :=
  rfl

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The continuous part contributes the integral of the pointwise inner product over `[0,T]`. -/
theorem inner_eq_integral_add_L2_inner (x y : SobolevW12 H T) :
    inner ℝ x y =
      (∫ t : I, inner ℝ (x.toContinuousMap t) (y.toContinuousMap t)) +
        inner ℝ x.deriv y.deriv := by
  rw [inner_eq_L2_inner_add_L2_inner, L2.inner_def]
  congr 1
  apply MeasureTheory.integral_congr_ae
  have hx :
      ((x.toLp : MeasureTheory.Lp H 2 (volume : Measure I)) : I → H) =ᵐ[volume] x.toContinuousMap :=
    by
    exact AEEqFun.coeFn_mk x.toContinuousMap _
  have hy :
      ((y.toLp : MeasureTheory.Lp H 2 (volume : Measure I)) : I → H) =ᵐ[volume] y.toContinuousMap :=
    by
    exact AEEqFun.coeFn_mk y.toContinuousMap _
  filter_upwards [hx, hy] with t hxt hyt
  simpa using congrArg₂ (inner ℝ) hxt hyt

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The textbook scalar product is the sum of the pointwise inner-product integrals of the
continuous part and of the derivative class. -/
theorem inner_eq_integral_add_derivative (x y : SobolevW12 H T) :
    inner ℝ x y =
      (∫ t : I, inner ℝ (x.toContinuousMap t) (y.toContinuousMap t)) +
        ∫ t : I, inner ℝ (x.deriv t) (y.deriv t) := by
  rw [inner_eq_integral_add_L2_inner, L2.inner_def]

end SobolevW12

end SobolevInner

end

/-! Source item: Chap02/Example_2_19 -/
noncomputable section


universe v

private lemma toEuclideanLin_apply_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ ≤ ‖A‖ * ‖x‖ := by
  have hmulVec :
      ‖replicateCol (Fin 1) (A.mulVec x.ofLp)‖ = ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ :=
    frobenius_norm_replicateCol (ι := Fin 1) (v := A.mulVec x.ofLp)
  have hx :
      ‖replicateCol (Fin 1) x.ofLp‖ = ‖WithLp.toLp 2 x.ofLp‖ :=
    frobenius_norm_replicateCol (ι := Fin 1) (v := x.ofLp)
  calc
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ = ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ := by
      change ‖A.toEuclideanLin x‖ = _
      rfl
    _ = ‖replicateCol (Fin 1) (A.mulVec x.ofLp)‖ := by
      symm
      exact hmulVec
    _ = ‖A * replicateCol (Fin 1) x.ofLp‖ := by
      rw [← replicateCol_mulVec]
    _ ≤ ‖A‖ * ‖replicateCol (Fin 1) x.ofLp‖ := frobenius_norm_mul A _
    _ = ‖A‖ * ‖WithLp.toLp 2 x.ofLp‖ := by
      rw [hx]
    _ = ‖A‖ * ‖x‖ := by
      rfl

namespace Matrix

/-- The continuous linear map induced by a matrix on Euclidean space has operator norm bounded by
its Frobenius norm. -/
theorem toEuclideanLin_opNorm_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
      A.toEuclideanLin.toContinuousLinearMap (norm_nonneg A) fun x ↦ ?_
  simpa using toEuclideanLin_apply_le_frobenius_norm A x

end Matrix

/-- Example 2.19: the operator norm of the continuous linear map induced by a matrix is bounded by
its Frobenius norm. -/
theorem matrix_operator_norm_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖A‖ :=
  Matrix.toEuclideanLin_opNorm_le_frobenius_norm A

end

/-! Source item: Chap02/Fact_2_11 -/


private theorem eq_zero_or_exists_smul_iff_not_linearIndependent_pair
    {𝕜 : Type u} {E : Type v} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (x y : E) :
    (x = 0 ∨ ∃ c : 𝕜, y = c • x) ↔ ¬ LinearIndependent 𝕜 ![x, y] := by
  constructor
  · intro hxy hlin
    rcases hxy with rfl | ⟨c, rfl⟩
    · exact (hlin.ne_zero 0) rfl
    · by_cases hx : x = 0
      · exact (hlin.ne_zero 0) hx
      · rw [LinearIndependent.pair_iff' hx] at hlin
        exact hlin c rfl
  · intro hdep
    by_cases hx : x = 0
    · exact Or.inl hx
    · rw [LinearIndependent.pair_iff' hx, not_forall] at hdep
      rcases hdep with ⟨c, hc⟩
      exact Or.inr ⟨c, (not_ne_iff.mp hc).symm⟩

/-- Fact 2.11: equality in the Cauchy--Schwarz inequality holds exactly when the pair `x, y` is
linearly dependent. Together with `norm_inner_le_norm`, this is the textbook fact. -/
theorem cauchy_schwarz_and_eq_iff_linearly_dependent_pair
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) :
    ‖inner 𝕜 x y‖ = ‖x‖ * ‖y‖ ↔ ¬ LinearIndependent 𝕜 ![x, y] := by
  calc
    ‖inner 𝕜 x y‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ c : 𝕜, y = c • x := by
      simpa using (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ ¬ LinearIndependent 𝕜 ![x, y] :=
      eq_zero_or_exists_smul_iff_not_linearIndependent_pair x y

/-! Source item: Chap02/Lemma_2_12 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Lemma 2.12 (2): textbook form of the parallelogram identity in a real inner product space. -/
theorem parallelogram_identity (x y : H) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      simpa using parallelogram_law_with_norm ℝ x y
    _ = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      ring

/-- Lemma 2.12 (3): textbook reformulation of the real polarization identity. -/
theorem polarization_identity (x y : H) :
    4 * ⟪x, y⟫_ℝ = ‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 := by
  have h_add := norm_add_sq_real x y
  have h_sub := norm_sub_sq_real x y
  nlinarith

/-- Lemma 2.12 (4): Apollonius's identity, centered at the canonical midpoint of `x` and `y`. -/
theorem apollonius_identity (x y z : H) :
    ‖x - y‖ ^ 2 =
      2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 - 4 * ‖z - midpoint ℝ x y‖ ^ 2 := by
  have h := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq z x y
  simp [dist_eq_norm, sq] at h
  linarith

/-! Source item: Chap02/Lemma_2_13 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Expand the quadratic defect of `‖x - α • y‖` into a scalar expression controlled by
`⟪x, y⟫_ℝ`. -/
private lemma norm_sub_smul_mul_self_sub_norm_mul_self (x y : H) (α : ℝ) :
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ =
      α * (α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) := by
  -- Rewrite the norm defect using the standard real inner-product expansion.
  calc
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖
        = (‖x‖ * ‖x‖ - 2 * ⟪x, α • y⟫_ℝ + ‖α • y‖ * ‖α • y‖) - ‖x‖ * ‖x‖ := by
            rw [norm_sub_mul_self_real]
    _ = -2 * ⟪x, α • y⟫_ℝ + ‖α • y‖ * ‖α • y‖ := by ring
    _ = -2 * (α * ⟪x, y⟫_ℝ) + ‖α • y‖ * ‖α • y‖ := by
          rw [real_inner_smul_right]
    _ = -2 * (α * ⟪x, y⟫_ℝ) + (|α| * ‖y‖) * (|α| * ‖y‖) := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = -2 * (α * ⟪x, y⟫_ℝ) + (α * α) * (‖y‖ * ‖y‖) := by
          rw [show (|α| * ‖y‖) * (|α| * ‖y‖) = (|α| * |α|) * (‖y‖ * ‖y‖) by ring,
            abs_mul_abs_self]
    _ = α * (α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) := by ring

/-- If the norm inequality holds for every `α ∈ [0,1]`, then the real inner product is
nonpositive. -/
private lemma real_inner_nonpos_of_norm_le_sub_smul_unitInterval (x y : H)
    (h : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖) :
    ⟪x, y⟫_ℝ ≤ 0 := by
  by_contra hxy
  have hxy_pos : 0 < ⟪x, y⟫_ℝ := lt_of_not_ge hxy
  let β : ℝ := ⟪x, y⟫_ℝ / (‖y‖ * ‖y‖ + 1)
  let α : ℝ := min 1 β
  have hden : 0 < ‖y‖ * ‖y‖ + 1 := by
    positivity
  have hβ_pos : 0 < β := by
    exact div_pos hxy_pos hden
  have hα_pos : 0 < α := by
    dsimp [α]
    exact (lt_min_iff.mpr ⟨zero_lt_one, hβ_pos⟩)
  have hα_mem : α ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_of_lt hα_pos, ?_⟩
    dsimp [α]
    exact min_le_left _ _
  -- Evaluate the interval hypothesis at a small positive scalar.
  have hα_norm : ‖x‖ ≤ ‖x - α • y‖ := h ⟨α, hα_mem⟩
  have hα_sq : ‖x‖ * ‖x‖ ≤ ‖x - α • y‖ * ‖x - α • y‖ := by
    nlinarith [hα_norm, norm_nonneg x, norm_nonneg (x - α • y)]
  have hdef_nonneg : 0 ≤ ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ := by
    nlinarith
  -- The special choice of `α` makes the quadratic defect strictly negative.
  have hβ_eq : β * (‖y‖ * ‖y‖ + 1) = ⟪x, y⟫_ℝ := by
    simp [β, hden.ne']
  have hnorm_sq_nonneg : 0 ≤ ‖y‖ * ‖y‖ := by
    positivity
  have hβ_lt : β * (‖y‖ * ‖y‖) < ⟪x, y⟫_ℝ := by
    nlinarith [hβ_eq, hβ_pos]
  have hα_le_β : α ≤ β := by
    dsimp [α]
    exact min_le_right _ _
  have hα_lt : α * (‖y‖ * ‖y‖) < ⟪x, y⟫_ℝ := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα_le_β hnorm_sq_nonneg) hβ_lt
  have hfactor_neg : α * (α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) < 0 := by
    have : α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ < 0 := by
      nlinarith [hα_lt, hxy_pos]
    exact mul_neg_of_pos_of_neg hα_pos this
  rw [norm_sub_smul_mul_self_sub_norm_mul_self] at hdef_nonneg
  linarith

/-- Lemma 2.13 (1), clause `(i)`: a nonpositive real inner product is equivalent to monotonicity
of `α ↦ ‖x - α • y‖` at `α = 0` along nonnegative real scalars. -/
theorem real_inner_nonpos_iff_norm_le_sub_nonneg_smul (x y : H) :
    ⟪x, y⟫_ℝ ≤ 0 ↔ ∀ α : NNReal, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := by
  constructor
  · intro hxy α
    have hα_nonneg : 0 ≤ (α : ℝ) := α.2
    have hy_sq_nonneg : 0 ≤ ‖y‖ * ‖y‖ := by
      positivity
    have hterm_nonneg : 0 ≤ (α : ℝ) * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ := by
      nlinarith [hxy, hα_nonneg, hy_sq_nonneg]
    have hfactor_nonneg : 0 ≤ (α : ℝ) * ((α : ℝ) * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) := by
      exact mul_nonneg hα_nonneg hterm_nonneg
    -- Nonnegativity of the defect gives the norm inequality after squaring.
    have hsq : ‖x‖ * ‖x‖ ≤ ‖x - (α : ℝ) • y‖ * ‖x - (α : ℝ) • y‖ := by
      nlinarith [norm_sub_smul_mul_self_sub_norm_mul_self x y (α : ℝ), hfactor_nonneg]
    have hsq' : ‖x‖ ^ 2 ≤ ‖x - (α : ℝ) • y‖ ^ 2 := by
      simpa [sq] using hsq
    exact le_of_sq_le_sq hsq' (norm_nonneg _)
  · intro h
    exact real_inner_nonpos_of_norm_le_sub_smul_unitInterval x y fun α ↦ by
      simpa using h ⟨α, α.2.1⟩

/-- Lemma 2.13 (1), clause `(i)`: it is enough to test the norm inequality only for
`α ∈ [0, 1]`. -/
theorem real_inner_nonpos_iff_norm_le_sub_smul_unitInterval (x y : H) :
    ⟪x, y⟫_ℝ ≤ 0 ↔ ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := by
  constructor
  · intro hxy α
    exact (real_inner_nonpos_iff_norm_le_sub_nonneg_smul x y).mp hxy ⟨α, α.2.1⟩
  · exact real_inner_nonpos_of_norm_le_sub_smul_unitInterval x y

/-- Lemma 2.13 (1): package the textbook clause `(i)` as a `TFAE`. -/
theorem real_inner_nonpos_sub_smul_tfae (x y : H) :
    List.TFAE
      [⟪x, y⟫_ℝ ≤ 0,
        (∀ α : NNReal, ‖x‖ ≤ ‖x - (α : ℝ) • y‖),
        (∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖)] := by
  tfae_have 1 ↔ 2 := real_inner_nonpos_iff_norm_le_sub_nonneg_smul x y
  tfae_have 1 ↔ 3 := real_inner_nonpos_iff_norm_le_sub_smul_unitInterval x y
  tfae_finish

/-- If the norm inequality holds on `[-1,1]`, then the real inner product vanishes. -/
private lemma real_inner_eq_zero_of_norm_le_sub_smul_symmetricUnitInterval (x y : H)
    (h : ∀ α : Set.Icc (-1 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖) :
    ⟪x, y⟫_ℝ = 0 := by
  -- First restrict the symmetric interval hypothesis to `[0,1]`.
  have hy : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := fun α ↦
    h ⟨(α : ℝ), by constructor <;> linarith [α.2.1, α.2.2]⟩
  have hnonpos : ⟪x, y⟫_ℝ ≤ 0 := by
    exact (real_inner_nonpos_iff_norm_le_sub_smul_unitInterval x y).mpr hy
  -- Then apply part (i) to `-y` by testing the original hypothesis at `-α`.
  have hneg_interval : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • (-y)‖ := fun α ↦ by
    have hmem : (-(α : ℝ)) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · linarith [α.2.2]
      · linarith [α.2.1]
    have hα : ‖x‖ ≤ ‖x - (-(α : ℝ)) • y‖ := h ⟨-(α : ℝ), hmem⟩
    simpa [sub_eq_add_neg, smul_neg, add_comm, add_left_comm, add_assoc] using hα
  have hneg_nonpos : ⟪x, -y⟫_ℝ ≤ 0 := by
    exact (real_inner_nonpos_iff_norm_le_sub_smul_unitInterval x (-y)).mpr hneg_interval
  have hnonneg : 0 ≤ ⟪x, y⟫_ℝ := by
    simpa [inner_neg_right] using hneg_nonpos
  exact le_antisymm hnonpos hnonneg

-- Proof sketch: if `⟪x, y⟫_ℝ = 0`, then `norm_sub_sq_eq_norm_sq_add_norm_sq_real` applied to
-- `x` and `α • y` gives the required inequality for every `α : ℝ`. Conversely, the hypothesis on
-- `α ∈ [-1,1]` implies the interval condition from part (i) for both `y` and `-y`, yielding
-- `⟪x, y⟫_ℝ ≤ 0` and `-⟪x, y⟫_ℝ ≤ 0`, hence equality.
/-- Lemma 2.13 (2), clause `(ii)`: vanishing of the real inner product is equivalent to the norm
inequality for every real scalar. -/
theorem real_inner_eq_zero_iff_norm_le_sub_smul (x y : H) :
    ⟪x, y⟫_ℝ = 0 ↔ ∀ α : ℝ, ‖x‖ ≤ ‖x - α • y‖ := by
  constructor
  · intro hxy α
    have horth : ⟪x, α • y⟫_ℝ = 0 := by
      rw [real_inner_smul_right, hxy, mul_zero]
    have hpyth : ‖x - α • y‖ * ‖x - α • y‖ = ‖x‖ * ‖x‖ + ‖α • y‖ * ‖α • y‖ :=
      norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
    -- Orthogonality turns the defect into a nonnegative square term.
    have hsq : ‖x‖ * ‖x‖ ≤ ‖x - α • y‖ * ‖x - α • y‖ := by
      nlinarith [hpyth, norm_nonneg (α • y)]
    have hsq' : ‖x‖ ^ 2 ≤ ‖x - α • y‖ ^ 2 := by
      simpa [sq] using hsq
    exact le_of_sq_le_sq hsq' (norm_nonneg _)
  · intro h
    exact real_inner_eq_zero_of_norm_le_sub_smul_symmetricUnitInterval x y fun α ↦ h α

/-- Lemma 2.13 (2), clause `(ii)`: it is enough to test the norm inequality for
`α ∈ [-1, 1]`. -/
theorem real_inner_eq_zero_iff_norm_le_sub_smul_symmetricUnitInterval (x y : H) :
    ⟪x, y⟫_ℝ = 0 ↔ ∀ α : Set.Icc (-1 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := by
  constructor
  · intro hxy α
    exact (real_inner_eq_zero_iff_norm_le_sub_smul x y).mp hxy α
  · exact real_inner_eq_zero_of_norm_le_sub_smul_symmetricUnitInterval x y

/-- Lemma 2.13 (2): package the textbook clause `(ii)` as a `TFAE`. -/
theorem real_inner_eq_zero_sub_smul_tfae (x y : H) :
    List.TFAE
      [⟪x, y⟫_ℝ = 0,
        (∀ α : ℝ, ‖x‖ ≤ ‖x - α • y‖),
        (∀ α : Set.Icc (-1 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖)] := by
  tfae_have 1 ↔ 2 := real_inner_eq_zero_iff_norm_le_sub_smul x y
  tfae_have 1 ↔ 3 := real_inner_eq_zero_iff_norm_le_sub_smul_symmetricUnitInterval x y
  tfae_finish

/-! Source item: Chap02/Lemma_2_14 -/


variable {ι : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Lemma 2.14: rewrite the exchanged cross terms as diagonal terms minus the pairwise
correction inner product. -/
-- Proof step: expand `⟪x i - x j, u i - u j⟫_ℝ` and solve the resulting real-valued identity.
private lemma pairwise_inner_exchange_identity
    (x u : ι → H) (i j : ι) :
    ⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ =
      ⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ - ⟪x i - x j, u i - u j⟫_ℝ := by
  have h_expand :
      ⟪x i - x j, u i - u j⟫_ℝ =
        ⟪x i, u i⟫_ℝ - ⟪x i, u j⟫_ℝ - ⟪x j, u i⟫_ℝ + ⟪x j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  nlinarith [h_expand]

/-- Helper for Lemma 2.14: doubling the inner product of two weighted affine combinations produces
the symmetric double sum of exchanged cross terms. -/
-- Proof step: first expand the affine-combination inner product into a double sum, then symmetrize the
-- second copy by swapping the finite summation order.
private lemma two_mul_weighted_inner_eq_sum_cross_terms
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) :
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
      ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
  have h_single :
      ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
        ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ := by
    -- Expand the two weighted sums using bilinearity of the real inner product.
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    ring_nf
  calc
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ)
            + (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) := by
              rw [h_single]
              ring
    _ = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ)
          + (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u i⟫_ℝ) := by
            congr 1
            -- Commute the second double sum so it matches the exchanged cross term.
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_comm (α j) (α i), real_inner_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
          -- Repackage the two double sums into the pointwise sum required by the textbook proof.
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Lemma 2.14: the diagonal double sum collapses to twice the weighted diagonal sum
when the weights add up to `1`. -/
-- Proof step: separate the two diagonal contributions and use the weight-sum hypothesis on each.
private lemma weighted_double_sum_diagonal_eq_two_mul_sum
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ)
    (hα : (∑ i ∈ s, α i) = 1) :
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) =
      2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  calc
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ)
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ)
            + (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u j⟫_ℝ) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) + (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            -- Freeze the `i`-diagonal term and sum the weights over `j`.
            calc
              ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ
                  = α i * ∑ j ∈ s, α j * ⟪x i, u i⟫_ℝ := by
                      simpa [mul_assoc] using
                        (Finset.mul_sum s (fun j ↦ α j * ⟪x i, u i⟫_ℝ) (α i)).symm
              _ = α i * ((∑ j ∈ s, α j) * ⟪x i, u i⟫_ℝ) := by rw [Finset.sum_mul]
              _ = α i * ⟪x i, u i⟫_ℝ := by rw [hα, one_mul]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            -- After commuting the sums, the same collapse applies to the `j`-diagonal term.
            calc
              ∑ i ∈ s, α i * α j * ⟪x j, u j⟫_ℝ
                  = (∑ i ∈ s, α i) * (α j * ⟪x j, u j⟫_ℝ) := by
                      simpa [mul_assoc] using
                        (Finset.sum_mul s (fun i ↦ α i) (α j * ⟪x j, u j⟫_ℝ)).symm
              _ = α j * ⟪x j, u j⟫_ℝ := by rw [hα, one_mul]
    _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by ring

/-- Lemma 2.14 (1): for a finite real-weighted family in a real inner product space whose weights
sum to `1`, the inner product of the two weighted affine combinations plus the half pairwise
correction term equals the weighted sum of the diagonal inner products. -/
-- Proof sketch: expand the left-hand inner product by bilinearity, rewrite
-- `⟪x i - x j, u i - u j⟫_ℝ`, and use the hypothesis `(∑ i ∈ s, α i) = 1` twice to collapse the
-- double sum of diagonal terms to `2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ`.
theorem weighted_inner_eq_sum_inner_add_half_pairwise
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) (hα : (∑ i ∈ s, α i) = 1) :
    ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
      ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  have h_two :
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
        2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
    calc
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ
          = (∑ i ∈ s, ∑ j ∈ s, α i * α j *
                (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ))
              + ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ := by
              -- Replace the doubled affine-combination inner product by its symmetric double-sum expansion.
              rw [two_mul_weighted_inner_eq_sum_cross_terms]
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j *
            ((⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) + ⟪x i - x j, u i - u j⟫_ℝ) := by
              -- Merge the correction term into the same double sum so the pointwise rewrite applies.
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) := by
              -- Rewrite each exchanged pair by the diagonal terms from the previous helper lemma.
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [pairwise_inner_exchange_identity]
              ring
      _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ :=
            weighted_double_sum_diagonal_eq_two_mul_sum s x u α hα
  -- Divide the doubled identity by `2`.
  linarith

/-- Lemma 2.14 (2): for a finite real-weighted family in a real inner product space whose weights
sum to `1`, the squared norm of the weighted affine combination plus the half pairwise correction
term equals the weighted sum of the squared norms. -/
-- Proof sketch: apply part (1) to the same family twice, taking `u = x`, and simplify
-- `⟪y, y⟫_ℝ` to `‖y‖ ^ 2` in a real inner product space.
theorem weighted_norm_sq_eq_sum_norm_sq_add_half_pairwise
    (s : Finset ι) (x : ι → H) (α : ι → ℝ) (hα : (∑ i ∈ s, α i) = 1) :
    ‖∑ i ∈ s, α i • x i‖ ^ (2 : ℕ) +
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ‖x i - x j‖ ^ (2 : ℕ) =
      ∑ i ∈ s, α i * ‖x i‖ ^ (2 : ℕ) := by
  -- Specialize part (1) to `u = x` and rewrite self-inner products as squared norms.
  simpa [real_inner_self_eq_norm_sq] using
    weighted_inner_eq_sum_inner_add_half_pairwise s x x α hα

/-! Source item: Chap02/Corollary_2_15 -/

/-- Corollary 2.15: in a real inner product space, the squared norm of an affine combination plus
the weighted squared distance equals the corresponding affine combination of squared norms. -/
-- Proof sketch: expand `‖α • x + (1 - α) • y‖ ^ 2` using `norm_add_sq_real` and scalar
-- multiplication identities, expand `‖x - y‖ ^ 2` using `norm_sub_sq_real`, and simplify the
-- resulting polynomial identity in `α`.
theorem norm_sq_affine_combination_add_weighted_norm_sub_sq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (α : ℝ) :
    ‖α • x + (1 - α) • y‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 =
      α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  -- Expand the two squared norms by the standard real inner-product identities and normalize the
  -- scalar coefficients in one pass.
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  simp [real_inner_smul_left, real_inner_smul_right]
  nlinarith [sq_abs α, sq_abs (1 - α)]

/-! Source item: Chap02/Corollary_2_16 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 2.16: if distinct vectors `x` and `y` in a real Hilbert space have the same norm,
then every nontrivial convex combination `α • x + (1 - α) • y` with `0 < α` and `α < 1` has norm
strictly less than `‖x‖`. -/
theorem norm_convexCombination_lt_of_ne_of_norm_eq {x y : H} {α : ℝ}
    (hxy : x ≠ y) (hnorm : ‖x‖ = ‖y‖) (hα0 : 0 < α) (hα1 : α < 1) :
    ‖α • x + (1 - α) • y‖ < ‖x‖ := by
  -- This is the textbook equal-norm specialization of the canonical strict-convexity estimate
  -- `norm_combo_lt_of_ne`.
  refine norm_combo_lt_of_ne le_rfl ?_ hxy hα0 (sub_pos.mpr hα1) ?_
  · simp [hnorm]
  · ring

/-! Source item: Chap02/Lemma_2_17 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand `‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2` with `norm_add_sq_real`, rewrite the scalar
-- factors using `real_inner_smul_left` and `real_inner_smul_right`, and simplify the resulting
-- polynomial identity in `α`.
/-- Lemma 2.17 (1): for `α ∈ (0,1)`, the scaled difference between `‖x‖²` and the squared norm of
`(1 - α⁻¹) • x + α⁻¹ • y` equals `(2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2`. -/
theorem alpha_sq_norm_sq_sub_inv_affine_combination_eq
    (x y : H) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2) =
      (2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2 := by
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have hnorm :
      ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2 =
        (1 - α⁻¹) ^ 2 * ‖x‖ ^ 2 + 2 * ((1 - α⁻¹) * α⁻¹ * inner ℝ x y) + (α⁻¹) ^ 2 * ‖y‖ ^ 2 := by
    -- Expand the affine combination exactly once, then rewrite the scalar coefficients.
    rw [norm_add_sq_real]
    have hαabs : |α| = α := abs_of_pos hα.1
    simp [norm_smul, real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc, hαabs]
    nlinarith [sq_abs (1 - α⁻¹)]
  -- Clear the inverse denominators and normalize the resulting scalar identity.
  rw [hnorm]
  field_simp [hα0]
  ring

-- Proof sketch: this is an immediate rearrangement of the previous identity, moving the
-- `‖x‖ ^ 2`-term into the parenthesized expression.
/-- Lemma 2.17 (2): for `α ∈ (0,1)`, the same scaled norm identity can be rewritten as
`2 * (1 - α) * inner ℝ x y - (‖y‖ ^ 2 + (1 - 2 * α) * ‖x‖ ^ 2)`. -/
theorem alpha_sq_norm_sq_sub_inv_affine_combination_eq_rearranged
    (x y : H) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2) =
      2 * (1 - α) * inner ℝ x y - (‖y‖ ^ 2 + (1 - 2 * α) * ‖x‖ ^ 2) := by
  -- Reuse the structural expansion from part (1) and only rearrange the scalar terms.
  calc
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2)
        = (2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2 :=
          alpha_sq_norm_sq_sub_inv_affine_combination_eq x y hα
    _ = 2 * (1 - α) * inner ℝ x y - (‖y‖ ^ 2 + (1 - 2 * α) * ‖x‖ ^ 2) := by
      ring

-- Proof sketch: combine the first identity with `norm_sub_sq_real x y` to rewrite
-- `2 * inner ℝ x y` as `‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2`, then simplify.
/-- Lemma 2.17 (3): for `α ∈ (0,1)`, the scaled norm identity also equals
`α * (‖x‖ ^ 2 - α⁻¹ * (1 - α) * ‖x - y‖ ^ 2 - ‖y‖ ^ 2)`. -/
theorem alpha_sq_norm_sq_sub_inv_affine_combination_eq_norm_sub
    (x y : H) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2) =
      α * (‖x‖ ^ 2 - α⁻¹ * (1 - α) * ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  -- Substitute the standard norm-subtraction formula into the part (1) identity.
  calc
    α ^ 2 * (‖x‖ ^ 2 - ‖(1 - α⁻¹) • x + α⁻¹ • y‖ ^ 2)
        = (2 * α - 1) * ‖x‖ ^ 2 + 2 * (1 - α) * inner ℝ x y - ‖y‖ ^ 2 :=
          alpha_sq_norm_sq_sub_inv_affine_combination_eq x y hα
    _ = α * (‖x‖ ^ 2 - α⁻¹ * (1 - α) * ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
      rw [norm_sub_sq_real]
      field_simp [hα0]
      ring

-- Proof sketch: expand `‖2 • y - x‖ ^ 2` using `norm_sub_sq_real (2 • y) x`, rewrite the scalar
-- terms with `norm_smul` and `real_inner_smul_left`, and simplify.
/-- Lemma 2.17 (4): the difference `‖x‖² - ‖2 • y - x‖²` equals
`4 * (inner ℝ x y - ‖y‖ ^ 2)`. -/
theorem norm_sq_sub_norm_sq_reflection_eq_four_mul
    (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * (inner ℝ x y - ‖y‖ ^ 2) := by
  rw [show (2 : ℝ) • y = y + y by simp [two_smul]]
  have hsub : ‖x‖ ^ 2 - ‖(y + y) - x‖ ^ 2 = 2 * inner ℝ (y + y) x - ‖y + y‖ ^ 2 := by
    -- First isolate the reflected norm term using the standard `‖u - v‖²` identity.
    nlinarith [norm_sub_sq_real (y + y) x]
  have hnorm : ‖y + y‖ ^ 2 = 4 * ‖y‖ ^ 2 := by
    -- Then expand the doubled point `y + y`.
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  -- Assemble the two expansions and commute the inner product once.
  rw [hsub, hnorm, inner_add_left, real_inner_comm y x]
  ring

-- Proof sketch: rewrite `inner ℝ (x - y) y` with `inner_sub_left` and
-- `real_inner_self_eq_norm_sq` to identify it with `inner ℝ x y - ‖y‖ ^ 2`, then use the
-- previous formula.
/-- Lemma 2.17 (5): the same reflection identity can be written as
`4 * inner ℝ (x - y) y`. -/
theorem norm_sq_sub_norm_sq_reflection_eq_four_inner_sub
    (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * inner ℝ (x - y) y := by
  -- Rewrite the part (4) formula using the linearity of the inner product in the left slot.
  calc
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * (inner ℝ x y - ‖y‖ ^ 2) :=
      norm_sq_sub_norm_sq_reflection_eq_four_mul x y
    _ = 4 * inner ℝ (x - y) y := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]

-- Proof sketch: apply `norm_sub_sq_real x y` to replace `2 * inner ℝ x y` by
-- `‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2`, then simplify the previous identity.
/-- Lemma 2.17 (6): the reflection identity is also
`2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2)`. -/
theorem norm_sq_sub_norm_sq_reflection_eq_two_mul_norm_sub
    (x y : H) :
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 =
      2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
  -- Substitute the standard expression for `‖x - y‖²` into the part (4) identity.
  calc
    ‖x‖ ^ 2 - ‖(2 : ℝ) • y - x‖ ^ 2 = 4 * (inner ℝ x y - ‖y‖ ^ 2) :=
      norm_sq_sub_norm_sq_reflection_eq_four_mul x y
    _ = 2 * (‖x‖ ^ 2 - ‖x - y‖ ^ 2 - ‖y‖ ^ 2) := by
      rw [norm_sub_sq_real]
      ring

/-! Source item: Chap02/Fact_2_18 -/

-- Private helper: an antitone permutation of `x`.
private def IsAntitonePerm {N : ℕ} (x xDown : Fin N → ℝ) : Prop :=
  Antitone xDown ∧ ∃ σ : Equiv.Perm (Fin N), xDown = x ∘ σ

/-- The canonical nonincreasing rearrangement of a finite real vector, obtained by sorting it in
descending order. -/
noncomputable def nonincreasingRearrangement {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  x ∘ sort (toDual ∘ x)

/-- The canonical nonincreasing rearrangement is antitone. -/
theorem antitone_nonincreasingRearrangement
    {N : ℕ} (x : Fin N → ℝ) :
    Antitone (nonincreasingRearrangement x) := by
  simpa [nonincreasingRearrangement, Function.comp_assoc] using
    (monotone_sort (toDual ∘ x) : Monotone ((toDual ∘ x) ∘ sort (toDual ∘ x)))

-- The canonical sorted tuple is an antitone permutation of the original tuple.
private theorem isAntitonePerm_nonincreasingRearrangement
    {N : ℕ} (x : Fin N → ℝ) :
    IsAntitonePerm x (nonincreasingRearrangement x) := by
  refine ⟨antitone_nonincreasingRearrangement x, sort (toDual ∘ x), rfl⟩

-- Helper for Fact 2.18: rewrite the original dot product through the sorting permutations.
private lemma dotProduct_eq_sorted_dotProduct_comp_perm
    {N : ℕ} {x y xDown yDown : Fin N → ℝ}
    {σx σy : Equiv.Perm (Fin N)}
    (hxEq : xDown = x ∘ σx) (hyEq : yDown = y ∘ σy) :
    dotProduct x y = dotProduct xDown (yDown ∘ (σx.trans σy.symm)) := by
  have hyComp : y ∘ σx = yDown ∘ (σx.trans σy.symm) := by
    funext i
    simp [hyEq]
  -- Move both vectors through the sorting permutation of `x`, then identify the induced
  -- permutation on the sorted version of `y`.
  calc
    dotProduct x y = dotProduct (x ∘ σx) (y ∘ σx) := by
      simp
    _ = dotProduct xDown (y ∘ σx) := by
      simp [hxEq]
    _ = dotProduct xDown (yDown ∘ (σx.trans σy.symm)) := by
      simp [hyComp]

-- Helper for Fact 2.18: if the sorted `y`-vector composed with a permutation still monovaries
-- with the sorted `x`-vector, then one can reorder only inside equal-value blocks of `xDown` to
-- recover `yDown`.
private theorem exists_block_preserving_perm_of_monovary_sorted_comp
    {N : ℕ} {xDown yDown : Fin N → ℝ}
    (hxAnti : Antitone xDown) (hyAnti : Antitone yDown)
    (τ : Equiv.Perm (Fin N))
    (hmono : Monovary xDown (yDown ∘ τ)) :
    ∃ ρ : Equiv.Perm (Fin N), xDown ∘ ρ = xDown ∧ yDown ∘ τ ∘ ρ = yDown := by
  classical
  obtain ⟨auxOrder, hxAux, hyAux⟩ := hmono.exists_antitone
  have e : @OrderIso (Fin N) (Fin N) instLEFin auxOrder.toLE := by
    letI := auxOrder
    exact monoEquivOfFin (Fin N) (Fintype.card_fin N)
  let ρ : Equiv.Perm (Fin N) := e.toEquiv
  -- Transport the auxiliary antitone order back to the standard order on `Fin N`.
  have hxComp : Antitone (xDown ∘ ρ) := by
    intro i j hij
    have hij' : @LE.le (Fin N) auxOrder.toLE (ρ i) (ρ j) := by
      change @LE.le (Fin N) auxOrder.toLE (e i) (e j)
      exact e.map_rel_iff'.2 hij
    exact hxAux hij'
  have hyComp : Antitone (yDown ∘ (ρ.trans τ)) := by
    intro i j hij
    have hij' : @LE.le (Fin N) auxOrder.toLE (ρ i) (ρ j) := by
      change @LE.le (Fin N) auxOrder.toLE (e i) (e j)
      exact e.map_rel_iff'.2 hij
    simpa [ρ] using hyAux hij'
  refine ⟨ρ, ?_, ?_⟩
  · -- The sorted tuple `xDown` is the unique antitone permutation of itself.
    have hxEq : xDown ∘ ρ = xDown ∘ Equiv.refl (Fin N) := unique_antitone hxComp (by simpa using hxAnti)
    simpa using hxEq
  · -- The same uniqueness argument forces the transported `yDown` tuple back to `yDown`.
    have hyEq : yDown ∘ (ρ.trans τ) = yDown ∘ Equiv.refl (Fin N) :=
      unique_antitone hyComp (by simpa using hyAnti)
    simpa [Function.comp_assoc] using hyEq

-- Proof sketch: choose permutations sending `x` and `y` to `xDown` and `yDown`, apply mathlib's
-- rearrangement inequality to the antitone rearrangements.
/-- Fact 2.18: the Euclidean inner product of two finite real vectors is bounded above by the inner
product of their nonincreasing rearrangements. -/
private theorem hardy_littlewood_polya_inequality_of_antitone_perm
    {N : ℕ} {x y xDown yDown : Fin N → ℝ}
    (hxDown : IsAntitonePerm x xDown)
    (hyDown : IsAntitonePerm y yDown) :
    dotProduct x y ≤ dotProduct xDown yDown := by
  rcases hxDown with ⟨hxAnti, σx, hxEq⟩
  rcases hyDown with ⟨hyAnti, σy, hyEq⟩
  let τ : Equiv.Perm (Fin N) := σx.trans σy.symm
  have hmono : Monovary xDown yDown := Antitone.monovary hxAnti hyAnti
  have hineq : dotProduct xDown (yDown ∘ τ) ≤ dotProduct xDown yDown := by
    have hineq' : ∑ i, xDown i * yDown (τ i) ≤ ∑ i, xDown i * yDown i :=
      hmono.sum_mul_comp_perm_le_sum_mul
    simpa [dotProduct, τ] using hineq'
  -- Rewrite the original inner product into the rearrangement form and apply mathlib's inequality.
  calc
    dotProduct x y = dotProduct xDown (yDown ∘ τ) := by
      simpa [τ] using dotProduct_eq_sorted_dotProduct_comp_perm hxEq hyEq
    _ ≤ dotProduct xDown yDown := hineq

-- Proof sketch: combine the rearrangement equality case with the uniqueness of antitone
-- rearrangements to identify equality with the existence of a common sorting permutation.
/-- Equality in the Hardy-Littlewood-Polya inequality holds exactly when one permutation sends both
vectors to their nonincreasing rearrangements. -/
private theorem hardy_littlewood_polya_inequality_eq_iff_of_antitone_perm
    {N : ℕ} {x y xDown yDown : Fin N → ℝ}
    (hxDown : IsAntitonePerm x xDown)
    (hyDown : IsAntitonePerm y yDown) :
    dotProduct x y = dotProduct xDown yDown ↔
      ∃ σ : Equiv.Perm (Fin N),
        xDown = x ∘ σ ∧ yDown = y ∘ σ := by
  rcases hxDown with ⟨hxAnti, σx, hxEq⟩
  rcases hyDown with ⟨hyAnti, σy, hyEq⟩
  let τ : Equiv.Perm (Fin N) := σx.trans σy.symm
  constructor
  · intro hEq
    have hrewrite : dotProduct x y = dotProduct xDown (yDown ∘ τ) := by
      simpa [τ] using dotProduct_eq_sorted_dotProduct_comp_perm hxEq hyEq
    have hSortedEq : dotProduct xDown (yDown ∘ τ) = dotProduct xDown yDown := by
      rw [← hrewrite]
      exact hEq
    have hmono : Monovary xDown (yDown ∘ τ) := by
      have hxy : Monovary xDown yDown := Antitone.monovary hxAnti hyAnti
      have hSortedEq' : ∑ i, xDown i * yDown (τ i) = ∑ i, xDown i * yDown i := by
        simpa [dotProduct, τ] using hSortedEq
      exact (hxy.sum_mul_comp_perm_eq_sum_mul_iff).mp hSortedEq'
    obtain ⟨ρ, hxPres, hyPres⟩ :=
      exists_block_preserving_perm_of_monovary_sorted_comp hxAnti hyAnti τ hmono
    refine ⟨ρ.trans σx, ?_, ?_⟩
    · calc
        xDown = xDown ∘ ρ := hxPres.symm
        _ = x ∘ (ρ.trans σx) := by
          funext i
          simp [hxEq]
    · calc
        yDown = yDown ∘ τ ∘ ρ := hyPres.symm
        _ = y ∘ (ρ.trans σx) := by
          funext i
          simp [τ, hyEq, Function.comp_assoc]
  · rintro ⟨σ, hxPerm, hyPerm⟩
    -- A common permutation preserves the dot product, so the sorted and unsorted products agree.
    calc
      dotProduct x y = dotProduct (x ∘ σ) (y ∘ σ) := by
        simp
      _ = dotProduct xDown yDown := by
        simp [hxPerm, hyPerm]

/-- Fact 2.18: the Euclidean inner product of two finite real vectors is bounded above by the inner
product of their canonical nonincreasing rearrangements. -/
theorem hardy_littlewood_polya_inequality
    {N : ℕ} {x y : Fin N → ℝ} :
    dotProduct x y ≤
      dotProduct (nonincreasingRearrangement x) (nonincreasingRearrangement y) := by
  simpa using
    hardy_littlewood_polya_inequality_of_antitone_perm
      (isAntitonePerm_nonincreasingRearrangement x)
      (isAntitonePerm_nonincreasingRearrangement y)

/- Equality in Fact 2.18 says that the same permutation sorts both vectors into descending order. -/
theorem hardy_littlewood_polya_inequality_eq_iff
    {N : ℕ} {x y : Fin N → ℝ} :
    dotProduct x y =
        dotProduct (nonincreasingRearrangement x) (nonincreasingRearrangement y) ↔
      ∃ σ : Equiv.Perm (Fin N),
        nonincreasingRearrangement x = x ∘ σ ∧
          nonincreasingRearrangement y = y ∘ σ := by
  simpa using
    hardy_littlewood_polya_inequality_eq_iff_of_antitone_perm
      (isAntitonePerm_nonincreasingRearrangement x)
      (isAntitonePerm_nonincreasingRearrangement y)
