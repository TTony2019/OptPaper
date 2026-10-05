import TheoremLib.Dual_guided_2026.SDOTAsymptotics
import TheoremLib.Dual_guided_2026.SDOTMasterFourthAsymptotics

/-!
# Theorem III.1: error scaling of HELLO-SDOT

The experiment and Appendix F assumptions are defined in `SDOT`.
`SDOTMoments` proves the exact categorical second moment (40), and
`SDOTTies` proves Lemma F.5 (51)--(52), including the averaged tie bound.
`SDOTMovingCells` proves the boundary-envelope estimate (55), and
`SDOTLinearization` proves (41) and the exact remainder decomposition.
`SDOTPopulationObjective` and `SDOTNetLocalization` prove the local margin
and concentration of empirical maximizers. Finite-grid bracketing then
controls the actual moving-cell remainder in second and fourth moment.
`SDOTAsymptotics` proves (39) and the expectation asymptotic.
`SDOTVariance` computes the categorical fourth moment and exact variance;
`SDOTMasterFourthAsymptotics` transfers this to the actual marginal error.
-/

namespace DualGuided2026

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

/-- Theorem III.1 (Error Scaling of HELLO-SDOT).

For fixed target sites, target size, target marginal, and a finite repetition
range, exact empirical OT solves under the strengthened moment condition
give both asymptotics. `theorem_3_1_mean` gives the expectation conclusion
under the basic moment condition alone.
-/
theorem theorem_3_1 (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data)
    (_hstrengthened : HasStrengthenedMoment data) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.meanError m R - helloSDOTMeanLeading data.n m R)
      (fun m => 1 / (m : ℝ)) ∧
    IsUniformLittleOInM data.rmax
      (fun m R => data.varianceError m R - helloSDOTVarianceLeading data.n m R)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  exact ⟨theorem_3_1_mean data hregular hexact,
    theorem_3_1_variance data hregular hexact⟩

end DualGuided2026
