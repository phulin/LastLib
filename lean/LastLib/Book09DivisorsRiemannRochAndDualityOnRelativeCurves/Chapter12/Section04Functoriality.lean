import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12.Section03DualityForLineBundlesAndVectorBundles

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-! ### 12.4 Functoriality -/

/-- Finite duality identifies the pushed-forward dualizing sheaf with the
internal Hom from the pushed-forward structure sheaf. -/
theorem chapter12_finite_dualizing_comparison_exists
    {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k)
    [Chapter12InternalHomTheory P.target.carrier] :
    Nonempty (Chapter12FiniteDualizingComparison P) := by
  sorry

theorem chapter12_finite_dualizing_comparison
    {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k)
    [Chapter12InternalHomTheory P.target.carrier]
    (E : Chapter12FiniteDualizingComparison P) :
    Nonempty (chapter12PushforwardDualizingSheaf P ≅
      chapter12InternalHom (chapter12PushforwardStructureSheaf P)
        P.target.dualizing) := by
  exact ⟨E.iso⟩

/-- Evaluation at the unit is the finite trace map. -/
theorem chapter12_finite_trace_is_evaluation
    {k : Type u} [Field k]
    {P : Chapter12FiniteMapOfProperCohenMacaulayCurves k}
    [Chapter12InternalHomTheory P.target.carrier]
    (E : Chapter12FiniteDualizingComparison P) :
    chapter12FiniteTraceByEvaluation E =
      E.iso.hom ≫
        Chapter12InternalHomTheory.evaluationAtOne (chapter12FiniteMapUnit P) := by
  rfl

theorem chapter12_finite_trace_exists
    {k : Type u} [Field k]
    (P : Chapter12FiniteMapOfProperCohenMacaulayCurves k)
    [Chapter12InternalHomTheory P.target.carrier] :
    Nonempty (chapter12PushforwardDualizingSheaf P ⟶ P.target.dualizing) := by
  sorry

/-- On smooth generically separable curves the finite trace package carries
the rational differential trace, including the comparison with the usual
rational formula. -/
theorem chapter12_smooth_generically_separable_trace_comparison
    {k : Type u} [Field k]
    {P : Chapter12FiniteMapOfProperCohenMacaulayCurves k}
    (R : Chapter12FiniteMapRationalTraceData P)
    (hsource : R.smoothSource) (htarget : R.smoothTarget)
    (hseparable : R.genericallySeparable)
    (η : R.rationalDifferentialY) :
    R.traceCompatibility η (R.rationalTrace η) := by
  exact R.rationalTrace_is_sheafTrace η

/-- Pullback of functions and trace of differentials are adjoint for the
residue pairing. -/
theorem chapter12_finite_map_residue_pairing_adjoint
    {k : Type u} [Field k]
    {P : Chapter12FiniteMapOfProperCohenMacaulayCurves k}
    (R : Chapter12FiniteMapResidueData P)
    (α : R.rationalFunctionX) (η : R.rationalDifferentialY) :
    R.pairingY (R.pullbackFunction α) η =
      R.pairingX α (R.traceDifferential η) := by
  exact R.adjoint α η

/-! The next record makes the phrase “transpose on cohomology” an explicit
pair of linear maps and gives the evaluation equations that characterize both
transposes. -/
structure Chapter12VectorBundleCohomologyTranspose
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E F : Chapter12VectorBundle C)
    (φ : Chapter12DualizedVectorBundleMap E F)
    (DE : Chapter12VectorBundleDualityFamily K W E)
    (DF : Chapter12VectorBundleDualityFamily K W F) where
  mapZero : chapter12HZero K E.module →ₗ[k] chapter12HZero K F.module
  mapOne : chapter12HOne K E.module →ₗ[k] chapter12HOne K F.module
  transposeZero :
    chapter12HOne K (chapter12VectorBundleOmegaTwist W F) →ₗ[k]
      chapter12HOne K (chapter12VectorBundleOmegaTwist W E)
  transposeOne :
    chapter12HZero K (chapter12VectorBundleOmegaTwist W F) →ₗ[k]
      chapter12HZero K (chapter12VectorBundleOmegaTwist W E)
  mapZero_eq_cohomologyMap : mapZero = chapter12CohomologyMap K φ.hom 0
  mapOne_eq_cohomologyMap : mapOne = chapter12CohomologyMap K φ.hom 1
  transposeZero_apply : ∀ x y,
    (DF.degreeZero.symm y) (mapZero x) =
      (DE.degreeZero.symm (transposeZero y)) x
  transposeOne_apply : ∀ x y,
    (DF.degreeOne.symm y) (mapOne x) =
      (DE.degreeOne.symm (transposeOne y)) x

theorem chapter12_vector_bundle_map_has_transpose
    {k : Type u} [Field k] {C : Chapter12Curve k}
    [Chapter12VectorBundleDuality C]
    (K : Chapter12CohomologyContext C)
    (W : Chapter12DualizingSheafData C K)
    (E F : Chapter12VectorBundle C)
    (φ : Chapter12DualizedVectorBundleMap E F)
    (DE : Chapter12VectorBundleDualityFamily K W E)
    (DF : Chapter12VectorBundleDualityFamily K W F) :
    Nonempty (Chapter12VectorBundleCohomologyTranspose K W E F φ DE DF) := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter12
