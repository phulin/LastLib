import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12.Section01TheExactReusableModelTheorem

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! ## 12.4. Semistable reduction input -/

structure Chapter12NodeDescription where
  R : Type u
  [commRingR : CommRing R]
  [domainR : IsDomain R]
  [dvrR : IsDiscreteValuationRing R]
  A : Type u
  [commRingA : CommRing A]
  [algebraRA : Algebra R A]
  [localA : IsLocalRing A]
  uniformizer : R
  presentation : Chapter12NodeCompletedLocalPresentation R A uniformizer
  completed_stalk_description : Prop
  etale_extension_allowed : Prop

structure Chapter12SemistableNodeAtlas
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    (M : Chapter12SemistableOpenModel B C V) where
  description : M.nodeIndex → Chapter12NodeDescription.{u}
  description_at_node : M.nodeIndex → Prop

structure Chapter12SemistableReductionInput
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (E : Chapter12FiniteSeparableExtension K L)
    (B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B)
    (C' : Chapter01SmoothProperCurveOverField L) where
  V : B'.carrier.Opens
  genericCurveBaseChange :
    C'.carrier ≅ chapter12FieldBaseChange (K := K) (L := L) C.carrier C.structureMap
  supplied : Chapter12SemistableOpenModel
    (chapter12NormalizedBaseAsExcellentDedekindBase B') C' V
  atlas : Chapter12SemistableNodeAtlas supplied
  compatibleAlgebraicInput : Prop

structure Chapter12SemistableExtensionResult
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {E : Chapter12FiniteSeparableExtension K L}
    {B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B}
    {C' : Chapter01SmoothProperCurveOverField L}
    (I : Chapter12SemistableReductionInput B C E B' C') where
  model : Chapter12RegularFlatProjectiveModel
    (chapter12NormalizedBaseAsExcellentDedekindBase B') C'
  extension : Chapter12SemistableModelExtension I.supplied model
  centers_outside_V : Prop
  semistable_locus_unchanged : Prop
  resolution_avoids_node : I.supplied.nodeIndex → Prop

theorem chapter12_semistable_reduction_extension_exists
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (B : Chapter12ExcellentDedekindBase S K)
    (C : Chapter01SmoothProperCurveOverField K)
    (E : Chapter12FiniteSeparableExtension K L)
    (B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B)
    (C' : Chapter01SmoothProperCurveOverField L)
    (I : Chapter12SemistableReductionInput B C E B' C') :
    Nonempty (Chapter12SemistableExtensionResult I) := by
  sorry

theorem chapter12_semistable_resolution_centers_avoid_supplied_open
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {E : Chapter12FiniteSeparableExtension K L}
    {B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B}
    {C' : Chapter01SmoothProperCurveOverField L}
    {I : Chapter12SemistableReductionInput B C E B' C'}
    (R : Chapter12SemistableExtensionResult I) :
    R.centers_outside_V := by
  sorry

/-! ### The node equation -/

theorem chapter12_semistable_node_completed_local_equation
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K}
    {E : Chapter12FiniteSeparableExtension K L}
    {B' : Chapter12NormalizedDedekindBase (K := K) (L := L) B}
    {C' : Chapter01SmoothProperCurveOverField L}
    (I : Chapter12SemistableReductionInput B C E B' C')
    (i : I.supplied.nodeIndex) :
    Nonempty Chapter12NodeDescription.{u} := by
  exact ⟨I.atlas.description i⟩

theorem chapter12_semistable_node_completed_local_ring_is_regular
    (D : Chapter12NodeDescription) :
    @IsRegularLocalRing D.A D.commRingA := by
  sorry

structure Chapter12NodeResolutionInvariance
    (D : Chapter12NodeDescription) where
  node_regular : @IsRegularLocalRing D.A D.commRingA
  resolution_is_iso_at_node : Prop
  completed_ring_unchanged : Prop

theorem chapter12_regular_node_is_not_modified_by_resolution
    (D : Chapter12NodeDescription)
    (R : Chapter12NodeResolutionInvariance D) :
    R.completed_ring_unchanged :=
by
  sorry

/-! ### Marked sections and stable contraction -/

theorem chapter12_marked_sections_can_be_separated_from_nodes
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    {M₀ : Chapter12SemistableOpenModel B C V}
    (M : Chapter12MarkedSemistableModel (B := B) (C := C) (V := V) M₀) :
    Nonempty (Chapter12NodeSeparationData M) := by
  sorry

theorem chapter12_node_separation_is_by_point_blowups
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    {M₀ : Chapter12SemistableOpenModel B C V}
    {M : Chapter12MarkedSemistableModel (B := B) (C := C) (V := V) M₀}
    (D : Chapter12NodeSeparationData M) :
    D.pointBlowupChain :=
by
  sorry

theorem chapter12_stable_model_contracts_insufficiently_marked_rational_components
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter12ExcellentDedekindBase S K}
    {C : Chapter01SmoothProperCurveOverField K} {V : S.Opens}
    {M₀ : Chapter12SemistableOpenModel B C V}
    (M : Chapter12MarkedSemistableModel (B := B) (C := C) (V := V) M₀) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ V.toScheme),
      Nonempty (Chapter12StableContractionData
        (X := M₀.carrier) (Y := Y) (S := V.toScheme) M₀.structureMap g) := by
  sorry

/-! ### Algebraization warning -/

theorem chapter12_completed_local_model_requires_algebraization_input
    {S : Scheme.{u}} (D : Chapter12CompletedLocalModelInput S)
    (A : Chapter12AlgebraizedSemistableInput D) :
    Chapter12AlgebraizationInput D :=
  A.algebraization

theorem chapter12_common_domination_compares_algebraic_models
    {S : Scheme.{u}} {D : Chapter12CompletedLocalModelInput S}
    (A : Chapter12AlgebraizedSemistableInput D) :
    A.commonDomination := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter12
