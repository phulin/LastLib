import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/-!
## 13.1 The hypothesis ledger

The table is recorded as named capability predicates and bridge theorems.  A
negative entry is not encoded by weakening a positive hypothesis: the three
explicit examples below witness the boundaries that matter later.
-/

/-! ### The rows of the ledger -/

/-- The total quotient ring used componentwise by a reduced affine chart. -/
noncomputable def chapter13TotalRingOfFractions (R : Type u) [CommRing R] : Type u :=
  Localization R⁰

theorem chapter13_totalRingOfFractions_is_the_canonical_localization
    (R : Type u) [CommRing R] :
    chapter13TotalRingOfFractions R = Localization R⁰ :=
  rfl

/- A reduced ring supplies this total-quotient construction, but no choice of
normalization or separation of branches is hidden in the definition. -/
def chapter13ReducedAffineLedger (R : Type u) [CommRing R] : Prop :=
  _root_.IsReduced R

def chapter13NormalAffineLedger (R : Type u) [CommRing R] : Prop :=
  chapter13NormalRing R

theorem chapter13_normal_affine_ledger_is_componentwise_integrally_closed
    (R : Type u) [CommRing R] (hR : chapter13NormalAffineLedger R) :
    ∀ (p : Ideal R) (hp : p.IsPrime),
      letI : p.IsPrime := hp
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p) := by
  exact hR

def chapter13RegularAffineLedger (R : Type u) [CommRing R] : Prop :=
  IsRegularRing R

def chapter13SmoothLedger {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Smooth f

def chapter13JapaneseLedger (R : Type u) [CommRing R] : Prop :=
  chapter13JapaneseDomain R

def chapter13NagataLedger (X : Scheme.{u}) : Prop :=
  Chapter13NagataScheme X

def chapter13ExcellentLedger (X : Scheme.{u}) : Prop :=
  Chapter13ExcellentScheme X

def chapter13ProperLedger {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsProper f

def chapter13ProjectiveLedger {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  chapter13ProjectiveMorphism f

def chapter13FlatDedekindLedger {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ _hS : Chapter13DedekindScheme S, ∃ _ : Flat f,
    chapter13NoVerticalTorsion f ∧
      Nonempty (Chapter13WellBehavedFibers f)

theorem chapter13_smooth_supplies_flat_and_geometrically_regular_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    Flat f ∧ Chapter13GeometricallyRegularFibers f := by
  sorry

theorem chapter13_nagata_supplies_finite_normalization_for_finite_type_maps
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (hX : IsReduced X) (hY : Chapter13NagataScheme Y) :
    IsFinite (chapter13NormalizationMap f) := by
  sorry

theorem chapter13_excellent_supplies_nagata_and_surface_resolution
    {X : Scheme.{u}} (hX : Chapter13ExcellentScheme X)
    (hDim : Chapter13SurfaceDimensionBound X) :
    Chapter13NagataScheme X ∧ Chapter13SurfaceResolutionCapability X := by
  exact ⟨chapter13_excellent_implies_nagata hX,
    chapter13_excellent_implies_surface_resolution hX hDim⟩

theorem chapter13_proper_supplies_valuative_extension_and_universal_closedness
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    Chapter13ValuativeExtension f ∧ UniversallyClosed f := by
  exact ⟨chapter13_proper_has_valuative_extension f, inferInstance⟩

theorem chapter13_projective_supplies_properness_and_polarization
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hproj : chapter13ProjectiveMorphism f) :
    IsProper f ∧ chapter13ProjectiveHasPolarization f := by
  exact ⟨chapter13_projective_implies_proper hproj,
    chapter13_projective_has_ample_polarization hproj⟩

theorem chapter13_flatness_does_not_entail_reduced_fibers :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Chapter13DedekindScheme S → Flat f → Chapter13ReducedFibers f) := by
  sorry

theorem chapter13_flat_over_dedekind_supplies_the_flat_ledger
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter13DedekindScheme S) [Flat f] :
    chapter13FlatDedekindLedger f := by
  sorry

theorem chapter13_reduced_does_not_entail_componentwise_normality :
    ¬ (∀ {R : Type u} [CommRing R],
      _root_.IsReduced R → chapter13NormalRing R) := by
  sorry

theorem chapter13_japanese_does_not_entail_the_nagata_prime_quotient_condition :
    ¬ (∀ {R : Type u} [CommRing R],
      chapter13JapaneseDomain R → chapter13NagataRing R) := by
  sorry

theorem chapter13_nagata_does_not_entail_surface_resolution :
    ¬ (∀ {X : Scheme.{u}},
      Chapter13NagataScheme X → Chapter13SurfaceResolutionCapability X) := by
  sorry

theorem chapter13_excellent_does_not_entail_smoothness_of_an_arbitrary_map :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Chapter13ExcellentScheme X → Smooth f) := by
  sorry

theorem chapter13_smooth_does_not_entail_properness :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S), Smooth f → IsProper f) := by
  sorry

theorem chapter13_proper_does_not_entail_a_projective_presentation :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      IsProper f → chapter13ProjectiveMorphism f) := by
  sorry

theorem chapter13_projective_does_not_entail_regular_normal_total_space :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      chapter13ProjectiveMorphism f →
        Chapter13RegularScheme X ∧ Chapter13NormalScheme X) := by
  sorry

theorem chapter13_regular_does_not_entail_reduced_special_fibers :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Chapter13RegularScheme X → Chapter13ReducedFibers f) := by
  sorry

/-! ### Normal but not regular: `k[x,y,z]/(xy-z^2)` -/

abbrev chapter13QuadricConePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 3) k

def chapter13QuadricConeEquationIdeal (k : Type u) [CommRing k] :
    Ideal (chapter13QuadricConePolynomialRing k) :=
  Ideal.span ({
    MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3) -
      MvPolynomial.X (2 : Fin 3) ^ 2
  } : Set (chapter13QuadricConePolynomialRing k))

abbrev chapter13QuadricConeRing (k : Type u) [CommRing k] :=
  chapter13QuadricConePolynomialRing k ⧸ chapter13QuadricConeEquationIdeal k

abbrev chapter13QuadricCone (k : Type u) [CommRing k] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (chapter13QuadricConeRing k))

def chapter13QuadricConeVertexIdeal (k : Type u) [CommRing k] :
    Ideal (chapter13QuadricConeRing k) :=
  Ideal.map (Ideal.Quotient.mk (chapter13QuadricConeEquationIdeal k))
    (Ideal.span ({
      MvPolynomial.X (0 : Fin 3),
      MvPolynomial.X (1 : Fin 3),
      MvPolynomial.X (2 : Fin 3)
    } : Set (chapter13QuadricConePolynomialRing k)))

noncomputable def chapter13QuadricConeVertex (k : Type u) [Field k] :
    PrimeSpectrum (chapter13QuadricConeRing k) :=
  { asIdeal := chapter13QuadricConeVertexIdeal k
    isPrime := by sorry }

def chapter13QuadricConeIsNormal (k : Type u) [Field k] : Prop :=
  Chapter13NormalScheme (chapter13QuadricCone k)

def chapter13QuadricConeIsRegularAtVertex (k : Type u) [Field k] : Prop :=
  chapter13RegularAt (chapter13QuadricCone k) (chapter13QuadricConeVertex k)

theorem chapter13_quadric_cone_is_normal_not_regular_at_vertex
    (k : Type u) [Field k] (hchar : (2 : k) ≠ 0) :
    chapter13QuadricConeIsNormal k ∧
      ¬ chapter13QuadricConeIsRegularAtVertex k := by
  sorry

/-! ### Regular total space but non-smooth nodal fiber: `R[x,y]/(xy-π)` -/

abbrev chapter13NodePolynomialRing (R : Type u) [CommRing R] :=
  MvPolynomial (Fin 2) R

def chapter13NodeEquationIdeal (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter13NodePolynomialRing R) :=
  Ideal.span ({
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C π
  } : Set (chapter13NodePolynomialRing R))

abbrev chapter13NodeRing (R : Type u) [CommRing R] (π : R) :=
  chapter13NodePolynomialRing R ⧸ chapter13NodeEquationIdeal R π

abbrev chapter13NodeSurface (R : Type u) [CommRing R] (π : R) : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (chapter13NodeRing R π))

def chapter13NodeBaseRingHom (R : Type u) [CommRing R] (π : R) :
    R →+* chapter13NodeRing R π :=
  (Ideal.Quotient.mk (chapter13NodeEquationIdeal R π)).comp
    (MvPolynomial.C : R →+* chapter13NodePolynomialRing R)

def chapter13NodeStructureMap (R : Type u) [CommRing R] (π : R) :
    chapter13NodeSurface R π ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) :=
  Scheme.Spec.map (CommRingCat.ofHom (chapter13NodeBaseRingHom R π)).op

abbrev chapter13NodeSpecialFiberRing (R : Type u) [CommRing R] (π : R) :=
  chapter13NodeRing R π ⧸
    Ideal.map (Ideal.Quotient.mk (chapter13NodeEquationIdeal R π))
      (Ideal.span ({MvPolynomial.C π} : Set (chapter13NodePolynomialRing R)))

def chapter13NodeSpecialFiberEquation (R : Type u) [CommRing R] (π : R) : Prop :=
  ∃ x y : chapter13NodeSpecialFiberRing R π,
    x * y = 0 ∧ x ≠ 0 ∧ y ≠ 0

theorem chapter13_node_total_space_regular_but_structure_map_not_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : ¬ IsUnit π) (hπ0 : π ≠ 0)
    (hπ_uniformizer : Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R) :
    Chapter13RegularScheme (chapter13NodeSurface R π) ∧
      ¬ Smooth (chapter13NodeStructureMap R π) ∧
      chapter13NodeSpecialFiberEquation R π := by
  sorry

/-! ### Purely inseparable scalar extension can be nonreduced -/

structure Chapter13PurelyInseparableNonreducedBaseChange where
  base : Type u
  [base_field : Field base]
  extension : Type u
  [extension_field : Field extension]
  [base_algebra : Algebra base extension]
  [purely_inseparable : IsPurelyInseparable base extension]
  tensor_not_reduced : ¬ _root_.IsReduced (TensorProduct base extension extension)

theorem chapter13_purely_inseparable_scalar_extension_can_be_nonreduced :
    Nonempty Chapter13PurelyInseparableNonreducedBaseChange := by
  sorry

/-! ### Explicit boundary predicates for later users -/

def chapter13NormalDoesNotSupplyRegularityAtClosedPoints
    {X : Scheme.{u}} (_hX : Chapter13NormalScheme X) (x : X) : Prop :=
  Chapter13NormalScheme X ∧ ¬ chapter13RegularAt X x

def chapter13RegularDoesNotSupplySmoothFibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    (_hX : Chapter13RegularScheme X) : Prop :=
  Chapter13RegularScheme X ∧ ¬ Smooth f

def chapter13FlatDoesNotSupplyReducedFibers
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] : Prop :=
  ¬ Chapter13ReducedFibers f

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter13
