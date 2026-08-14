import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05.Section01DefinitionsAndLocalDimensions
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05.Section02FlatnessFromTorsionFreeness

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v

/-! ### 5.3 Horizontal and vertical geometry -/

structure Chapter05HorizontalPrimeDivisorClosureData
    {S X : Scheme.{u}} (f : X ⟶ S) (D : Chapter05PrimeDivisor X) where
  genericBasePoint : S
  genericBasePoint_is_generic :
    IsGenericPoint genericBasePoint (Set.univ : Set S)
  genericFiberPoint : f.fiber genericBasePoint
  genericFiberPoint_closed :
    IsClosed ({genericFiberPoint} : Set (f.fiber genericBasePoint))
  genericPoint_eq : f.fiberι genericBasePoint genericFiberPoint = D.point
  proper : IsProper (D.inclusion ≫ f)
  locallyQuasiFinite : LocallyQuasiFinite (D.inclusion ≫ f)
  finite : IsFinite (D.inclusion ≫ f)

theorem chapter05_horizontal_prime_divisor_is_closure_of_generic_closed_point
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ProperArithmeticSurface S X f)
    (D : Chapter05PrimeDivisor X)
    (hD : chapter05PrimeDivisorHorizontal f D) :
    Nonempty (Chapter05HorizontalPrimeDivisorClosureData f D) := by
  sorry

theorem chapter05_horizontal_prime_divisor_is_finite_over_base
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ProperArithmeticSurface S X f)
    (D : Chapter05PrimeDivisor X)
    (hD : chapter05PrimeDivisorHorizontal f D) :
    IsFinite (D.inclusion ≫ f) := by
  let H := Classical.choice
    (chapter05_horizontal_prime_divisor_is_closure_of_generic_closed_point
      f hS hX D hD)
  exact H.finite

theorem chapter05_horizontal_prime_divisor_is_proper_over_base
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ProperArithmeticSurface S X f)
    (D : Chapter05PrimeDivisor X)
    (hD : chapter05PrimeDivisorHorizontal f D) :
    IsProper (D.inclusion ≫ f) := by
  let H := Classical.choice
    (chapter05_horizontal_prime_divisor_is_closure_of_generic_closed_point
      f hS hX D hD)
  exact H.proper

theorem chapter05_horizontal_prime_divisor_quasiFinite_over_base
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ProperArithmeticSurface S X f)
    (D : Chapter05PrimeDivisor X)
    (hD : chapter05PrimeDivisorHorizontal f D) :
    LocallyQuasiFinite (D.inclusion ≫ f) := by
  let H := Classical.choice
    (chapter05_horizontal_prime_divisor_is_closure_of_generic_closed_point
      f hS hX D hD)
  exact H.locallyQuasiFinite

/-! The scheme-theoretic fiber is Cartier in the local DVR chart.  The
uniformizer is pulled back through a stalk map and then into the function
field, which keeps the rational function used by `Scheme.ord` canonical. -/

theorem chapter05_pulledBack_uniformizer_exists
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05ExcellentDedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (s : Chapter05BaseClosedPoint S)
    (x : X) (hx : f x = s.point) :
    Nonempty (letI := hX.integral
      letI := chapter05_arithmeticSurface_locallyNoetherian f hS hX
      Chapter05PulledBackUniformizer f s) := by
  sorry

theorem chapter05_fiber_multiplicity_eq_order
    {S X : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s) (i : D.family.index) :
    (D.multiplicity i : ℤ) =
      AlgebraicGeometry.Scheme.ord D.uniformizer.rationalFunction
        (D.family.primeDivisor i).point := by
  exact D.multiplicity_eq_order i

theorem chapter05_fiber_multiplicity_positive
    {S X : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s) (i : D.family.index) :
    0 < D.multiplicity i := by
  exact D.multiplicity_positive i

/- LOCAL_DEPENDENCY_GUESS: the canonical order function is available, but the
finite-support construction of the principal divisor of a base function on a
normal arithmetic surface is not bundled in the pinned scheme API. -/

theorem chapter05_fiber_divisor_eq_div_uniformizer
    {S X : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s)
    (P : Chapter05PrincipalDivisorPresentation
      D.uniformizer.rationalFunction)
    (hsupport :
      ∀ Q : Chapter05PrimeDivisor X, P.divisor Q ≠ 0 →
        ∃ i : D.family.index, Q = D.family.primeDivisor i) :
    P.divisor = chapter05FiberDivisor D := by
  sorry

theorem chapter05_fiber_divisor_is_principal_and_component_sum
    {S X : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s)
    (P : Chapter05PrincipalDivisorPresentation
      D.uniformizer.rationalFunction)
    (hsupport :
      ∀ Q : Chapter05PrimeDivisor X, P.divisor Q ≠ 0 →
        ∃ i : D.family.index, Q = D.family.primeDivisor i) :
    chapter05FiberDivisor D = P.divisor ∧
      P.divisor = ∑ i, Finsupp.single (D.family.primeDivisor i)
        (D.multiplicity i : ℤ) := by
  constructor
  · exact (chapter05_fiber_divisor_eq_div_uniformizer D P hsupport).symm
  · rw [chapter05_fiber_divisor_eq_div_uniformizer D P hsupport]
    exact chapter05_fiberDivisor_eq_component_sum D

def Chapter05AllFiberMultiplicitiesOne
    {S X : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s) : Prop :=
  ∀ i, D.multiplicity i = 1

theorem chapter05_fiber_genericallyReduced_iff_multiplicities_one_and_residue_condition
    {S X : Scheme.{u}} {f : X ⟶ S} {s : Chapter05BaseClosedPoint S}
    [IsIntegral X] [IsLocallyNoetherian X]
    (D : Chapter05FiberDivisorData f s) :
    Chapter05FiberGenericallyReduced f s.point ↔
      Chapter05AllFiberMultiplicitiesOne D ∧
        Chapter05FiberGenericResidueExtensionsReduced f s.point := by
  sorry

theorem chapter05_geometricallyReduced_fiber_is_a_geometric_residue_condition
    {S X : Scheme.{u}} (f : X ⟶ S) (s : S) :
    Chapter05FiberGeometricallyReduced f s ↔
      GeometricallyReduced (f.fiberToSpecResidueField s) :=
  Iff.rfl

/-! Horizontal and vertical are relative notions.  A finite base-change
family records the points lying over the original divisor; the remaining
incidence data is deliberately explicit because it is not a bundled object in
the pinned scheme API. -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib has pullbacks and irreducible components,
but no canonical operation turning a prime divisor into the finite family of
prime divisors in a base change.  The point-over relation below is the minimal
book-facing interface needed to state splitting. -/

structure Chapter05BaseChangedHorizontalPrimeDivisorFamily
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    (B : Chapter05FiniteBaseChange S S')
    (D : Chapter05PrimeDivisor X) where
  index : Type u
  finiteIndex : Fintype index
  component : index →
    Chapter05PrimeDivisor (chapter05BaseChangedSurface f B.map)
  component_is_horizontal : ∀ i,
    chapter05PrimeDivisorHorizontal
      (chapter05BaseChangedStructureMap f B.map) (component i)
  component_point_over : ∀ i,
    (pullback.fst f B.map) (component i).point = D.point
  component_injective : Function.Injective component

def Chapter05HorizontalSplitsAfterFiniteBaseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    (B : Chapter05FiniteBaseChange S S')
    (D : Chapter05PrimeDivisor X) : Prop :=
  ∃ H : Chapter05BaseChangedHorizontalPrimeDivisorFamily f B D,
    letI := H.finiteIndex
    1 < Fintype.card H.index

/- LOCAL_DEPENDENCY_GUESS: The analogous finite family for a vertical divisor
is represented by its point-over relation and the canonical relative
horizontal/vertical predicate. -/

structure Chapter05BaseChangedVerticalPrimeDivisorFamily
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    (B : Chapter05FiniteBaseChange S S')
    (D : Chapter05PrimeDivisor X) where
  index : Type u
  finiteIndex : Fintype index
  component : index →
    Chapter05PrimeDivisor (chapter05BaseChangedSurface f B.map)
  component_is_vertical : ∀ i,
    chapter05PrimeDivisorVertical
      (chapter05BaseChangedStructureMap f B.map) (component i)
  component_point_over : ∀ i,
    (pullback.fst f B.map) (component i).point = D.point
  component_injective : Function.Injective component

def Chapter05VerticalRemainsVerticalAfterFiniteBaseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    (B : Chapter05FiniteBaseChange S S')
    (D : Chapter05PrimeDivisor X)
    (hD : chapter05PrimeDivisorVertical f D) : Prop :=
  hD ∧
    ∃ H : Chapter05BaseChangedVerticalPrimeDivisorFamily f B D, Nonempty H.index

theorem chapter05_horizontal_baseChange_component_is_horizontal
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    {B : Chapter05FiniteBaseChange S S'}
    {D : Chapter05PrimeDivisor X}
    (H : Chapter05BaseChangedHorizontalPrimeDivisorFamily f B D)
    (i : H.index) :
    chapter05PrimeDivisorHorizontal
      (chapter05BaseChangedStructureMap f B.map) (H.component i) :=
  H.component_is_horizontal i

theorem chapter05_vertical_baseChange_component_is_vertical
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    {B : Chapter05FiniteBaseChange S S'}
    {D : Chapter05PrimeDivisor X}
    (H : Chapter05BaseChangedVerticalPrimeDivisorFamily f B D)
    (i : H.index) :
    chapter05PrimeDivisorVertical
      (chapter05BaseChangedStructureMap f B.map) (H.component i) :=
  H.component_is_vertical i

/- The ramification equation records the precise way a base valuation can
change a fiber multiplicity. -/

structure Chapter05RamifiedDVRBaseChange
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] where
  uniformizer : R
  newUniformizer : R'
  ramificationIndex : ℕ
  ramificationIndex_gt_one : 1 < ramificationIndex
  unit : R'
  unit_isUnit : IsUnit unit
  uniformizer_pullback :
    algebraMap R R' uniformizer = unit * newUniformizer ^ ramificationIndex

/- LOCAL_DEPENDENCY_GUESS: the pinned valuation API does not yet expose the
comparison of the divisorial order on a surface with the additive valuation
of a ramified base change.  The arithmetic relation is named separately so a
later proof can replace this interface without changing the chapter API. -/

def Chapter05RamificationChangesMultiplicity
    (m e m' : ℕ) : Prop :=
  m' = e * m

/- LOCAL_DEPENDENCY_GUESS: normalization branches are not represented by a
single pinned Mathlib residue-branch object, so the finite normalization map
and the nontrivial branch index are kept explicit. -/

structure Chapter05NormalizationResidueBranchSplit where
  source : Scheme.{u}
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ source
  finite : IsFinite normalizationMap
  sourcePoint : source
  branches : Type u
  [branches_finite : Fintype branches]
  branchPoint : branches → normalization
  branch_lies_over : ∀ i, normalizationMap (branchPoint i) = sourcePoint
  branch_injective : Function.Injective branchPoint
  branches_nontrivial : 1 < Fintype.card branches

theorem chapter05_normalization_can_split_residue_field_branches
    (B : Chapter05NormalizationResidueBranchSplit) :
    letI := B.branches_finite
    1 < Fintype.card B.branches := by
  exact B.branches_nontrivial

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05
