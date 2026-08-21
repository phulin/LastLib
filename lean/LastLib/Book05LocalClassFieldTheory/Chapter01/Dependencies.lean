import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section04AbsoluteValueNormalizations
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section04TheFundamentalEquality
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section04TheValuationOfANorm
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section03ConstructingTheUnramifiedLift
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section03CleanDecomposition
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter01

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators Pointwise Topology WithZero IsMulCommutative

/-!
The first chapter fixes the book-facing local-field and reciprocity interfaces.
The valuation is written additively, while multiplicative groups are represented
by `Units`, matching the canonical norm and Galois APIs used later.
-/

/-- The valuation ring attached to the additive valuation used in the book. -/
abbrev Chapter01ValuationRing {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : ValuationSubring K :=
  v.toValuation.valuationSubring

/-- The maximal ideal of the book's valuation ring. -/
abbrev Chapter01MaximalIdeal {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Ideal (Chapter01ValuationRing v) :=
  IsLocalRing.maximalIdeal (Chapter01ValuationRing v)

/-- The residue field `𝓞/𝔪`. -/
abbrev Chapter01ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (Chapter01ValuationRing v)

/-- The canonical reduction map to the residue field. -/
def chapter01ResidueMap {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Chapter01ValuationRing v →+* Chapter01ResidueField v :=
  IsLocalRing.residue (Chapter01ValuationRing v)

/-- The multiplicative group of valuation-ring units. -/
abbrev Chapter01UnitGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  (Chapter01ValuationRing v)ˣ

/-- The units of the field obtained from valuation-ring units. -/
def chapter01UnitInclusion {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Chapter01UnitGroup v →* Kˣ :=
  Units.map (Chapter01ValuationRing v).subtype.toMonoidHom

/-- The normalized uniformizer predicate in valuation-ring coordinates. -/
def chapter01IsUniformizer {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Chapter01ValuationRing v) : Prop :=
  π ≠ 0 ∧ v (π : K) = (1 : WithTop ℤ)

/-- `Uⁿ = 1 + 𝔪ⁿ` on valuation-ring units. -/
abbrev Chapter01UnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup (Chapter01UnitGroup v) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
    (Chapter01ValuationRing v) n

/-- The same unit filtration transported to `Kˣ`. -/
def chapter01FieldUnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  (Chapter01UnitFiltration v n).map (chapter01UnitInclusion v)

/-- The transported principal-unit filtration is a neighborhood basis in the
canonical local-field topology. -/
def Chapter01FieldUnitFiltrationNeighborhoodBasis {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) [TopologicalSpace Kˣ] : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitFiltrationNeighborhoodBasis
    (chapter01FieldUnitFiltration v)

/-- The finite-residue, complete, discretely valued local-field condition. -/
def Chapter01LocalField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteAdditiveValuation v ∧
    Finite (Chapter01ResidueField v)

/-- A chosen local-field presentation records the notation `π` and `q`. -/
structure Chapter01LocalFieldData (K : Type*) [Field K] where
  valuation : AddValuation K (WithTop ℤ)
  local_field : Chapter01LocalField valuation
  [residue_finite : Finite (Chapter01ResidueField valuation)]
  uniformizer : Chapter01ValuationRing valuation
  uniformizer_spec : chapter01IsUniformizer valuation uniformizer
  residue_cardinality : ℕ
  residue_cardinality_eq :
    Nat.card (Chapter01ResidueField valuation) = residue_cardinality

/-- The residue cardinality `q` attached to a finite residue field. -/
noncomputable def chapter01ResidueCardinality {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : ℕ :=
  Nat.card (Chapter01ResidueField v)

/-- The field-level unit filtration, with `U⁰ = 𝓞ˣ` and
`Uⁿ = 1 + 𝔪ⁿ` for positive `n`. -/
def chapter01PrincipalUnitSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  if n = 0 then
    {x | ∃ u : Chapter01UnitGroup v, x = (u : K)}
  else
    {x | ∃ y : Chapter01ValuationRing v,
      y ∈ (Chapter01MaximalIdeal v) ^ n ∧ x = 1 + (y : K)}

/-- The valuation exact sequence `1 → 𝓞ˣ → Kˣ → ℤ → 0`. -/
def Chapter01ValuationExactSequence {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (ν : Kˣ →* Multiplicative ℤ) : Prop :=
  Function.Injective (chapter01UnitInclusion v) ∧
    Function.MulExact (chapter01UnitInclusion v) ν ∧ Function.Surjective ν

/-- Book-facing data for the normalized valuation coordinate. -/
structure Chapter01ValuationCoordinateData {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) where
  valuation : Kˣ →* Multiplicative ℤ
  exact : Chapter01ValuationExactSequence v valuation

/-- Finite separable extensions are the part of the algebraic closure used by
local class field theory. -/
def Chapter01FiniteSeparableExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  FiniteDimensional K L ∧ ∀ x : L, IsSeparable K x

/-- A finite purely inseparable extension is retained as a warning case, not
as a class-field-theoretic level. -/
def Chapter01PurelyInseparableExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop :=
  FiniteDimensional K L ∧ IsPurelyInseparable K L

/-- The fixed algebraic and separable closures used for embedded extensions. -/
abbrev Chapter01AlgebraicClosure (K : Type*) [Field K] := AlgebraicClosure K

abbrev Chapter01SeparableClosure (K : Type*) [Field K] :=
  separableClosure K (AlgebraicClosure K)

/-- An intermediate field is inside the chosen separable closure. -/
def chapter01InsideSeparableClosure {K : Type*} [Field K]
    (L : IntermediateField K (Chapter01AlgebraicClosure K)) : Prop :=
  L ≤ Chapter01SeparableClosure K

/-- The norm homomorphism on multiplicative groups. -/
noncomputable def chapter01NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

/-- The norm subgroup of `Kˣ`. -/
def chapter01NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (chapter01NormHom K L).range

/-- The finite norm quotient. -/
abbrev Chapter01NormQuotient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  Kˣ ⧸ chapter01NormSubgroup K L

/-- The quotient class of a field unit. -/
def chapter01NormQuotientMk
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) : Chapter01NormQuotient K L :=
  QuotientGroup.mk' (chapter01NormSubgroup K L) x

@[simp] theorem chapter01_mem_norm_subgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter01NormSubgroup K L ↔
      ∃ y : Lˣ, chapter01NormHom K L y = x := by
  rfl

/-- Open finite-index subgroups of a topological group. -/
abbrev Chapter01OpenFiniteIndexSubgroup
    (G : Type*) [Group G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ H.FiniteIndex}

/-! The source in §1.2 uses the topology-sensitive profinite completion.  The
abstract Mathlib completion below is indexed by all finite-index normal
subgroups, so it is deliberately kept separate from this open-indexed
diagram. -/

/-- Open finite-index normal subgroups of a topological group. -/
structure Chapter01OpenFiniteIndexNormalSubgroup
    (G : Type*) [Group G] [TopologicalSpace G]
    extends FiniteIndexNormalSubgroup G where
  isOpen : IsOpen (toSubgroup : Set G)

namespace Chapter01OpenFiniteIndexNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

instance (H : Chapter01OpenFiniteIndexNormalSubgroup G) :
    H.toSubgroup.Normal := H.isNormal'

instance (H : Chapter01OpenFiniteIndexNormalSubgroup G) :
    H.toSubgroup.FiniteIndex := H.isFiniteIndex'

instance : SetLike (Chapter01OpenFiniteIndexNormalSubgroup G) G where
  coe H := H.toSubgroup
  coe_injective A B h := by
    cases A with
    | mk A hA =>
      cases B with
      | mk B hB =>
        have hAB : A.toSubgroup = B.toSubgroup := by
          ext g
          exact Set.ext_iff.mp h g
        cases FiniteIndexNormalSubgroup.toSubgroup_injective hAB
        rfl

instance : PartialOrder (Chapter01OpenFiniteIndexNormalSubgroup G) :=
  .ofSetLike (Chapter01OpenFiniteIndexNormalSubgroup G) G

@[simp]
theorem mem_toSubgroup_iff {H : Chapter01OpenFiniteIndexNormalSubgroup G}
    {g : G} : g ∈ H.toSubgroup ↔ g ∈ H :=
  Iff.rfl

end Chapter01OpenFiniteIndexNormalSubgroup

noncomputable def chapter01OpenFiniteIndexDiagram
    (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Chapter01OpenFiniteIndexNormalSubgroup G ⥤ FiniteGrp where
  obj H := FiniteGrp.of (G ⧸ H.toSubgroup)
  map f := FiniteGrp.ofHom <|
    QuotientGroup.map _ _ (MonoidHom.id G) (by
      intro g hg
      exact f.le hg)
  map_id H := by
    ext ⟨g⟩
    rfl
  map_comp f g := by
    ext ⟨x⟩
    rfl

noncomputable def chapter01OpenFiniteIndexProfiniteDiagram
    (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Chapter01OpenFiniteIndexNormalSubgroup G ⥤ ProfiniteGrp :=
  chapter01OpenFiniteIndexDiagram G ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The topology-sensitive profinite completion over open finite-index
quotients. -/
noncomputable def chapter01OpenProfiniteCompletion
    (G : Type*) [CommGroup G] [TopologicalSpace G] : ProfiniteGrp :=
  ProfiniteGrp.limit (chapter01OpenFiniteIndexProfiniteDiagram G)

abbrev Chapter01OpenProfiniteCompletion
    (G : Type*) [CommGroup G] [TopologicalSpace G] : Type _ :=
  (chapter01OpenProfiniteCompletion G : Type _)

noncomputable def chapter01OpenProfiniteCompletionEtaFn
    (G : Type*) [CommGroup G] [TopologicalSpace G] (g : G) :
    Chapter01OpenProfiniteCompletion G :=
  ⟨fun H => QuotientGroup.mk g, by
    intro H K f
    rfl⟩

noncomputable def chapter01OpenProfiniteCompletionEta
    (G : Type*) [CommGroup G] [TopologicalSpace G] :
    G →* Chapter01OpenProfiniteCompletion G where
  toFun := chapter01OpenProfiniteCompletionEtaFn G
  map_one' := by
    apply ProfiniteGrp.limit_ext _
    intro H
    rfl
  map_mul' g h := by
    apply ProfiniteGrp.limit_ext _
    intro H
    rfl

noncomputable def chapter01OpenProfiniteCompletionProjection
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    (H : Chapter01OpenFiniteIndexNormalSubgroup G) :
    Chapter01OpenProfiniteCompletion G →* (G ⧸ H.toSubgroup) :=
  (((ProfiniteGrp.limitCone
      (chapter01OpenFiniteIndexProfiniteDiagram G)).π.app H).hom).toMonoidHom

@[simp]
theorem chapter01OpenProfiniteCompletionProjection_eta
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    (H : Chapter01OpenFiniteIndexNormalSubgroup G) (g : G) :
    chapter01OpenProfiniteCompletionProjection G H
        (chapter01OpenProfiniteCompletionEta G g) = QuotientGroup.mk g := by
  rfl

/-- The finite abelian levels in a chosen maximal abelian extension. -/
abbrev Chapter01FiniteAbelianIndex
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :=
  FiniteGaloisIntermediateField K KAb

/-- The maximality predicate for a chosen model of `Kᵃᵇ`. -/
def chapter01IsMaximalAbelianExtension
    (K : Type u) (KAb : Type v) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] : Prop :=
  ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L], Nonempty (L →ₐ[K] KAb)

/-- A chosen maximal abelian extension inside the fixed separable closure. -/
structure Chapter01MaximalAbelianExtensionData (K : Type*) [Field K] where
  extension : IntermediateField K (Chapter01AlgebraicClosure K)
  [abelian_galois_extension : IsAbelianGalois K extension]
  maximal : chapter01IsMaximalAbelianExtension K extension
  contained_in_separable_closure :
    extension ≤ Chapter01SeparableClosure K

/-- The finite Artin data needed to pass to an inverse limit. -/
structure Chapter01FiniteArtinSystem
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] where
  artin : ∀ L : Chapter01FiniteAbelianIndex K KAb, Kˣ →* Gal(L / K)
  surjective : ∀ L, Function.Surjective (artin L)
  kernel_eq_norm : ∀ L,
    (artin L).ker = chapter01NormSubgroup K L
  compatible :
    ∀ {L₁ L₂ : (FiniteGaloisIntermediateField K KAb)ᵒᵖ}
      (f : L₁ ⟶ L₂) (x : Kˣ),
      (finGaloisGroupMap f).hom (artin L₁.unop x) = artin L₂.unop x

/-- The canonical Galois inverse-limit identification. -/
noncomputable def chapter01AbelianGaloisLimitEquiv
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    Gal(KAb / K) ≃ₜ*
      ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb) :=
  InfiniteGalois.continuousMulEquivToLimit K KAb

/-- The abstract profinite completion of a group in the pinned Mathlib
interface.  It is indexed by all finite-index normal subgroups; the
topology-sensitive completion used by §1.2 is
`Chapter01OpenProfiniteCompletion`. -/
abbrev Chapter01ProfiniteCompletion (G : Type*) [Group G] : Type _ :=
  (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) : Type _)

/-- The geometric inverse of a homomorphism into a commutative group. -/
def chapter01GeometricInverseHom
    {G H : Type*} [Group G] [Group H] [IsMulCommutative H]
    (f : G →* H) : G →* H where
  toFun x := (f x)⁻¹
  map_one' := by simp
  map_mul' x y := by simp [map_mul, mul_comm]

end

end LastLib.Book05LocalClassFieldTheory.Chapter01
