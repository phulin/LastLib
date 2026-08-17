import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section06FrobeniusAndRestriction
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section04ImperfectResidueFields
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section06TameBoundary
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open Set
open scoped BigOperators Pointwise WithZero

/-!
Shared interfaces for Chapter 1, “From inertia to depth”.  The valuation-ring
and residue-action abbreviations deliberately point at the canonical Book 2
objects.  The new lower-numbering wrapper is the only indexing convention
introduced here: Book 2's congruence level `n` is the source's lower group
`G_(n-1)`.
-/

universe u v

/-- The valuation ring attached to a multiplicative valuation. -/
abbrev chapter01ValuationRing {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  v.valuationSubring

/-- The maximal ideal of the chosen valuation ring. -/
abbrev chapter01MaximalIdeal {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    Ideal (chapter01ValuationRing v) :=
  IsLocalRing.maximalIdeal (chapter01ValuationRing v)

/-- The residue field of the chosen valuation ring. -/
abbrev chapter01ResidueField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  IsLocalRing.ResidueField (chapter01ValuationRing v)

/-- Completeness and rank-one discreteness for a normalized valuation. -/
abbrev chapter01CompleteDiscreteValuation {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteDiscreteValuation K v

/-- A chosen generator of the maximal ideal. -/
abbrev chapter01IsUniformizer {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (π : chapter01ValuationRing v) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01IsUniformizer v π

/-- The exact normalized additive restriction formula from the preceding book. -/
abbrev chapter01ValuationRestrictionScale
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ValuationRestrictionScale
    vK vL e

/-- The chosen place on an extension is the one induced by the base valuation. -/
abbrev chapter01SamePlace
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01SamePlace vK vL

/-- The ideal-theoretic ramification index attached to two chosen branches. -/
abbrev chapter01RamificationIndex
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [Valuation.HasExtension vK vL] : ℕ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
    vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring)

/-- The residue degree attached to two chosen branches. -/
abbrev chapter01ResidueDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [Valuation.HasExtension vK vL] : ℕ :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
    vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring)

/-- The degree equality needed whenever a group order is identified with `e`. -/
def chapter01Defectless
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [Valuation.HasExtension vK vL] : Prop :=
  Module.finrank K L = chapter01RamificationIndex vK vL * chapter01ResidueDegree vK vL

/-- The ambient finite Galois group. -/
abbrev chapter01GaloisGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L] := Gal(L / K)

/-- The decomposition group of the selected valuation branch. -/
abbrev chapter01DecompositionGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (chapter01GaloisGroup K L) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A

/-- The inertia subgroup inside the selected decomposition group. -/
abbrev chapter01InertiaGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (chapter01DecompositionGroup K A) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A

/-- The same inertia subgroup mapped into the ambient Galois group. -/
abbrev chapter01InertiaGroupInG
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (chapter01GaloisGroup K L) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG K A

/-- The canonical action on the residue field of the selected branch. -/
abbrev chapter01ResidueAction
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter01DecompositionGroup K A →* RingAut (IsLocalRing.ResidueField A) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ResidueAction K A

/-- Automorphisms of a residue extension fixing the base residue field. -/
abbrev chapter01ResidueAutomorphismsOver
    (k l : Type*) [CommRing k] [CommRing l] [Algebra k l] : Subgroup (RingAut l) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ResidueAutomorphismsOver k l

/-- The residue action restricted to automorphisms over a specified base. -/
def chapter01ResidueActionOverBase
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (k : Type*) [CommRing k]
    [Algebra k (IsLocalRing.ResidueField A)]
    (hbase : ∀ σ : chapter01DecompositionGroup K A, ∀ x : k,
      chapter01ResidueAction K A σ (algebraMap k (IsLocalRing.ResidueField A) x) =
        algebraMap k (IsLocalRing.ResidueField A) x) :
    chapter01DecompositionGroup K A →*
      chapter01ResidueAutomorphismsOver k (IsLocalRing.ResidueField A) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ResidueActionOverBase
    K A k hbase

/-- A book-facing package for a residue action and its inertia kernel. -/
structure Chapter01ResidueActionData
    (K L k : Type*) [Field K] [Field L] [CommRing k]
    [Algebra K L] (A : ValuationSubring L)
    [Algebra k (IsLocalRing.ResidueField A)] where
  action : chapter01DecompositionGroup K A →*
    RingAut (IsLocalRing.ResidueField A)
  fixes_base : ∀ σ : chapter01DecompositionGroup K A, ∀ x : k,
    action σ (algebraMap k (IsLocalRing.ResidueField A) x) =
      algebraMap k (IsLocalRing.ResidueField A) x
  kernel_eq_inertia : chapter01InertiaGroup K A = MonoidHom.ker action

/-- The source's first cotangent layer `𝔪/𝔪²`. -/
abbrev chapter01CotangentLine
    {L : Type*} [Field L] (A : ValuationSubring L) : Type _ :=
  (IsLocalRing.maximalIdeal A : Ideal A) ⧸
    (IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A (IsLocalRing.maximalIdeal A : Ideal A)) :
      Submodule A (IsLocalRing.maximalIdeal A : Ideal A))

/-- Book 2's congruence filtration, reindexed as lower ramification groups. -/
def chapter01LowerRamificationGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ) : Subgroup (chapter01DecompositionGroup K A) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup K A (i + 1)

/-- The first positive lower group, i.e. wild inertia in the separable-residue case. -/
abbrev chapter01WildInertiaGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (chapter01DecompositionGroup K A) :=
  chapter01LowerRamificationGroup K A 1

/-- The lower groups mapped to the ambient Galois group. -/
def chapter01WildInertiaGroupInG
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (chapter01GaloisGroup K L) :=
  (chapter01WildInertiaGroup K A).map (Subgroup.subtype _)

/-- The characteristic exponent of a residue field. -/
def chapter01CharacteristicExponent (k : Type*) [Ring k] : ℕ := ringExpChar k

/-- The numerical prime-to-`p` condition. -/
def chapter01TameIndex (k : Type*) [Ring k] (e : ℕ) : Prop :=
  Nat.Coprime e (chapter01CharacteristicExponent k)

/-- Tameness for a finite residue-field profile, including separability. -/
def chapter01TameExtension
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    (e : ℕ) : Prop :=
  Algebra.IsSeparable k l ∧ chapter01TameIndex k e

/-- Wildness in the source's explicitly separable-residue convention. -/
def chapter01WildExtension
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    (e : ℕ) : Prop :=
  Algebra.IsSeparable k l ∧ ¬chapter01TameIndex k e

/-- The fixed field of a subgroup of the finite Galois group. -/
abbrev chapter01FixedField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (chapter01GaloisGroup K L)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-- A finite subgroup has `p`-primary order in the sense used below. -/
def chapter01PPrimaryOrder {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) : Prop :=
  ∃ r : ℕ, Nat.card H = p ^ r

/-- The finite-field Frobenius conventions used by the later group presentation. -/
noncomputable def chapter01ArithmeticFrobenius
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06ArithmeticFrobenius k l

noncomputable def chapter01GeometricFrobenius
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06GeometricFrobenius k l

/-- A residue Frobenius coset in a ramified quotient. -/
def chapter01ArithmeticFrobeniusCoset
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06RamifiedGaloisReduction
      G H I) (φ : H) : Set G :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06ArithmeticFrobeniusCoset I D φ

/-- A presentation records the cyclic ambiguity in the chosen Frobenius lift.
The uniqueness of its residue class and the compatibility congruence are
exposed by the Section 1.6 lemmas. -/
structure Chapter01FiniteTameGroupPresentation
    (G : Type*) [Group G] [Finite G]
    (I : Subgroup G) [I.Normal] (q e f : ℕ) where
  frobenius : G
  tameGenerator : G
  tameGenerator_mem : tameGenerator ∈ I
  tameGenerator_order_positive : 0 < e
  tameGenerator_order : orderOf tameGenerator = e
  residue_degree_positive : 0 < f
  residue_card_positive : 0 < q
  inertia_generated : Subgroup.zpowers tameGenerator = I
  group_generated :
    Subgroup.closure ({frobenius, tameGenerator} : Set G) = ⊤
  conjugation : frobenius * tameGenerator * frobenius⁻¹ = tameGenerator ^ q
  frobenius_power : ∃ a : ℕ, frobenius ^ f = tameGenerator ^ a

end

end LastLib.Book03RamificationTheory.Chapter01
