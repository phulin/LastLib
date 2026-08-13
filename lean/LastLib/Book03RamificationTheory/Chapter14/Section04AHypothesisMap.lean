import LastLib.Book03RamificationTheory.Chapter14.Core
import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section05TraceAndNormUnderFiniteFieldFrobenius
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section01TheStructuralQuestion
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section06CompactnessAndLocalCompactness
import LastLib.Book03RamificationTheory.Chapter11.Section02ArtinsIntegrality
import Mathlib.FieldTheory.Perfect
import Mathlib.RepresentationTheory.Maschke

namespace LastLib.Book03RamificationTheory.Chapter14

noncomputable section

open Polynomial
open scoped BigOperators

/-!
## 14.4. A hypothesis map
-/

/- Completeness, discreteness, and the finite-local-extension package are
kept separate from residue separability. -/
def chapter14CompleteDiscreteValuationRingBoundary
    (A : Type*) [CommRing A] [IsLocalRing A] [IsDomain A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A ∧
    IsDiscreteValuationRing A

def chapter14FiniteFreeExtensionBoundary
    (A B : Type*) [Semiring A] [AddCommMonoid B] [Module A B] : Prop :=
  Module.Finite A B ∧ Module.Free A B

def chapter14UniqueValuationExtensionBoundary
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (w : Valuation L Γ) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension v w

abbrev Chapter14FiniteCompleteLocalExtension :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Chapter09FiniteLocalExtension

/- SOURCE_ISSUE: The source's bullet says, “Completeness and discreteness give
unique valuation extension, finite freeness, and $[L:K]=ef$.”  The degree
part is not valid for arbitrary imperfect-residue extensions because of the
defect.  This corrected interface requires the perfect base residue field,
exactly as the earlier Chapter 9 theorem does. -/
theorem chapter14_perfect_residue_degree_formula
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)]
    [PerfectField (IsLocalRing.ResidueField A)]
    [Chapter14FiniteCompleteLocalExtension A B K L] :
    Module.finrank K L =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex A B
        (IsLocalRing.maximalIdeal B) *
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree A B
          (IsLocalRing.maximalIdeal B) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_local_degree_formula
    A B K L

/- Separability of the field extension is the trace/different boundary, while
Galois symmetry is the separate boundary for field-valued ramification groups. -/
def chapter14SeparableFieldBoundary (K L : Type*) [Field K] [Field L]
    [Algebra K L] : Prop :=
  Algebra.IsSeparable K L

def chapter14GaloisSymmetryBoundary (K L : Type*) [Field K] [Field L]
    [Algebra K L] : Prop :=
  IsGalois K L

def chapter14ClassicalGaloisConductorBoundary (residueSeparable : Prop) : Prop :=
  residueSeparable

/- The finite-Galois conductor formulas are rational fixed-space formulas;
this definition deliberately has no integrality hypothesis. -/
def chapter14RationalFixedSpaceConductor
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12RamificationProfile G)
    (ρ : Representation ℚ G V) : ℚ :=
  LastLib.Book03RamificationTheory.Chapter12.chapter12ArtinConductorSum P ρ

@[simp] theorem chapter14RationalFixedSpaceConductor_def
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12RamificationProfile G)
    (ρ : Representation ℚ G V) :
    chapter14RationalFixedSpaceConductor P ρ =
      LastLib.Book03RamificationTheory.Chapter12.chapter12ArtinConductorSum P ρ :=
  rfl

def chapter14RationalFixedSpaceSwanConductor
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12RamificationProfile G)
    (ρ : Representation ℚ G V) : ℚ :=
  LastLib.Book03RamificationTheory.Chapter12.chapter12SwanConductorSum P ρ

@[simp] theorem chapter14RationalFixedSpaceSwanConductor_def
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12RamificationProfile G)
    (ρ : Representation ℚ G V) :
    chapter14RationalFixedSpaceSwanConductor P ρ =
      LastLib.Book03RamificationTheory.Chapter12.chapter12SwanConductorSum P ρ :=
  rfl

/- LOCAL_DEPENDENCY_GUESS: under separable residue, the group-order and Hilbert-formula interfaces
are explicit.  A later reconciliation can replace this record by the
valuation-derived one without changing its consumers. -/
def chapter14HilbertDifferentExponent
    {G : Type*} [Group G] [Fintype G]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12RamificationProfile G) : ℕ :=
  Finset.sum (Finset.range (P.bound + 1)) (fun i => Nat.card (P.lower i) - 1)

structure Chapter14SeparableResidueRamificationData
    {G : Type*} [Group G] [Fintype G]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12RamificationProfile G)
    (e d : ℕ) where
  residue_separable : Prop
  zeroth_group_card : Nat.card P.inertia = e
  different_exponent : d = chapter14HilbertDifferentExponent P

def chapter14LocalMonogenicity
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Prop :=
  ∃ α : B, ∃ f : A[X],
    LastLib.Book03RamificationTheory.Chapter07.chapter07MonogenicPresentation
      A B K L α f

def chapter14SeparableResidueMonogenicityStatement
    (residueSeparable : Prop) (A B K L : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Prop :=
  residueSeparable → chapter14LocalMonogenicity A B K L

structure Chapter14PerfectResidueConductorContext
    (κ : Type*) [Field κ] [PerfectField κ]
    {G : Type*}
    [Fintype G] [Group G]
    (D : LastLib.Book03RamificationTheory.Chapter11.Chapter11RamificationData G) where
  residue_separable : D.residue_separable
  residue_perfect : D.residue_perfect
  ramification_character_input :
    LastLib.Book03RamificationTheory.Chapter11.Chapter11RamificationCharacterInput D

/- Artin integrality and Hasse--Arf retain the stronger perfectness and the
virtual-character input required by the preceding Chapter 11 API. -/
theorem chapter14_perfect_residue_artin_integrality
    {κ k G V : Type*} [Field κ] [PerfectField κ]
    [Field k] [CharZero k] [Fintype G] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (D : LastLib.Book03RamificationTheory.Chapter11.Chapter11RamificationData G)
    (C : Chapter14PerfectResidueConductorContext κ D)
    (ρ : Representation k G V) :
    LastLib.Book03RamificationTheory.Chapter11.Chapter11NonnegativeInteger
      (LastLib.Book03RamificationTheory.Chapter11.chapter11ArtinConductor D ρ) := by
  sorry

theorem chapter14_perfect_residue_hasse_arf
    {κ G : Type*} [Field κ] [PerfectField κ]
    [Fintype G] [CommGroup G]
    (D : LastLib.Book03RamificationTheory.Chapter11.Chapter11RamificationData G)
    (U : LastLib.Book03RamificationTheory.Chapter11.Chapter11UpperRamificationData D)
    (_C : Chapter14PerfectResidueConductorContext κ D) {r : ℚ}
    (hr : U.IsUpperBreak r) : ∃ z : ℤ, r = z := by
  sorry

theorem chapter14_perfect_residue_implies_separable_residue_extension
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [PerfectField k] :
    chapter14ResidueExtensionSeparable k l := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_perfect_residue_field_gives_separable_extension
    k l

/- Finiteness of the residue field adds Frobenius, cyclic units, and local
compactness; none is used in the preceding definitions. -/
def chapter14Frobenius
    (k : Type*) [CommSemiring k] (p : ℕ) [ExpChar k p] : k →+* k :=
  frobenius k p

theorem chapter14_finite_residue_frobenius_bijective
    (k : Type*) [Field k] [Finite k] (p : ℕ) [ExpChar k p] :
    Function.Bijective (chapter14Frobenius k p) := by
  sorry

theorem chapter14_finite_residue_units_cyclic
    (k : Type*) [Field k] [Finite k] : IsCyclic kˣ := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_finite_field_units_are_cyclic k

theorem chapter14_complete_dv_field_locally_compact_iff_finite_residue
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne]
    [CompleteSpace ((Valued.v : Valuation K Γ₀).valuationSubring)]
    [IsDiscreteValuationRing ((Valued.v : Valuation K Γ₀).valuationSubring)] :
    LocallyCompactSpace K ↔
      Finite (IsLocalRing.ResidueField
        ((Valued.v : Valuation K Γ₀).valuationSubring)) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_complete_dv_field_locallyCompact_iff_finite_residue

/- Characteristic zero belongs to the coefficient field of a representation,
not to the characteristic of the local field. -/
def chapter14RepresentationCoefficientCharacteristicZero
    (R : Type*) [AddMonoidWithOne R] : Prop :=
  CharZero R

theorem chapter14_char_zero_group_algebra_semisimple
    (R G : Type*) [Field R] [Group G] [Finite G] [CharZero R] :
    IsSemisimpleRing (MonoidAlgebra R G) := by
  sorry

theorem chapter14_char_zero_ordinary_character_at_identity
    {R G V : Type*} [Field R] [CharZero R] [Monoid G]
    [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    (ρ : Representation R G V) :
    ρ.character 1 = Module.finrank R V := by
  exact Representation.char_one ρ

def chapter14FieldAndCoefficientCharacteristicBoundary
    (K R : Type*) [Field K] [Field R] : Prop :=
  CharZero R

/- The characteristic-zero coefficient condition is independent of every
residue-field finiteness assumption. -/
theorem chapter14_coefficient_boundary_has_no_residue_finiteness_hypothesis
    (K R : Type*) [Field K] [Field R] :
    chapter14FieldAndCoefficientCharacteristicBoundary K R ↔ CharZero R :=
  Iff.rfl

end
end LastLib.Book03RamificationTheory.Chapter14
