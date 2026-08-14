import LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.Section01SuccessivePrecision
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section04FormalPowerSeries
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Topology

/-!
Common interfaces for Book 2, Chapter 10.  The valuation-subring unit group
and its principal-unit subgroup are Mathlib objects; the higher congruence
subgroups below are expressed in the same ring-of-integers coordinates.
-/

/-- The residue field of a local ring, using Mathlib's canonical quotient. -/
abbrev Chapter10ResidueField (A : Type*) [CommRing A] [IsLocalRing A] : Type _ :=
  IsLocalRing.ResidueField A

/-- A finite-precision quotient of a local ring. -/
abbrev Chapter10PrecisionQuotient
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  A ⧸ (IsLocalRing.maximalIdeal A) ^ n

/-- The subgroup of units congruent to `1` modulo a power of an ideal. -/
def chapter10IdealUnitFiltration
    (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ((u * v : Rˣ) : R) - 1 ∈ I ^ n at *
    rw [Units.val_mul]
    rw [show (u : R) * (v : R) - 1 =
        ((u : R) - 1) + (u : R) * ((v : R) - 1) by ring]
    exact add_mem hu (Ideal.mul_mem_left _ _ hv)
  inv_mem' := by
    intro u hu
    change ((↑u⁻¹ : Rˣ) : R) - 1 ∈ I ^ n at *
    have hinv : ((↑u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
      simp
    rw [show ((↑u⁻¹ : Rˣ) : R) - 1 =
        -((↑u⁻¹ : Rˣ) : R) * ((u : R) - 1) by
          rw [neg_mul, mul_sub, hinv]
          ring]
    simpa [neg_mul] using
      (I ^ n).neg_mem
        (Ideal.mul_mem_left (I ^ n) ((↑u⁻¹ : Rˣ) : R) hu)

/-- The unit filtration on a local ring `A`: `Uⁿ = 1 + 𝔪ⁿ`. -/
def chapter10UnitFiltration
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Subgroup Aˣ :=
  chapter10IdealUnitFiltration A (IsLocalRing.maximalIdeal A) n

/-- The same filtration transported to the unit group of the fraction field. -/
def chapter10FieldUnitFiltration {L : Type*} [Field L]
    (A : ValuationSubring L) (n : ℕ) : Subgroup Lˣ :=
  (chapter10UnitFiltration A n).map (Units.map A.subtype.toMonoidHom)

/-- The quotient of the ring-of-integers units by `Uⁿ`. -/
abbrev Chapter10UnitRingQuotient {L : Type*} [Field L]
    (A : ValuationSubring L) (n : ℕ) : Type _ :=
  Aˣ ⧸ chapter10UnitFiltration A n

/-- The quotient of `Lˣ` by the field-level congruence subgroup `Uⁿ`. -/
abbrev Chapter10FieldUnitQuotient {L : Type*} [Field L]
    (A : ValuationSubring L) (n : ℕ) : Type _ :=
  Lˣ ⧸ chapter10FieldUnitFiltration A n

/-- Reduction of ring-of-integers units to residue-field units. -/
def chapter10UnitReduction {L : Type*} [Field L]
    (A : ValuationSubring L) : Aˣ →* (Chapter10ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom

/-- The additive quotient of the `n`th and `(n+1)`st ideal layers. -/
def chapter10IdealLayerDenominator
    (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) :
    Submodule R (↥(I ^ n : Ideal R)) :=
  Submodule.comap (I ^ n : Submodule R R).subtype
    (I ^ (n + 1) : Submodule R R)

abbrev Chapter10IdealLayer
    (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) : Type _ :=
  (↥(I ^ n : Ideal R)) ⧸ chapter10IdealLayerDenominator R I n

/-- The multiplicative quotient `Uⁿ/Uⁿ⁺¹` inside the ring-of-integers units. -/
abbrev Chapter10UnitLayerQuotient {L : Type*} [Field L]
    (A : ValuationSubring L) (n : ℕ) : Type _ :=
  chapter10UnitFiltration A n ⧸
    (chapter10UnitFiltration A (n + 1)).subgroupOf (chapter10UnitFiltration A n)

/-- A normalized uniformizer in the valuation ring, reusing Book 1's interface. -/
abbrev Chapter10Uniformizer {L : Type*} [Field L]
    (A : ValuationSubring L) (π : A) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.isUniformizerElement A π

/-- A topology in which the congruence subgroups form a neighborhood basis at `1`. -/
def Chapter10UnitFiltrationNeighborhoodBasis
    {G : Type*} [Group G] [TopologicalSpace G]
    (U : ℕ → Subgroup G) : Prop :=
  (∀ n, IsOpen (U n : Set G)) ∧
    ∀ s ∈ 𝓝 (1 : G), ∃ n, (U n : Set G) ⊆ s

/-- A compactness predicate for a topological group. -/
def Chapter10CompactUnitGroup {G : Type*} [TopologicalSpace G] : Prop :=
  IsCompact (Set.univ : Set G)

/-- A local-field unit expansion records convergence of successive corrections. -/
def Chapter10SuccessiveUnitCorrectionProduct
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ] (u s₀ : Aˣ) (c : ℕ → Aˣ) : Prop :=
  (∀ n, c n ∈ chapter10UnitFiltration A (n + 1)) ∧
    (∀ N, u * (s₀ * Finset.prod (Finset.range N) c)⁻¹ ∈
      chapter10UnitFiltration A (N + 1)) ∧
    Filter.Tendsto
      (fun N : ℕ => s₀ * Finset.prod (Finset.range N) c)
      Filter.atTop (𝓝 u)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
