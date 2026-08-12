import LastLib.Book03RamificationTheory.Chapter05.Section02HerbrandsQuotientTheorem
import LastLib.Book03RamificationTheory.Chapter15.Section01TheRamificationDictionary
import LastLib.Book03RamificationTheory.Chapter15.Section02ACalculationProtocol
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Ideal.Norm.RelNorm

namespace LastLib.Book03RamificationTheory.Chapter16

noncomputable section

universe uG

open Ideal
open LastLib.Book03RamificationTheory.Chapter15
open scoped BigOperators

/-! ## 16.1. The ramification dictionary -/

/-- The finite lower filtration used by the synthesis chapter. -/
abbrev Chapter16LowerRamificationFiltration (G : Type*) [Group G] [Finite G] :=
  Chapter15LowerRamificationFiltration G

/-- The residue-symmetry quotient `G/G₀`. -/
abbrev chapter16ResidueQuotient
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) : Type _ :=
  chapter15ResidueQuotient F

/-- The successive lower layer `Gᵢ/Gᵢ₊₁`. -/
abbrev chapter16Layer
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (i : ℕ) : Type _ :=
  chapter15Layer F i

theorem chapter16_layer_normal
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (i : ℕ) :
    ((F.group (i + 1)).subgroupOf (F.group i)).Normal := by
  exact chapter15_layer_normal F i

theorem chapter16_residue_quotient_equiv_of_kernel
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (F : Chapter16LowerRamificationFiltration G) (ρ : G →* Q)
    (hker : MonoidHom.ker ρ = F.group 0)
    (hsurj : Function.Surjective ρ) :
    Nonempty (chapter16ResidueQuotient F ≃* Q) := by
  exact chapter15_residue_quotient_equiv_of_kernel F ρ hker hsurj

/-- The quotient `G/G₀` is the residue-field symmetry object. -/
def chapter16ResidueFieldSymmetry
    {G k l : Type*} [Group G] [Finite G] [Field k] [Field l]
    [Algebra k l] (F : Chapter16LowerRamificationFiltration G) : Prop :=
  chapter15ResidueFieldSymmetry (k := k) (l := l) F

/-- The tame layer is cyclic. -/
def chapter16TameLayerIsCyclic
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) : Prop :=
  chapter15TameLayerIsCyclic F

/-- A positive lower layer is additive over a residue field of characteristic `p`. -/
def chapter16WildLayerIsAdditiveOver
    {G : Type*} [Group G] [Finite G] [Field k]
    (p i : ℕ) [CharP k p]
    (F : Chapter16LowerRamificationFiltration G) : Prop :=
  chapter15WildLayerIsAdditiveOver (k := k) p i F

/-- The tame layer has order prime to the residue characteristic. -/
def chapter16TameLayerPrimeToCharacteristic
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) (F : Chapter16LowerRamificationFiltration G) : Prop :=
  Nat.Coprime p (Nat.card (chapter16Layer F 0))

/-- The finite displacement sum representing the different exponent. -/
def chapter16DifferentDisplacementSum
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) : ℕ :=
  chapter15DifferentDisplacementSum F

/-- The residue-degree-weighted displacement sum representing the discriminant exponent. -/
def chapter16DiscriminantDisplacementSum
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (f : ℕ) : ℕ :=
  chapter15DiscriminantDisplacementSum F f

/-- The fixed-space codimension of a subgroup action. -/
abbrev chapter16Codimension
    {k G V : Type*} [DivisionRing k] [Group G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) : ℕ :=
  chapter15Codimension ρ H

/-- The Artin conductor written with the finite lower filtration. -/
def chapter16ArtinConductor
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter16LowerRamificationFiltration G)
    (ρ : Representation k G V) : ℚ :=
  chapter15ArtinConductor F ρ

/-- The tame codimension contribution to the Artin conductor. -/
def chapter16TameConductor
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter16LowerRamificationFiltration G)
    (ρ : Representation k G V) : ℚ :=
  chapter15TameConductor F ρ

/-- The positive-depth weighted contribution, i.e. the Swan conductor. -/
def chapter16SwanConductor
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter16LowerRamificationFiltration G)
    (ρ : Representation k G V) : ℚ :=
  chapter15SwanConductor F ρ

/-- The Herbrand reindexing used to pass from lower to upper numbering. -/
noncomputable def chapter16HerbrandFunction
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (u : ℝ) : ℝ :=
  chapter15HerbrandFunction F u

/-- The upper coordinate of the lower break at `i`. -/
def chapter16UpperBreak
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (i : ℕ) : ℝ :=
  chapter15UpperBreak F i

/-- The different ideal upstairs. -/
def chapter16DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] : Ideal B :=
  chapter15DifferentIdeal A B

/-- The discriminant ideal downstairs is the relative norm of the different. -/
noncomputable def chapter16RelativeDiscriminantIdeal
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.relNorm A (chapter16DifferentIdeal A B)

/-- A single finite filtration together with the residue-layer part of the table. -/
/- SOURCE_ISSUE: The sentence "For a finite Galois extension with separable
residue extension, all of the main invariants can now be read from one
filtration" does not select a valuation or prime above the base, and the
displayed identity `δ = f d` is not branch-free before a one-branch (for
example complete or henselian) hypothesis is imposed.  The minimal correction
is to make the finite filtration, residue degree, and the two exponents
explicit in the records below. -/
structure Chapter16RamificationDictionary
    {G k l : Type*} [Group G] [Finite G] [Field k] [Field l]
    [Algebra k l] (p : ℕ) [CharP k p]
    (F : Chapter16LowerRamificationFiltration G) where
  residue_characteristic_prime : Nat.Prime p
  residue_extension_separable : Algebra.IsSeparable k l
  residue_symmetry : chapter16ResidueFieldSymmetry (k := k) (l := l) F
  tame_layer_cyclic : chapter16TameLayerIsCyclic F
  tame_layer_prime_to_characteristic :
    chapter16TameLayerPrimeToCharacteristic p F
  wild_layers_additive : ∀ i : ℕ, 1 ≤ i →
    chapter16WildLayerIsAdditiveOver (k := k) p i F

/-- The numerical part of the dictionary, with the finite-cutoff convention explicit. -/
structure Chapter16NumericalDictionary
    {G k V : Type*} [Group G] [Finite G] [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter16LowerRamificationFiltration G)
    (f d δ : ℕ) (a : ℚ) (ρ : Representation k G V) where
  residue_degree_pos : 0 < f
  different_formula : d = chapter16DifferentDisplacementSum F
  discriminant_formula : δ = chapter16DiscriminantDisplacementSum F f
  artin_formula : a = chapter16ArtinConductor F ρ

theorem chapter16_different_displacement_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) :
    chapter16DifferentDisplacementSum F =
      ∑ i ∈ Finset.range F.cutoff, (Nat.card (F.group i) - 1) := by
  rfl

theorem chapter16_discriminant_displacement_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (f : ℕ) :
    chapter16DiscriminantDisplacementSum F f =
      f * chapter16DifferentDisplacementSum F := by
  rfl

theorem chapter16_artin_conductor_eq_tame_add_swan
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter16LowerRamificationFiltration G)
    (ρ : Representation k G V) :
    chapter16ArtinConductor F ρ =
      chapter16TameConductor F ρ + chapter16SwanConductor F ρ := by
  exact chapter15_artin_conductor_eq_tame_add_swan F ρ

/- The lower filtration restricts by intersection with a subgroup. -/
noncomputable def chapter16RestrictLowerFiltration
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (H : Subgroup G) :
    Chapter16LowerRamificationFiltration H :=
  chapter15RestrictLowerFiltration F H

@[simp] theorem chapter16RestrictLowerFiltration_group
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (H : Subgroup G) (i : ℕ) :
    (chapter16RestrictLowerFiltration F H).group i =
      (F.group i).comap H.subtype := by
  exact chapter15RestrictLowerFiltration_group F H i

theorem chapter16_restrict_lower_membership_iff
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (H : Subgroup G)
    (i : ℕ) (h : H) :
    h ∈ (chapter16RestrictLowerFiltration F H).group i ↔
      (H.subtype h) ∈ F.group i := by
  rfl

/-- Lower quotient compatibility is the strong condition that does not hold in general. -/
def chapter16LowerQuotientCompatibility
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (F : Chapter16LowerRamificationFiltration G)
    (FQ : Chapter16LowerRamificationFiltration Q)
    (π : G →* Q) : Prop :=
  chapter15LowerQuotientCompatibility F FQ π

/-- The pushforward of an upper-numbered subgroup along a quotient map. -/
def chapter16UpperPushforward
    {G Q : Type*} [Group G] [Group Q]
    (U : ℝ → Subgroup G) (π : G →* Q) (r : ℝ) : Subgroup Q :=
  (U r).map π

/-- Upper quotient compatibility is the finite-level form of profinite upper numbering. -/
def chapter16UpperQuotientCompatibility
    {G Q : Type*} [Group G] [Group Q]
    (U : ℝ → Subgroup G) (UQ : ℝ → Subgroup Q) (π : G →* Q) : Prop :=
  chapter15UpperQuotientCompatibility U UQ π

/- LOCAL_DEPENDENCY_GUESS: The existing checkout has finite Herbrand quotient
interfaces but no profinite upper-filtration object.  This is the minimal
finite-quotient-compatible system needed to state the extension to a profinite
Galois group without assuming a topology or a conductor identity. -/
structure Chapter16ProfiniteUpperRamificationSystem
    (G : Type uG) [Group G] where
  absolute : ℝ → Subgroup G
  quotient : ∀ (Q : Type uG) [Group Q] [Finite Q],
    (π : G →* Q) → Function.Surjective π → ℝ → Subgroup Q
  quotient_map : ∀ (Q : Type uG) [Group Q] [Finite Q]
    (π : G →* Q) (hπ : Function.Surjective π) (r : ℝ),
    (absolute r).map π = quotient Q π hπ r
  quotient_transitive : ∀ (Q R : Type uG) [Group Q] [Finite Q]
    [Group R] [Finite R] (π : G →* Q) (hπ : Function.Surjective π)
    (τ : Q →* R) (hτ : Function.Surjective τ) (r : ℝ),
    (quotient Q π hπ r).map τ =
      quotient R (τ.comp π) (hτ.comp hπ) r

theorem chapter16_profinite_upper_quotient_map
    {G : Type uG} [Group G]
    (P : Chapter16ProfiniteUpperRamificationSystem G)
    {Q : Type uG} [Group Q] [Finite Q] (π : G →* Q)
    (hπ : Function.Surjective π) (r : ℝ) :
    (P.absolute r).map π = P.quotient Q π hπ r := by
  exact P.quotient_map Q π hπ r

theorem chapter16_herbrand_upper_groups_survive_quotient
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (S : LastLib.Book03RamificationTheory.Chapter05.Chapter05QuotientRamificationSetup
      G H)
    (hup : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        S.upstairs))
    (hdown : Function.Bijective
      (LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction
        S.downstairs))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    LastLib.Book03RamificationTheory.Chapter05.chapter05UpperRamificationGroup
        S.downstairs v =
      LastLib.Book03RamificationTheory.Chapter05.chapter05UpperQuotientImage
        H S.upstairs v := by
  exact LastLib.Book03RamificationTheory.Chapter05.chapter05_herbrand_quotient_theorem
    H S hup hdown hv

theorem chapter16_relative_discriminant_is_norm_of_different
    (A B : Type*) [CommRing A] [CommRing B]
    [IsDedekindDomain A]
    [Algebra A B] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] [Module.Finite A B] :
    chapter16RelativeDiscriminantIdeal A B =
      Ideal.relNorm A (chapter16DifferentIdeal A B) := by
  rfl

end

end LastLib.Book03RamificationTheory.Chapter16
