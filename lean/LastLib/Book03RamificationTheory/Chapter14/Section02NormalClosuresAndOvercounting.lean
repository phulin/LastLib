import LastLib.Book03RamificationTheory.Chapter14.Core
import LastLib.Book03RamificationTheory.Chapter04.Dependencies
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ULift
import Mathlib.RepresentationTheory.Rep.Basic

namespace LastLib.Book03RamificationTheory.Chapter14

noncomputable section

open scoped BigOperators

universe u

instance chapter14ULiftRationalCharZero : CharZero (ULift.{u} ℚ) :=
  charZero_of_injective_ringHom (ULift.ringEquiv.symm.toRingHom.injective)

/-!
## 14.2. Normal closures and overcounting
-/ 

/- LOCAL_DEPENDENCY_GUESS: the subgroup/fixed-field data are separated from a chosen embedding of the
nongalois field.  The residue-separability field is deliberately a Prop: the
valuation model supplying it is chosen in the local ramification chapters. -/
structure Chapter14NormalClosureData
    (K M L : Type*) (δ : ℕ) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [Algebra.IsSeparable K M]
    [IsGalois K L]
    [Fintype (Gal(L / K))] where
  realization :
    LastLib.Book03RamificationTheory.Chapter12.Chapter12FiniteGaloisRealization K L
  intermediate_equiv : M ≃ₐ[K] realization.intermediate
  subgroup_over_M : Nonempty (realization.subgroup ≃* Gal(L / M))
  residue_extension_separable : Prop

theorem chapter14_normal_closure_fixed_field
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [Algebra.IsSeparable K M]
    [IsGalois K L]
    [Fintype (Gal(L / K))]
    (δ : ℕ) (R : Chapter14NormalClosureData K M L δ) :
    R.realization.intermediate =
      IntermediateField.fixedField R.realization.subgroup :=
  R.realization.fixedField_eq

/- The group filtration lives on a Galois group.  Its action on the left
cosets is supplied canonically by Mathlib's quotient action. -/
structure Chapter14GaloisRamificationFiltration
    (G : Type*) [Group G] where
  lower : LastLib.Book03RamificationTheory.Chapter04.Chapter04LowerFiltration G
  upper : ℝ → Subgroup G
  upper_antitone : ∀ u v, u ≤ v → upper v ≤ upper u
  upper_zero : upper 0 = lower.lower 0

def chapter14LowerRamificationGroup
    {G : Type*} [Group G]
    (F : Chapter14GaloisRamificationFiltration G) (n : ℕ) : Subgroup G :=
  F.lower.lower n

def chapter14UpperRamificationGroup
    {G : Type*} [Group G]
    (F : Chapter14GaloisRamificationFiltration G) (u : ℝ) : Subgroup G :=
  F.upper u

theorem chapter14_lower_group_descends_to_subgroup
    {G : Type*} [Group G]
    (F : Chapter14GaloisRamificationFiltration G) (H : Subgroup G) (n : ℕ) :
    (LastLib.Book03RamificationTheory.Chapter04.chapter04SubgroupLowerFiltration
      F.lower H).lower n = (F.lower.lower n).comap H.subtype :=
  rfl

/- The canonical left-coset G-set is the permutation domain. -/
abbrev chapter14CosetSpace (G : Type*) [Group G] (H : Subgroup G) := G ⧸ H

def chapter14PermutationRepresentation
    (k G X : Type*) [Field k] [Group G] [MulAction G X] :
    Representation k G (MonoidAlgebra k X) :=
  (Rep.ofMulAction k G X).ρ

def chapter14RegularRepresentation
    (k G : Type*) [Field k] [Group G] :
    Representation k G (MonoidAlgebra k G) :=
  (Rep.ofMulAction k G G).ρ

def chapter14PermutationConductor
    {G : Type u} [Group G] [Fintype G]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile G)
    (H : Subgroup G) [Fintype (G ⧸ H)]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) (G ⧸ H))] : ℕ :=
  P.artinConductor (E := ULift.{u} ℚ) _
    (chapter14PermutationRepresentation (ULift.{u} ℚ) G (G ⧸ H))

def chapter14RegularConductor
    {G : Type u} [Group G] [Fintype G]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile G)
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) G)] : ℕ :=
  P.artinConductor (E := ULift.{u} ℚ) _
    (chapter14RegularRepresentation (ULift.{u} ℚ) G)

theorem chapter14_coset_permutation_dimension
    {k G : Type*} [Field k] [Group G] (H : Subgroup G)
    [Fintype (G ⧸ H)]
    [FiniteDimensional k (MonoidAlgebra k (G ⧸ H))] :
    Module.finrank k (MonoidAlgebra k (G ⧸ H)) = Nat.card (G ⧸ H) := by
  sorry

theorem chapter14_regular_permutation_dimension
    {k G : Type*} [Field k] [Group G] [Fintype G]
    [FiniteDimensional k (MonoidAlgebra k G)] :
    Module.finrank k (MonoidAlgebra k G) = Nat.card G := by
  sorry

theorem chapter14_cubic_coset_card
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hG : Nat.card G = 6) (hH : Nat.card H = 2) :
    Nat.card (G ⧸ H) = 3 := by
  sorry

/- A generic cubic comparison keeps the two conductors and the two
discriminants separate.  Its `distinct` field is the mathematically precise
genericity condition; it is not silently inferred from the group orders. -/
structure Chapter14GenericCubicOvercounting
    (G : Type u) [Group G] [Finite G] [Fintype G]
    (H : Subgroup G) [Fintype (G ⧸ H)]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) (G ⧸ H))]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) G)]
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile G) where
  group_card : Nat.card G = 6
  subgroup_card : Nat.card H = 2
  cubicDiscriminant : ℕ
  closureDiscriminant : ℕ
  permutation_conductor_eq :
    chapter14PermutationConductor P H = cubicDiscriminant
  regular_conductor_eq :
    chapter14RegularConductor P = closureDiscriminant
  discriminants_distinct : cubicDiscriminant ≠ closureDiscriminant

theorem chapter14_generic_cubic_dimensions
    {G : Type u} [Group G] [Finite G] [Fintype G]
    {H : Subgroup G} [Fintype (G ⧸ H)]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) (G ⧸ H))]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) G)]
    {P : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile G}
    (D : Chapter14GenericCubicOvercounting G H P) :
    Nat.card (G ⧸ H) = 3 ∧
      Module.finrank ℚ (MonoidAlgebra ℚ (G ⧸ H)) = 3 ∧
      Module.finrank ℚ (MonoidAlgebra ℚ G) = 6 := by
  sorry

theorem chapter14_generic_cubic_conductors_are_not_equal
    {G : Type u} [Group G] [Finite G] [Fintype G]
    {H : Subgroup G} [Fintype (G ⧸ H)]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) (G ⧸ H))]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ) G)]
    {P : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile G}
    (D : Chapter14GenericCubicOvercounting G H P) :
    chapter14PermutationConductor P H ≠ chapter14RegularConductor P := by
  intro h
  apply D.discriminants_distinct
  calc
    D.cubicDiscriminant = chapter14PermutationConductor P H :=
      D.permutation_conductor_eq.symm
    _ = chapter14RegularConductor P := h
    _ = D.closureDiscriminant := D.regular_conductor_eq

/- The permutation conductor identity is only asserted after the selected
normal closure has separable residue extension. -/
theorem chapter14_permutation_conductor_recovers_intrinsic_different
    {K M L : Type u} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional K L] [Algebra.IsSeparable K M]
    [IsGalois K L]
    [Fintype (Gal(L / K))]
    (δ : ℕ) (R : Chapter14NormalClosureData K M L δ)
    (P : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile
      (Gal(L / K)))
    [Fintype (Gal(L / K) ⧸ R.realization.subgroup)]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ)
        (Gal(L / K) ⧸ R.realization.subgroup))]
    (hres : R.residue_extension_separable) :
    chapter14PermutationConductor P R.realization.subgroup = δ := by
  sorry

theorem chapter14_permutation_conductor_independent_of_closure
    {K M L₁ L₂ : Type u} [Field K] [Field M] [Field L₁] [Field L₂]
    [Algebra K M] [Algebra K L₁] [Algebra K L₂]
    [Algebra M L₁] [Algebra M L₂]
    [IsScalarTower K M L₁] [IsScalarTower K M L₂]
    [FiniteDimensional K M] [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [Algebra.IsSeparable K M]
    [IsGalois K L₁] [IsGalois K L₂]
    [Fintype (Gal(L₁ / K))] [Fintype (Gal(L₂ / K))]
    (δ : ℕ)
    (R₁ : Chapter14NormalClosureData K M L₁ δ)
    (R₂ : Chapter14NormalClosureData K M L₂ δ)
    (P₁ : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile
      (Gal(L₁ / K)))
    (P₂ : LastLib.Book03RamificationTheory.Chapter12.Chapter12ConductorProfile
      (Gal(L₂ / K)))
    [Fintype (Gal(L₁ / K) ⧸ R₁.realization.subgroup)]
    [Fintype (Gal(L₂ / K) ⧸ R₂.realization.subgroup)]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ)
        (Gal(L₁ / K) ⧸ R₁.realization.subgroup))]
    [FiniteDimensional (ULift.{u} ℚ)
      (MonoidAlgebra (ULift.{u} ℚ)
        (Gal(L₂ / K) ⧸ R₂.realization.subgroup))]
    (hres₁ : R₁.residue_extension_separable)
    (hres₂ : R₂.residue_extension_separable) :
    chapter14PermutationConductor P₁ R₁.realization.subgroup =
      chapter14PermutationConductor P₂ R₂.realization.subgroup := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter14
