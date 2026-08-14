import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Res
import LastLib.Book03RamificationTheory.Chapter11.Section03AdditivityAndExactSequences
import LastLib.Book03RamificationTheory.Chapter12.Core

namespace LastLib.Book03RamificationTheory.Chapter13

noncomputable section

universe u

instance chapter13ULiftRationalCharZero : CharZero (ULift.{u} ℚ) :=
  charZero_of_injective_ringHom (ULift.ringEquiv.symm.toRingHom.injective)

open LastLib.Book03RamificationTheory.Chapter11
open LastLib.Book03RamificationTheory.Chapter12
open scoped BigOperators

/-!
## Shared interfaces for Chapter 13

The source chapter passes between a finite separable extension, a chosen finite
Galois closure, and the finite quotient through which a representation acts.
The record below keeps those choices explicit while leaving the valuation-ring
implementation to the preceding chapters.  Its numerical field is the
book-facing interface for the relative discriminant exponent
`v_K (𝔡_{M/K})`.
-/

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters should eventually identify
this record with their canonical chosen Galois closure and residue-extension
data.  The fields here are only the finite-separable, transitive-action, and
discriminant-normalization inputs used by the conductor identities. -/
structure Chapter13NongaloisExtensionContext
    (K M Ω G : Type*)
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (AlgHom K M Ω)]
    [Fintype (AlgHom K M Ω)] where
  /-- Finiteness of the embedding set, supplied by finite separability. -/
  finite_embeddings : Finite (AlgHom K M Ω)
  /-- A chosen embedding, used to identify the embedding set with a coset set. -/
  base_embedding : AlgHom K M Ω
  /-- The Galois action on embeddings is transitive. -/
  transitive : ∀ φ : AlgHom K M Ω, ∃ g : G, g • base_embedding = φ
  /-- The chosen finite group is identified with the Galois group of the closure. -/
  group_identification : G ≃* Gal(Ω / K)
  /-- Compatibility of the abstract action with postcomposition by automorphisms. -/
  action_compatible :
    ∀ (g : G) (φ : AlgHom K M Ω),
      g • φ = (group_identification g).toAlgHom.comp φ
  /-- Separability of the residue extension of the chosen Galois closure. -/
  residue_extension_separable : Prop
  /-- The local degree and different/discriminant numerical interface. -/
  numbers : Chapter12LocalExtensionNumbers
  degree_eq : Module.finrank K M = numbers.degree
  relative_discriminant_valuation : ℕ
  discriminant_eq_valuation :
    numbers.discriminantExponent = relative_discriminant_valuation

namespace Chapter13NongaloisExtensionContext

variable {K M Ω G : Type*}
variable [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
variable [FiniteDimensional K M] [Algebra.IsSeparable K M]
variable [FiniteDimensional K Ω] [IsGalois K Ω]
variable [Group G] [Fintype G] [MulAction G (AlgHom K M Ω)]
variable [Fintype (AlgHom K M Ω)]

theorem degree_eq_numbers_degree (C : Chapter13NongaloisExtensionContext K M Ω G) :
    Module.finrank K M = C.numbers.degree :=
  C.degree_eq

theorem discriminant_eq_relative_valuation
    (C : Chapter13NongaloisExtensionContext K M Ω G) :
    C.numbers.discriminantExponent = C.relative_discriminant_valuation :=
  C.discriminant_eq_valuation

end Chapter13NongaloisExtensionContext

/- The subgroup fixing the chosen embedding is the book's `G_M`. -/
def chapter13EmbeddingStabilizer
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (AlgHom K M Ω)]
    [Fintype (AlgHom K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G) : Subgroup G := by
  exact MulAction.stabilizer G C.base_embedding

@[simp] theorem chapter13_mem_embeddingStabilizer_iff
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (AlgHom K M Ω)]
    [Fintype (AlgHom K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G) (g : G) :
    g ∈ chapter13EmbeddingStabilizer C ↔ g • C.base_embedding = C.base_embedding := by
  rfl

/-!
The lower-numbered sum and its residue-degree normalization are separated from
the conductor profile.  This lets the regular-representation calculation use
Hilbert's formula without baking its conclusion into a hypothesis.
-/

/- LOCAL_DEPENDENCY_GUESS: this numerical bridge should be replaced by the
canonical different/discriminant interface from the preceding local-field
chapters.  Its fields record only Hilbert's different formula and the
residue-degree normalization; they do not assume any conductor identity. -/
structure Chapter13LocalDiscriminantData
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) where
  differentExponent : ℕ
  discriminantExponent : ℕ
  different_eq_hilbert :
    differentExponent =
      Finset.sum (Finset.range D.bound)
        (fun i => Fintype.card (D.lower i) - 1)
  discriminant_eq_residue_degree_mul_different :
    discriminantExponent = D.f * differentExponent

def chapter13DifferentDisplacementSum
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) : ℕ :=
  Finset.sum (Finset.range D.bound)
    (fun i => Fintype.card (D.lower i) - 1)

@[simp] theorem chapter13DifferentDisplacementSum_def
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) :
    chapter13DifferentDisplacementSum D =
      Finset.sum (Finset.range D.bound)
        (fun i => Fintype.card (D.lower i) - 1) :=
  rfl

theorem chapter13_local_different_exponent_eq_displacement_sum
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) (Δ : Chapter13LocalDiscriminantData D) :
    Δ.differentExponent = chapter13DifferentDisplacementSum D := by
  exact Δ.different_eq_hilbert

theorem chapter13_local_discriminant_exponent_eq_residue_mul_different
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) (Δ : Chapter13LocalDiscriminantData D) :
    Δ.discriminantExponent = D.f * Δ.differentExponent :=
  Δ.discriminant_eq_residue_degree_mul_different

/- The coefficient-polymorphic conductor wrapper used for characters. -/
def chapter13ArtinConductor
    {E G V : Type*} [Field E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (D : Chapter11RamificationData G) (ρ : Representation E G V) : ℚ :=
  chapter11ArtinConductor D ρ

/- This bridge is derived from the earlier conductor-profile fixed-space
interface: it is the trivial-representation input needed when the induction
formula is specialized to `W = 1`. -/
theorem chapter13_conductor_profile_trivial_representation_zero
    {G : Type u} [Group G] [Fintype G]
    (P : Chapter12ConductorProfile G) :
    P.artinConductor (E := ULift.{u} ℚ) _
        (Representation.trivial (ULift.{u} ℚ) G (ULift.{u} ℚ)) = 0 := by
  sorry

def chapter13CharacterConductor
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) (V : FDRep ℂ G) : ℚ :=
  chapter13ArtinConductor D V.ρ

def chapter13TrivialRepresentation
    (E G : Type*) [Field E] [Group G] : Representation E G E :=
  Representation.trivial E G E

def chapter13TrivialCharacter
    (G : Type*) [Group G] [Fintype G] : FDRep ℂ G :=
  FDRep.of (chapter13TrivialRepresentation ℂ G)

theorem chapter13_trivial_representation_conductor_zero
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G) :
    chapter13ArtinConductor D (chapter13TrivialRepresentation E G) = 0 := by
  sorry

theorem chapter13_trivial_character_conductor_zero
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) :
    chapter13CharacterConductor D (chapter13TrivialCharacter G) = 0 := by
  sorry

/- This is the coefficient-extension and representation-equivalence bridge
used whenever a direct-sum or induced model is replaced by an isomorphic one. -/
theorem chapter13_artin_conductor_eq_of_representation_equiv
    {E G V W : Type*} [Field E] [Group G] [Fintype G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (D : Chapter11RamificationData G)
    (ρ : Representation E G V) (σ : Representation E G W)
    (hρσ : Nonempty (ρ.Equiv σ)) :
    chapter13ArtinConductor D ρ = chapter13ArtinConductor D σ := by
  sorry

def chapter13ConductorIdeal
    {A : Type*} [CommRing A] (m : Ideal A) (a : ℕ) : Ideal A :=
  m ^ a

def chapter13DiscriminantIdeal
    {A : Type*} [CommRing A] (m : Ideal A) (δ : ℕ) : Ideal A :=
  m ^ δ

@[simp] theorem chapter13_trivial_conductor_ideal_eq_unit
    {A : Type*} [CommRing A] (m : Ideal A) :
    chapter13ConductorIdeal m 0 = ⊤ := by
  simp [chapter13ConductorIdeal]

end

end LastLib.Book03RamificationTheory.Chapter13
