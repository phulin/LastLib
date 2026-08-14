import LastLib.Book03RamificationTheory.Chapter16.Section02ACalculationProtocol
import LastLib.Book03RamificationTheory.Chapter15.Section03ConsequencesForTwoDimensionalArithmetic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RepresentationTheory.Rep.Basic

namespace LastLib.Book03RamificationTheory.Chapter16

noncomputable section

universe uk uG uV

open Ideal
open LastLib.Book03RamificationTheory.Chapter15
open scoped BigOperators

/-! ## 16.3. Consequences for two-dimensional arithmetic -/

/-- The kernel of a finite-dimensional representation. -/
def chapter16RepresentationKernel
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) : Subgroup G :=
  MonoidHom.ker ρ

theorem chapter16_representation_kernel_normal
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) :
    (chapter16RepresentationKernel ρ).Normal := by
  exact chapter15_representation_kernel_normal ρ

instance chapter16_representation_kernel_normal_instance
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) :
    (chapter16RepresentationKernel ρ).Normal :=
  chapter16_representation_kernel_normal ρ

/-- The fixed field cut out by the kernel of a representation of a finite Galois group. -/
def chapter16RepresentationFixedField
    {k K L V : Type*} [Semiring k] [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module k V]
    (ρ : Representation k (Gal(L / K)) V) : IntermediateField K L :=
  IntermediateField.fixedField (chapter16RepresentationKernel ρ)

/-- The quotient seen by the representation is the Galois group of its fixed field. -/
theorem chapter16_representation_quotient_is_fixed_field_galois_group
    {k K L V : Type*} [Semiring k] [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module k V]
    [FiniteDimensional K L] [IsGalois K L]
    (ρ : Representation k (Gal(L / K)) V) :
    Nonempty
      ((Gal(L / K) ⧸ chapter16RepresentationKernel ρ) ≃*
        Gal(chapter16RepresentationFixedField ρ / K)) := by
  sorry

/-- A finite representation together with a faithful-action certificate. -/
structure Chapter16FaithfulFiniteRepresentation
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) where
  faithful : Function.Injective ρ

theorem chapter16_faithful_representation_kernel_eq_bot
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V)
    (hfaithful : Function.Injective ρ) :
    chapter16RepresentationKernel ρ = ⊥ := by
  sorry

/-- The finite quotient through which a finite-image representation factors. -/
def chapter16FactorsThroughFiniteQuotient
    {k : Type uk} {G : Type uG} {V : Type uV}
    [Semiring k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) : Prop :=
  chapter15FactorsThroughFiniteQuotient.{uk, uG, uV, uG} ρ

theorem chapter16_finite_image_representation_uses_finite_galois_layer
    {k : Type uk} {G : Type uG} {V : Type uV}
    [Semiring k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    chapter16FactorsThroughFiniteQuotient ρ := by
  exact chapter15_finite_image_representation_uses_finite_galois_layer ρ

/-- The finite torsion-field interface attached to a representation. -/
/- SOURCE_ISSUE: The sentence "For torsion fields, a faithful finite
representation determines a finite Galois extension" needs an ambient
absolute/finite Galois action and a fixed-field construction; a faithful
representation of an abstract finite group alone does not determine a field.
The interface below makes the ambient finite Galois extension and its fixed
field explicit. -/
structure Chapter16TorsionFieldInterface
    {k K L V : Type*} [Field k] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup V] [Module k V] where
  representation : Representation k (Gal(L / K)) V
  faithful : Function.Injective representation
  finite_quotient : chapter16FactorsThroughFiniteQuotient representation
  fixed_field : IntermediateField K L
  fixed_field_eq : fixed_field = chapter16RepresentationFixedField representation

theorem chapter16_torsion_field_is_fixed_field
    {k K L V : Type*} [Field k] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup V] [Module k V]
    (T : Chapter16TorsionFieldInterface (k := k) (K := K) (L := L) (V := V)) :
    T.fixed_field = chapter16RepresentationFixedField T.representation := by
  exact T.fixed_field_eq

/-- In dimension two, tame inertia moves zero, one, or two dimensions. -/
theorem chapter16_two_dimensional_tame_codimension_cases
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter16LowerRamificationFiltration G)
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) :
    chapter16Codimension ρ (F.group 0) = 0 ∨
      chapter16Codimension ρ (F.group 0) = 1 ∨
      chapter16Codimension ρ (F.group 0) = 2 := by
  exact chapter15_two_dimensional_tame_codimension_cases F ρ hV

/-- Fixed spaces commute with restriction followed by subgroup image. -/
theorem chapter16_fixed_subspace_comp_map
    {k G H V : Type*} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (π : H →* G) (S : Subgroup H) :
    chapter16FixedSubspace (ρ.comp π) S =
      chapter16FixedSubspace ρ (S.map π) := by
  sorry

/-- Fixed-space codimension is unchanged when a subgroup action is pushed through a map. -/
theorem chapter16_fixed_space_codimension_comp_map
    {k G H V : Type*} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (π : H →* G) (S : Subgroup H) :
    chapter16Codimension (ρ.comp π) S =
      chapter16Codimension ρ (S.map π) := by
  sorry

/-- Upper-numbered quotient compatibility is the stability bridge for finite images. -/
theorem chapter16_upper_quotient_stability
    {G Q : Type*} [Group G] [Group Q]
    (U : ℝ → Subgroup G) (UQ : ℝ → Subgroup Q) (π : G →* Q)
    (hcompat : chapter16UpperQuotientCompatibility U UQ π) :
    ∀ r : ℝ, chapter16UpperPushforward U π r = UQ r := by
  intro r
  exact hcompat r

/-- The canonical permutation representation on a finite action set. -/
def chapter16PermutationRepresentation
    (k G X : Type*) [Field k] [Group G] [MulAction G X] :
    Representation k G (MonoidAlgebra k X) :=
  (Rep.ofMulAction k G X).ρ

/-- The regular representation is the permutation representation on the group itself. -/
def chapter16RegularRepresentation
    (k G : Type*) [Field k] [Group G] :
    Representation k G (MonoidAlgebra k G) :=
  chapter16PermutationRepresentation k G G

theorem chapter16_regular_representation_is_group_permutation
    (k G : Type*) [Field k] [Group G] :
    chapter16RegularRepresentation k G =
      chapter16PermutationRepresentation k G G := by
  rfl

/- The permutation conductor recovers the discriminant exponent of the field extension. -/
theorem chapter16_permutation_conductor_recovers_discriminant
    {A B G k : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Field k] (p : Ideal A) [p.IsPrime] [Finite (p.primesOver B)]
    [FiniteDimensional k (MonoidAlgebra k (p.primesOver B))]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (F : Chapter16LowerRamificationFiltration G)
    (C : Chapter15PrimeBranchPermutationData
      (k := k) (X := p.primesOver B) p P F)
    (hbranches : (p.primesOver B).ncard = 1) :
    chapter16ArtinConductor F
        (chapter16PermutationRepresentation k G (p.primesOver B)) =
      (chapter16DiscriminantExponent A B p : ℚ) := by
  exact chapter15_permutation_conductor_recovers_discriminant p P F C hbranches

/-- A field discriminant is ideal-valued. -/
abbrev Chapter16FieldDiscriminant (A : Type*) [Semiring A] := Ideal A

/-- A model discriminant is a coefficient-valued invariant. -/
abbrev Chapter16WeierstrassDiscriminant (R : Type*) := R

theorem chapter16_field_and_model_discriminants_have_distinct_interfaces
    (A R : Type*) [Semiring A] :
    Chapter16FieldDiscriminant A = Ideal A ∧
      Chapter16WeierstrassDiscriminant R = R := by
  exact ⟨rfl, rfl⟩

/-- A bound on the last nontrivial upper-numbered group. -/
def chapter16LastUpperBreakBound
    {G : Type*} [Group G]
    (U : ℝ → Subgroup G) (b : ℝ) : Prop :=
  ∀ r : ℝ, b < r → U r = ⊥

/-- A separate bound on the order of a finite Galois group. -/
def chapter16GroupOrderBound
    {G : Type*} [Group G] [Finite G] (N : ℕ) : Prop :=
  Nat.card G ≤ N

/-- The numerical form in which a local discriminant estimate is consumed. -/
def chapter16DiscriminantExponentBound (δ B : ℕ) : Prop :=
  δ ≤ B

/- LOCAL_DEPENDENCY_GUESS: The source gives no explicit numerical theorem
converting an upper-break and group-order estimate into a displacement bound.
This record leaves that genuinely separate estimate as a field, while keeping
the two structural bounds visible to downstream arithmetic. -/
structure Chapter16RamificationBoundInput
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G)
    (U : ℝ → Subgroup G) (f B : ℕ) where
  last_upper_break : ℝ
  last_upper_break_bound :
    chapter16LastUpperBreakBound U last_upper_break
  group_order_limit : ℕ
  group_order_bound : chapter16GroupOrderBound (G := G) group_order_limit
  displacement_bound : chapter16DiscriminantDisplacementSum F f ≤ B

/-- The displacement estimate implies the corresponding discriminant bound. -/
theorem chapter16_ramification_bound_feeds_discriminant_bound
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G) (f δ B : ℕ)
    (hδ : δ = chapter16DiscriminantDisplacementSum F f)
    (hbound : chapter16DiscriminantDisplacementSum F f ≤ B) :
    chapter16DiscriminantExponentBound δ B := by
  simpa [chapter16DiscriminantExponentBound, hδ] using hbound

theorem chapter16_ramification_bound_input_feeds_discriminant_bound
    {G : Type*} [Group G] [Finite G]
    {F : Chapter16LowerRamificationFiltration G}
    {U : ℝ → Subgroup G} {f B : ℕ}
    (I : Chapter16RamificationBoundInput F U f B)
    (δ : ℕ) (hδ : δ = chapter16DiscriminantDisplacementSum F f) :
    chapter16DiscriminantExponentBound δ B := by
  exact chapter16_ramification_bound_feeds_discriminant_bound
    F f δ B hδ I.displacement_bound

end

end LastLib.Book03RamificationTheory.Chapter16
