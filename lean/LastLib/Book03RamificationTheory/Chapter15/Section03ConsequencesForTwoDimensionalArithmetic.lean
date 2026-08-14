import LastLib.Book03RamificationTheory.Chapter15.Section02ACalculationProtocol
import LastLib.Book03RamificationTheory.Chapter13.Section01ThePermutationRepresentationOfEmbeddings
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RepresentationTheory.Rep.Basic

namespace LastLib.Book03RamificationTheory.Chapter15

noncomputable section

open scoped BigOperators

/-! ## 15.3. The elliptic-curve and torsion-field interface -/

structure Chapter15EllipticTorsionFieldInterface
    (K L M : Type*) (n : ℕ)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup M] [Module (ZMod n) M] [Finite M] where
  n_prime_to_characteristic :
    CharP K 0 ∨
      ∃ p : ℕ, Nat.Prime p ∧ CharP K p ∧ Nat.Coprime n p
  action : Gal(L / K) →* Equiv.Perm M
  torsion_card : Nat.card M = n ^ 2
  cutout : IntermediateField K L
  cutout_eq_fixed_field :
    cutout = IntermediateField.fixedField action.ker

theorem chapter15_elliptic_torsion_cutout_is_fixed_field
    {K L M : Type*} (n : ℕ)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (T : Chapter15EllipticTorsionFieldInterface K L M n) :
    T.cutout = IntermediateField.fixedField T.action.ker := by
  sorry

/- Finite flatness supplies an integral geometric theorem whose output is an
   upper-depth cutoff.  The arithmetic content is kept separate from that
   theorem, so this record contains the cutoff input rather than a disguised
   discriminant conclusion. -/
structure Chapter15FiniteFlatCutoffData
    (Γ M : Type*) [Group Γ] [AddCommGroup M] [MulAction Γ M] [Finite M] where
  residuePrime : ℕ
  residuePrime_prime : Nat.Prime residuePrime
  exponent : ℕ
  baseRamificationIndex : ℕ
  upper : ℝ → Subgroup Γ
  cutoff : ℝ
  cutoff_bound :
    cutoff ≤ (baseRamificationIndex : ℝ) *
        ((exponent : ℝ) + ((residuePrime : ℝ) - 1)⁻¹) - 1
  action_trivial_after_cutoff :
    ∀ {r : ℝ}, cutoff < r → ∀ g : upper r, ∀ x : M, (g : Γ) • x = x

theorem chapter15_finite_flat_cutoff_is_a_last_break_bound
    {Γ M : Type*} [Group Γ] [AddCommGroup M] [MulAction Γ M] [Finite M]
    (D : Chapter15FiniteFlatCutoffData Γ M) :
    ∀ {r : ℝ}, D.cutoff < r → ∀ g : D.upper r, ∀ x : M, (g : Γ) • x = x := by
  sorry

/-! ## 15.3--15.4. Consequences for two-dimensional arithmetic -/

/-- The kernel of a finite-dimensional linear representation. -/
def chapter15RepresentationKernel
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Subgroup G :=
  MonoidHom.ker ρ

/-- A representation kernel is normal, so it defines a quotient Galois layer. -/
theorem chapter15_representation_kernel_normal
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    (chapter15RepresentationKernel ρ).Normal := by
  sorry

instance chapter15_representation_kernel_normal_instance
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    (chapter15RepresentationKernel ρ).Normal :=
  chapter15_representation_kernel_normal ρ

/-- The fixed field cut out by a representation of a finite Galois group. -/
def chapter15RepresentationFixedField
    {k K L V : Type*} [Semiring k] [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module k V]
    (ρ : Representation k (Gal(L / K)) V) : IntermediateField K L :=
  IntermediateField.fixedField (chapter15RepresentationKernel ρ)

/-- The finite quotient seen by a representation is the Galois group of its fixed field. -/
theorem chapter15_representation_quotient_is_fixed_field_galois_group
    {k K L V : Type*} [Semiring k] [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module k V]
    [FiniteDimensional K L] [IsGalois K L]
    (ρ : Representation k (Gal(L / K)) V) :
    Nonempty
      ((Gal(L / K) ⧸ chapter15RepresentationKernel ρ) ≃*
        Gal(chapter15RepresentationFixedField ρ / K)) := by
  sorry

/-- A finite-image representation together with the finite quotient through which it factors. -/
def chapter15FactorsThroughFiniteQuotient
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  ∃ (Q : Type*) (hQ : Group Q) (hQfinite : Finite Q),
     (letI : Group Q := hQ
      letI : Finite Q := hQfinite
      ∃ (π : G →* Q) (_hπ : Function.Surjective π)
       (ρQ : Representation k Q V), ρ = ρQ.comp π)

/-- The finite-image hypothesis for a representation of an arbitrary group. -/
def chapter15FiniteImageRepresentation
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  Set.Finite (Set.range ρ)

/-- A finite-image representation factors through its finite quotient image. -/
theorem chapter15_finite_image_representation_uses_finite_galois_layer_of_finite_image
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    (hfinite : chapter15FiniteImageRepresentation ρ) :
    chapter15FactorsThroughFiniteQuotient ρ := by
  sorry

/-- The finite quotient is the only Galois layer needed by a finite representation. -/
theorem chapter15_finite_image_representation_uses_finite_galois_layer
    {k G V : Type*} [Semiring k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    chapter15FactorsThroughFiniteQuotient ρ := by
  sorry

/-- In dimension two, the tame fixed-space codimension is exactly `0`, `1`, or `2`. -/
theorem chapter15_two_dimensional_tame_codimension_cases
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter15LowerRamificationFiltration G)
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) :
    chapter15Codimension ρ (F.group 0) = 0 ∨
      chapter15Codimension ρ (F.group 0) = 1 ∨
      chapter15Codimension ρ (F.group 0) = 2 := by
  sorry

/-- The permutation module on a finite G-set, in the canonical group-algebra model. -/
def chapter15PermutationRepresentation
    (k G X : Type*) [Field k] [Group G] [MulAction G X] :
    Representation k G (MonoidAlgebra k X) :=
  (Rep.ofMulAction k G X).ρ

/- The branch/action compatibility is explicit: a chosen permutation model is
   identified with the prime set, and the lower filtration is identified with
   the branch lower groups.  The last two fields are the local Hilbert and
   residue-degree normalizations; neither field assumes the conductor result. -/
structure Chapter15PrimeBranchPermutationData
    {A B G k X : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [Field k] [MulAction G X] [Finite X]
    [FiniteDimensional k (MonoidAlgebra k X)]
    (p : Ideal A) (P : Ideal B) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
    (F : Chapter15LowerRamificationFiltration G) where
  branch_equiv : X ≃ p.primesOver B
  branch_action : G →* Equiv.Perm (p.primesOver B)
  branch_action_compatible :
    ∀ (g : G) (x : X),
      branch_equiv (g • x) = branch_action g (branch_equiv x)
  branch_lower : ℕ → Subgroup G
  filtration_eq_branch_lower : ∀ i : ℕ, F.group i = branch_lower i
  residue_extension_separable : Prop
  residue_degree : ℕ
  residue_degree_eq : residue_degree = P.inertiaDeg A
  discriminant_eq_residue_degree_mul_different :
    chapter15DiscriminantExponent A B p =
      residue_degree * chapter15DifferentDisplacementSum F
  permutation_conductor_eq_residue_degree_mul_different :
    chapter15ArtinConductor F (chapter15PermutationRepresentation k G X) =
      (residue_degree : ℚ) *
        (chapter15DifferentDisplacementSum F : ℚ)

theorem chapter15_permutation_conductor_recovers_discriminant
    {A B G k X : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [Field k] [MulAction G X] [Finite X]
    [FiniteDimensional k (MonoidAlgebra k X)]
    (p : Ideal A) (P : Ideal B) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
    (F : Chapter15LowerRamificationFiltration G)
    (C : Chapter15PrimeBranchPermutationData p P F)
    (hbranches : (p.primesOver B).ncard = 1) :
    chapter15ArtinConductor F (chapter15PermutationRepresentation k G X) =
      (chapter15DiscriminantExponent A B p : ℚ) := by
  sorry

/- A one-point branch set has zero permutation conductor.  It is not the
embedding permutation representation used by the conductor--
discriminant identity. -/
theorem chapter15_one_branch_permutation_conductor_zero
    {G k X : Type*} [Field k] [Group G] [Finite G] [MulAction G X] [Finite X]
    [FiniteDimensional k (MonoidAlgebra k X)]
    (F : Chapter15LowerRamificationFiltration G) (hX : Nat.card X = 1) :
    chapter15ArtinConductor F (chapter15PermutationRepresentation k G X) = 0 := by
  sorry

/-- A field discriminant is an ideal-valued invariant, distinct in kind from a model discriminant. -/
abbrev Chapter15FieldDiscriminant (A : Type*) [Semiring A] := Ideal A

/-- The discriminant of a chosen Weierstrass model is coefficient-valued. -/
abbrev Chapter15WeierstrassDiscriminant (R : Type*) := R

end

end LastLib.Book03RamificationTheory.Chapter15
