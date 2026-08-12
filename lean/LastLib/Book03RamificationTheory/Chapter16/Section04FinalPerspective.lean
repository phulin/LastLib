import LastLib.Book03RamificationTheory.Chapter16.Section03ConsequencesForTwoDimensionalArithmetic
import LastLib.Book03RamificationTheory.Chapter15.Section04FinalPerspective
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace LastLib.Book03RamificationTheory.Chapter16

noncomputable section

open LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
open LastLib.Book03RamificationTheory.Chapter15

/-! ## 16.4. Final perspective -/

/-- The lower group in the canonical valuation-ring realization. -/
abbrev chapter16LowerRamificationGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ) :
    Subgroup (chapter05DecompositionGroup K A) :=
  chapter15LowerRamificationGroup K A i

/-- Inertia is the first lower group in the canonical realization. -/
abbrev chapter16InertiaGroup
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    Subgroup (chapter05DecompositionGroup K A) :=
  chapter15InertiaGroup K A

theorem chapter16_first_lower_group_eq_inertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter16LowerRamificationGroup K A 1 = chapter16InertiaGroup K A := by
  exact chapter15_first_lower_group_eq_inertia A

theorem chapter16_inertia_is_residue_action_kernel
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter16InertiaGroup F A =
      MonoidHom.ker (chapter05ResidueAction F A) := by
  exact inertia_group_is_residue_action_kernel A

theorem chapter16_inertia_mem_iff_residue_fixed
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E)
    (σ : chapter05DecompositionGroup F A) :
    σ ∈ chapter16InertiaGroup F A ↔
      ∀ x : IsLocalRing.ResidueField A,
        chapter05ResidueAction F A σ x = x := by
  exact inertia_mem_iff_residue_fixed A σ

theorem chapter16_residue_action_exact_sequence
    {D Q : Type*} [Group D] [Group Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Function.MulExact (Subgroup.subtype (MonoidHom.ker ρ)) ρ ∧
      Function.Surjective ρ := by
  exact residue_action_exact_sequence ρ hρ

theorem chapter16_lower_group_mem_iff_congruence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (i : ℕ)
    (σ : chapter05DecompositionGroup K A) :
    σ ∈ chapter16LowerRamificationGroup K A i ↔
      ∀ x : A, (σ • x - x) ∈ (IsLocalRing.maximalIdeal A) ^ i := by
  rfl

/-- The trace-dual lattice used to measure failure of integral self-duality. -/
noncomputable def chapter16TraceDualLattice
    (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] : Submodule B L :=
  chapter15TraceDualLattice A K B L

theorem chapter16_mem_trace_dual_iff
    (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (x : L) :
    x ∈ chapter16TraceDualLattice A K B L ↔
      ∀ y : B, algebraMap B L y ∈ (1 : Submodule B L) →
        Algebra.trace K L (x * algebraMap B L y) ∈ Set.range (algebraMap A K) := by
  exact chapter15_mem_trace_dual_iff A K B L x

theorem chapter16_codimension_eq_zero_iff
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) :
    chapter16Codimension ρ H = 0 ↔
      chapter16FixedSubspace ρ H = ⊤ := by
  sorry

theorem chapter16_fixed_subspace_antitone
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) {H J : Subgroup G} (hHJ : H ≤ J) :
    chapter16FixedSubspace ρ J ≤ chapter16FixedSubspace ρ H := by
  sorry

/-- The same Hilbert sum is the different exponent used by the final dictionary. -/
theorem chapter16_hilbert_sum_is_the_different_exponent
    {A B G : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [IsGaloisGroup G A B]
    (P : Ideal B) (F : Chapter16LowerRamificationFiltration G)
    (hstable : ∀ i : ℕ, ∀ g : G, ∀ x : B,
      x ∈ P ^ i ↔ g • x ∈ P ^ i)
    (hF : ∀ i : ℕ,
      F.group i = chapter16RingLowerRamificationGroup P i (hstable i)) :
    chapter16DifferentExponent A B P =
      chapter16DifferentDisplacementSum F := by
  exact chapter16_hilbert_different_formula P F hstable hF

end

end LastLib.Book03RamificationTheory.Chapter16
