import LastLib.Book03RamificationTheory.Chapter16.Section01TheRamificationDictionary
import LastLib.Book03RamificationTheory.Chapter15.Section02ACalculationProtocol
import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Factorization

namespace LastLib.Book03RamificationTheory.Chapter16

noncomputable section

open Ideal Polynomial
open LastLib.Book03RamificationTheory.Chapter15
open scoped BigOperators
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ## 16.2. A calculation protocol -/

/-- The certificate required before using an integral generator in a derivative formula. -/
def chapter16IntegralGeneratorCertificate
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (α : L) : Prop :=
  chapter15IntegralGeneratorCertificate A L α

/-- The monogenic presentation used by the canonical derivative formula. -/
def chapter16MonogenicPresentation
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X]) : Prop :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07MonogenicPresentation
    A B K L α f

/-- The derivative of a monic integral generator polynomial. -/
def chapter16DerivativeAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (α : B) : B :=
  LastLib.Book03RamificationTheory.Chapter07.chapter07DerivativeAt A B f α

theorem chapter16_different_eq_derivative_ideal
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B]
    [IsDedekindDomain B] [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter16MonogenicPresentation A B K L α f) :
    chapter16DifferentIdeal A B =
      Ideal.span ({chapter16DerivativeAt A B f α} : Set B) := by
  sorry

/-- The residue extension separability check in the protocol. -/
def chapter16ResidueExtensionSeparable
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  Algebra.IsSeparable k l

/-- The ramification index attached to a selected prime. -/
def chapter16RamificationIndex
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.ramificationIdx A

/-- The residue degree attached to a selected prime. -/
def chapter16ResidueDegree
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.inertiaDeg A

/-- A finite local calculation checklist for the residue and ideal data. -/
structure Chapter16LocalCalculationChecklist
    {A B k l : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Field k] [Field l] [Algebra k l]
    (p : Ideal A) (P : Ideal B) [p.IsPrime] [P.IsPrime]
    [P.LiesOver p] where
  residue_extension_separable : chapter16ResidueExtensionSeparable k l
  ramification_index : ℕ
  residue_degree : ℕ
  ramification_index_eq :
    ramification_index = chapter16RamificationIndex (A := A) P
  residue_degree_eq : residue_degree = chapter16ResidueDegree (A := A) P

/-- The displacement profile whose membership recovers the lower groups. -/
def chapter16DisplacementProfile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A) : ℕ → Prop :=
  chapter15DisplacementProfile A σ

/-- The valuation displacement of an automorphism on an element. -/
def chapter16ValuationDisplacement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AddValuation L (WithTop ℤ))
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K w.toValuation.valuationSubring)
    (x : L) : WithTop ℤ :=
  w ((σ : Gal(L / K)) x - x)

@[simp] theorem chapter16_displacement_profile_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A)
    (i : ℕ) :
    chapter16DisplacementProfile A σ i ↔
      σ ∈ chapter15LowerRamificationGroup K A i := by
  rfl

theorem chapter16_lower_group_membership_is_displacement_check
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A)
    (i : ℕ) :
    σ ∈ chapter15LowerRamificationGroup K A i ↔
      chapter16DisplacementProfile A σ i := by
  exact (chapter16_displacement_profile_iff A σ i).symm

theorem chapter16_inertia_iff_positive_valuation_displacement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AddValuation L (WithTop ℤ))
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K w.toValuation.valuationSubring) :
    σ ∈ chapter15InertiaGroup K w.toValuation.valuationSubring ↔
      ∀ x : w.toValuation.valuationSubring,
        chapter16ValuationDisplacement w σ (x : L) > 0 := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.inertia_iff_positive_valuation_displacement
      w σ

/-- The inertia and tame-character data used after the Galois check. -/
abbrev Chapter16TameCharacterData
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G)
    (C : Type*) [Group C] [Finite C] :=
  Chapter15TameCharacterData F C

structure Chapter16GaloisCalculationStep
    {G : Type*} [Group G] [Finite G]
    (F : Chapter16LowerRamificationFiltration G)
    (C : Type*) [Group C] [Finite C] where
  inertia : Subgroup G
  inertia_eq_lower_zero : inertia = F.group 0
  tame_character : Chapter16TameCharacterData F C

/-- The lower-numbering compatibility condition for a quotient. -/
def chapter16LowerQuotientCheck
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (F : Chapter16LowerRamificationFiltration G)
    (FQ : Chapter16LowerRamificationFiltration Q)
    (π : G →* Q) : Prop :=
  chapter16LowerQuotientCompatibility F FQ π

/-- The upper-numbering quotient check. -/
def chapter16UpperQuotientCheck
    {G Q : Type*} [Group G] [Group Q]
    (U : ℝ → Subgroup G) (UQ : ℝ → Subgroup Q) (π : G →* Q) : Prop :=
  chapter16UpperQuotientCompatibility U UQ π

/-- The ring-level lower group used in Hilbert's different formula. -/
def chapter16RingLowerRamificationGroup
    {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]
    (P : Ideal B) (i : ℕ)
    (hstable : ∀ g : G, ∀ x : B,
      x ∈ P ^ i ↔ g • x ∈ P ^ i) : Subgroup G :=
  chapter15RingLowerRamificationGroup P i hstable

/-- The different exponent at a selected prime. -/
noncomputable def chapter16DifferentExponent
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] (P : Ideal B) : ℕ :=
  chapter15DifferentExponent A B P

/-- The discriminant exponent at a selected prime downstairs. -/
noncomputable def chapter16DiscriminantExponent
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B] (p : Ideal A) : ℕ :=
  chapter15DiscriminantExponent A B p

/-- Hilbert's formula identifies the different exponent with accumulated displacement. -/
theorem chapter16_hilbert_different_formula
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
  sorry

/-- The derivative and Hilbert calculations agree whenever both are certified. -/
theorem chapter16_derivative_and_hilbert_calculations_agree
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [Finite G]
    (P : Ideal B) (F : Chapter16LowerRamificationFiltration G) (d : ℕ)
    (hderivative : d = chapter16DifferentExponent A B P)
    (hhilbert : d = chapter16DifferentDisplacementSum F) :
    chapter16DifferentExponent A B P =
      chapter16DifferentDisplacementSum F := by
  exact hderivative.symm.trans hhilbert

/-- The derivative element supplied by a certified integral generator lies in the different. -/
theorem chapter16_generator_derivative_mem_different
    {A B K L : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra A L]
    [Algebra B L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsFractionRing B L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]
    (α : B)
    (hα : Algebra.adjoin K ({algebraMap B L α} : Set L) = ⊤) :
    aeval α (derivative (minpoly A α)) ∈ chapter16DifferentIdeal A B := by
  sorry

/-- The different is multiplicative in a tower, with the lower different mapped upstairs. -/
theorem chapter16_different_ideal_transitivity
    {A B C : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    chapter16DifferentIdeal A C =
      chapter16DifferentIdeal B C *
        (chapter16DifferentIdeal A B).map (algebraMap B C) := by
  sorry

/-- The exponent form of different transitivity at a compatible prime tower. -/
theorem chapter16_different_exponent_tower
    {A B C : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsPrime] [P.IsPrime] [Q.IsPrime]
    [P.LiesOver p] [Q.LiesOver P] :
    chapter16DifferentExponent A C Q =
      chapter16DifferentExponent B C Q +
        Q.ramificationIdx B * chapter16DifferentExponent A B P := by
  sorry

/-- In the one-branch local situation, the norm of the different gives `δ = f d`. -/
theorem chapter16_discriminant_exponent_eq_residue_degree_mul_different
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [p.IsPrime] [p.IsMaximal]
    [P.IsPrime] [P.LiesOver p]
    (hbranches : (p.primesOver B).ncard = 1) :
    chapter16DiscriminantExponent A B p =
      chapter16ResidueDegree (A := A) P * chapter16DifferentExponent A B P := by
  sorry

/-- The fixed subspace used in the final representation step. -/
def chapter16FixedSubspace
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (H : Subgroup G) : Submodule k V :=
  chapter15FixedSubspace ρ H

theorem chapter16_mem_fixed_subspace_iff
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (H : Subgroup G) (v : V) :
    v ∈ chapter16FixedSubspace ρ H ↔ ∀ h : H, ρ h v = v := by
  rfl

end

end LastLib.Book03RamificationTheory.Chapter16
