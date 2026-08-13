import LastLib.Book03RamificationTheory.Chapter15.Section01TheRamificationDictionary
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Factorization

namespace LastLib.Book03RamificationTheory.Chapter15

noncomputable section

open Ideal Polynomial
open scoped BigOperators
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ## 15.2. A calculation protocol -/

/--
The certificate required before using a generator in the derivative formula:
the element is integral and its order is the full integral closure.
-/
def chapter15IntegralGeneratorCertificate
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (α : L) : Prop :=
  IsIntegral A α ∧
    (integralClosure A L : Set L) =
      (Algebra.adjoin A ({α} : Set L) : Set L)

/-- Residue separability is kept as a named check in the calculation protocol. -/
def chapter15ResidueExtensionSeparable
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
  Algebra.IsSeparable k l

/-- The local ramification index in the canonical ideal interface. -/
def chapter15RamificationIndex
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.ramificationIdx A

/-- The local residue degree in the canonical ideal interface. -/
def chapter15ResidueDegree
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal B) : ℕ :=
  P.inertiaDeg A

/-- The displacement profile used to form lower groups. -/
def chapter15DisplacementProfile
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
  (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) :
    ℕ → Prop :=
  fun i =>
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence A (i + 1) σ

@[simp]
theorem chapter15_displacement_profile_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (σ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A)
    (i : ℕ) :
    chapter15DisplacementProfile A σ i ↔
      σ ∈ chapter15LowerRamificationGroup K A i := by
  rfl

/-- A book-facing record for the tame character used in explicit calculations. -/
structure Chapter15TameCharacterData
    {G : Type*} [Group G] [Finite G]
    (F : Chapter15LowerRamificationFiltration G)
    (C : Type*) [Group C] [Finite C] where
  character : chapter15Layer F 0 →* C
  injective : Function.Injective character
  cyclic : IsCyclic C

/-- Hilbert's different formula in a ring-level lower-group interface. -/
def chapter15RingLowerRamificationGroup
    {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]
    (P : Ideal B) (i : ℕ)
    (hstable : ∀ g : G, ∀ x : B,
      x ∈ P ^ (i + 1) ↔ g • x ∈ P ^ (i + 1)) : Subgroup G := by
  refine
    { carrier := {g | ∀ x : B, g • x - x ∈ P ^ (i + 1)}
      one_mem' := by
        intro x
        simp
      mul_mem' := by
        intro g h hg hh x
        have h₁ : g • (h • x - x) ∈ P ^ (i + 1) :=
          (hstable g (h • x - x)).mp (hh x)
        have h₂ : g • x - x ∈ P ^ (i + 1) := hg x
        have hrewrite : g • h • x - x =
            g • (h • x - x) + (g • x - x) := by
          rw [smul_sub]
          exact (sub_add_sub_cancel _ _ _).symm
        rw [mul_smul, hrewrite]
        exact (P ^ (i + 1)).add_mem h₁ h₂
      inv_mem' := by
        intro g hg x
        have h₁ : g⁻¹ • (g • x - x) ∈ P ^ (i + 1) :=
          (hstable g⁻¹ (g • x - x)).mp (hg x)
        have h₂ : -(g⁻¹ • (g • x - x)) ∈ P ^ (i + 1) :=
          (P ^ (i + 1)).neg_mem h₁
        simpa [smul_sub, smul_smul] using h₂ }

/-- Hilbert's formula identifies the different exponent with accumulated displacement. -/
theorem chapter15_hilbert_different_formula
    {A B G : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [IsGaloisGroup G A B]
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (F : Chapter15LowerRamificationFiltration G)
    (hstable : ∀ i : ℕ, ∀ g : G, ∀ x : B,
      x ∈ P ^ (i + 1) ↔ g • x ∈ P ^ (i + 1))
    (hF : ∀ i : ℕ,
      F.group i = chapter15RingLowerRamificationGroup P i (hstable i)) :
    chapter15DifferentExponent A B P =
      chapter15DifferentDisplacementSum F := by
  sorry

/-- If both calculations are available, their exponents agree. -/
theorem chapter15_derivative_and_hilbert_calculations_agree
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [Finite G]
    (P : Ideal B) (F : Chapter15LowerRamificationFiltration G) (d : ℕ)
    (hderivative : d = chapter15DifferentExponent A B P)
    (hhilbert : d = chapter15DifferentDisplacementSum F) :
    chapter15DifferentExponent A B P =
      chapter15DifferentDisplacementSum F := by
  exact hderivative.symm.trans hhilbert

/-- Derivative calculation of the different, available after the generator certificate. -/
theorem chapter15_generator_derivative_mem_different
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
    aeval α (derivative (minpoly A α)) ∈ chapter15DifferentIdeal A B := by
  sorry

/-- The different is multiplicative in a tower, with the lower different mapped upstairs. -/
theorem chapter15_different_ideal_transitivity
    {A B C : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    chapter15DifferentIdeal A C =
      chapter15DifferentIdeal B C *
        (chapter15DifferentIdeal A B).map (algebraMap B C) := by
  sorry

/-- The exponent form of different transitivity at a compatible prime tower. -/
theorem chapter15_different_exponent_tower
    {A B C : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [p.IsPrime] [p.IsMaximal] [P.IsPrime] [P.IsMaximal] [Q.IsPrime] [Q.IsMaximal]
    [P.LiesOver p] [Q.LiesOver P] :
    chapter15DifferentExponent A C Q =
      chapter15DifferentExponent B C Q +
        Q.ramificationIdx B * chapter15DifferentExponent A B P := by
  sorry

/-- In the one-branch local situation, the norm of the different gives `δ = f d`. -/
/- SOURCE_ISSUE: In §13.5, the displayed identity
   `f * ∑ᵢ (|Gᵢ| - 1) = δ(L/K)` follows the wording
   "Let ρ have finite image G, let L/K be its fixed field, and assume that
   this extension has separable residue extension."  In a general
   Dedekind/global setting this does not select a single branch or remove
   branch-count contributions (a complete or henselian local base does).
   The minimal principled correction is the explicit one-branch hypothesis
   below. -/
theorem chapter15_discriminant_exponent_eq_residue_degree_mul_different
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (p : Ideal A) (P : Ideal B) [p.IsPrime] [p.IsMaximal]
    [P.IsPrime] [P.LiesOver p]
    (hbranches : (p.primesOver B).ncard = 1) :
    chapter15DiscriminantExponent A B p =
      P.inertiaDeg A * chapter15DifferentExponent A B P := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter15
