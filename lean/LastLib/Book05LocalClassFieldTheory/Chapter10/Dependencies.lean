import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section04AbsoluteValueNormalizations
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section02TheFirstQuotient
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section08CompletenessAndInverseLimitsOfUnits
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section04TheTotallyRamifiedCase
import LastLib.Book05LocalClassFieldTheory.Chapter02.Section02OpenSubgroupsOfFiniteIndex
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section06FiniteReciprocity

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

open scoped Pointwise

/-!
## Interfaces shared by Chapter 10

The source chapter uses the standard local-field notation `K`, `O`, `k`, and
`Uⁿ`.  The definitions below keep those objects tied to Mathlib's valuation
subring and to the unit filtration already exposed by Book 2.  The records
marked as dependency interfaces name the genuinely missing earlier
constructions; they do not package any of Chapter 10's norm conclusions.
-/

/- The canonical valuation-ring and residue-field objects attached to an
   additive valuation. -/
abbrev Chapter10ValuationRing {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : ValuationSubring K :=
  v.toValuation.valuationSubring

abbrev Chapter10ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (Chapter10ValuationRing v)

abbrev Chapter10RingUnitGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  (Chapter10ValuationRing v)ˣ

/- The valuation-ring filtration and its transport to `Kˣ` are the canonical
   `1 + 𝔪ⁿ` groups from Book 2. -/
abbrev Chapter10UnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    Subgroup (Chapter10RingUnitGroup v) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
    (Chapter10ValuationRing v) n

abbrev Chapter10FieldUnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10FieldUnitFiltration
    (Chapter10ValuationRing v) n

abbrev Chapter10UnitQuotient {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Type _ :=
  Chapter10RingUnitGroup v ⧸ Chapter10UnitFiltration v n

abbrev Chapter10PrecisionQuotient {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Type _ :=
  Chapter10ValuationRing v ⧸
    (IsLocalRing.maximalIdeal (Chapter10ValuationRing v)) ^ n

def chapter10UnitReduction {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Chapter10RingUnitGroup v →* (Chapter10ResidueField v)ˣ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitReduction
    (Chapter10ValuationRing v)

def chapter10RingUnitInField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Chapter10RingUnitGroup v →* Kˣ :=
  Units.map (Chapter10ValuationRing v).subtype.toMonoidHom

def chapter10PrecisionUnitReduction {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    Chapter10RingUnitGroup v →*
      (Chapter10PrecisionQuotient v n)ˣ :=
  Units.map
    (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (Chapter10ValuationRing v)) ^ n)).toMonoidHom

theorem chapter10_first_unit_quotient_equiv_residue_units
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    Nonempty
      (Chapter10UnitQuotient v 1 ≃*
        (Chapter10ResidueField v)ˣ) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_first_unit_quotient_equiv_residue_units
      (Chapter10ValuationRing v)

theorem chapter10_unit_filtration_descending
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    ∀ n : ℕ, Chapter10UnitFiltration v (n + 1) ≤
      Chapter10UnitFiltration v n := by
  intro n
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_descending
      (Chapter10ValuationRing v) n

theorem chapter10_field_unit_filtration_zero_one
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) :
    Chapter10FieldUnitFiltration v 0 =
        (Chapter10ValuationRing v).unitGroup ∧
      Chapter10FieldUnitFiltration v 1 =
        (Chapter10ValuationRing v).principalUnitGroup := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_field_filtration_zero_one
      (Chapter10ValuationRing v)

/- A uniformizer/unit coordinate package with exactly the local hypotheses used
   by the chapter.  `complete` is Book 2's normalized complete additive
   valuation interface; `residue_finite` and `valuationRing_dvr` are kept
   explicit because later finite-precision theorems consume them separately. -/
structure Chapter10LocalFieldProfile (K : Type*) [Field K] where
  valuation : AddValuation K (WithTop ℤ)
  complete :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteAdditiveValuation
      valuation
  residue_finite : Finite (Chapter10ResidueField valuation)
  valuationRing_dvr : IsDiscreteValuationRing (Chapter10ValuationRing valuation)
  uniformizer : Kˣ
  uniformizer_value : valuation (uniformizer : K) = (1 : WithTop ℤ)
  residueCharacteristic : ℕ
  residueCharacteristic_prime : Nat.Prime residueCharacteristic
  residueCharacteristic_charP :
    CharP (Chapter10ResidueField valuation) residueCharacteristic

instance chapter10LocalFieldProfile_dvr
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) :
    IsDiscreteValuationRing (Chapter10ValuationRing D.valuation) :=
  D.valuationRing_dvr

instance chapter10LocalFieldProfile_finite_residue
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) :
    Finite (Chapter10ResidueField D.valuation) :=
  D.residue_finite

noncomputable instance chapter10LocalFieldProfile_fintype_residue
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) :
    Fintype (Chapter10ResidueField D.valuation) := by
  exact Fintype.ofFinite _

abbrev Chapter10LocalUnitGroup {K : Type*} [Field K]
    (D : Chapter10LocalFieldProfile K) : Type _ :=
  Chapter10RingUnitGroup D.valuation

def chapter10LocalUnitSubgroup {K : Type*} [Field K]
    (D : Chapter10LocalFieldProfile K) : Subgroup Kˣ :=
  Chapter10FieldUnitFiltration D.valuation 0

def chapter10PrincipalUnitSubgroup {K : Type*} [Field K]
    (D : Chapter10LocalFieldProfile K) (n : ℕ) : Subgroup Kˣ :=
  Chapter10FieldUnitFiltration D.valuation n

/- The subgroup `π^(mℤ) Uⁿ`, used repeatedly in the explicit formulas. -/
def chapter10ValueUnitSubgroup {K : Type*} [Field K]
    (D : Chapter10LocalFieldProfile K) (π : Kˣ) (m n : ℕ) : Subgroup Kˣ :=
  Subgroup.zpowers (π ^ m) ⊔ Chapter10FieldUnitFiltration D.valuation n

theorem chapter10_mem_value_unit_subgroup_iff
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (π : Kˣ) (m n : ℕ) (x : Kˣ) :
    x ∈ chapter10ValueUnitSubgroup D π m n ↔
      ∃ z : ℤ, ∃ u : Chapter10FieldUnitFiltration D.valuation n,
        x = π ^ ((m : ℤ) * z) * (u : Kˣ) := by
  sorry

/- The algebraic norm and the corresponding multiplicative norm subgroup. -/
noncomputable def chapter10NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

def chapter10NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (chapter10NormHom K L).range

abbrev Chapter10NormQuotient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  Kˣ ⧸ chapter10NormSubgroup K L

theorem chapter10_mem_normSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter10NormSubgroup K L ↔
      ∃ y : Lˣ, chapter10NormHom K L y = x := by
  simp [chapter10NormSubgroup]

/- A finite Artin map is the earlier finite-reciprocity interface with the
   norm kernel made explicit. -/
structure Chapter10FiniteArtinMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  reciprocity : Kˣ →* Gal(L / K)
  kernel_eq_norm : reciprocity.ker = chapter10NormSubgroup K L
  surjective : Function.Surjective reciprocity

noncomputable def chapter10ArtinQuotientEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (A : Chapter10FiniteArtinMap K L) :
    Chapter10NormQuotient K L ≃* Gal(L / K) := by
  let hker : A.reciprocity.ker = chapter10NormSubgroup K L :=
    A.kernel_eq_norm
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        A.reciprocity A.surjective)

/- Total ramification is expressed using the canonical valuation-extension and
   residue-agreement predicates from Book 2. -/
def Chapter10TotallyRamifiedValuedExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationExtension
      vK vL ∧
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationScaling
      vK vL e ∧
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TotallyRamifiedResidueAgreement
      vK vL

/- LOCAL_DEPENDENCY_GUESS: Chapter 6's formal-module construction should
   provide these radical fields, their compatible normalized valuations, and
   the torsion labeling.  The fields below deliberately stop short of any
   norm or reciprocity statement. -/
structure Chapter10TameRadicalData
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (e : ℕ) where
  extensionValuation : AddValuation L (WithTop ℤ)
  extension_complete :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationComplete
      extensionValuation
  extension_residue_finite :
    Finite
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField
        extensionValuation)
  extension_dvr :
    IsDiscreteValuationRing
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing
        extensionValuation)
  valuation_extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationExtension
      D.valuation extensionValuation
  positive : 0 < e
  tame : Nat.Coprime e D.residueCharacteristic
  unitFactor : Kˣ
  root : L
  root_nonzero : root ≠ 0
  root_equation :
    root ^ e =
      algebraMap K L ((unitFactor : K) * (D.uniformizer : K))
  generates : Algebra.adjoin K ({root} : Set L) = ⊤
  roots_of_unity_in_base :
    ∀ ζ : AlgebraicClosure K, ζ ^ e = 1 →
      ∃ z : K, algebraMap K (AlgebraicClosure K) z = ζ

noncomputable def chapter10NormOfRootUnit
    {K : Type*} [Field K] {D : Chapter10LocalFieldProfile K}
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    {e : ℕ} (T : Chapter10TameRadicalData D L e) : Kˣ :=
  chapter10NormHom K L (Units.mk0 T.root T.root_nonzero)

/- LOCAL_DEPENDENCY_GUESS: the torsion layers of the preceding formal module
   come with a primitive point and a labeling by the finite unit quotient. -/
structure Chapter10FormalTorsionSystem
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (Ω : Type*) [Field Ω] [Algebra K Ω] where
  torsionField : ℕ → IntermediateField K Ω
  finite : ∀ n, FiniteDimensional K (torsionField n)
  galois : ∀ n, IsGalois K (torsionField n)
  tower : ∀ n, torsionField n ≤ torsionField (n + 1)
  primitivePoint : ∀ n, torsionField n
  torsionLabel : ∀ n,
    Chapter10UnitQuotient D.valuation n →* Gal(torsionField n / K)
  formalAction : ∀ n,
    Chapter10UnitQuotient D.valuation n →* Gal(torsionField n / K)
  torsionLabel_apply : ∀ n a,
    torsionLabel n a = formalAction n a

/- The finite ambient extension used in the congruence construction. -/
structure Chapter10ExplicitAmbientExtension
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (m n : ℕ) where
  field : IntermediateField K (AlgebraicClosure K)
  [finite : FiniteDimensional K field]
  [galois : IsGalois K field]
  abelian : ∀ σ τ : Gal(field / K), σ * τ = τ * σ
  normSubgroup_eq :
    chapter10NormSubgroup K field =
      chapter10ValueUnitSubgroup D D.uniformizer m n
  artin : Chapter10FiniteArtinMap K field

/- The finite conductor assertion is the unit-depth part of an open norm
   subgroup. -/
def Chapter10FiniteConductor
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (H : Subgroup Kˣ) : Prop :=
  ∃ n : ℕ, Chapter10FieldUnitFiltration D.valuation n ≤ H

/- Power subgroups are used for residue conditions and square classes. -/
def chapter10PowerMap {G : Type*} [CommGroup G] (e : ℕ) : G →* G where
  toFun x := x ^ e
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]

def chapter10PowerSubgroup {G : Type*} [CommGroup G] (e : ℕ) : Subgroup G :=
  (chapter10PowerMap e).range

theorem chapter10_mem_powerSubgroup_iff
    {G : Type*} [CommGroup G] (e : ℕ) (x : G) :
    x ∈ chapter10PowerSubgroup e ↔ ∃ y : G, y ^ e = x := by
  rfl

theorem chapter10_powerSubgroup_is_normal
    {G : Type*} [CommGroup G] (e : ℕ) :
    (chapter10PowerSubgroup (G := G) e).Normal := by
  infer_instance

def chapter10ResidueUnitIsPower
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (e : ℕ) (u : Chapter10RingUnitGroup v) : Prop :=
  chapter10UnitReduction v u ∈
    chapter10PowerSubgroup (G := (Chapter10ResidueField v)ˣ) e

def chapter10TeichmullerPowerSubgroup
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (e : ℕ)
    (s : (Chapter10ResidueField v)ˣ →* Chapter10RingUnitGroup v) :
    Subgroup Kˣ :=
  Subgroup.map (chapter10RingUnitInField v)
    (Subgroup.map s
      (chapter10PowerSubgroup (G := (Chapter10ResidueField v)ˣ) e))

def chapter10TeichmullerSectionSpec
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (q : ℕ) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10TeichmullerSectionSpec
    (Chapter10ValuationRing v) q

theorem chapter10_teichmuller_section_exists_unique
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    [Fintype (Chapter10ResidueField v)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter10ValuationRing v))
      (Chapter10ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter10ValuationRing v)) :
    ∃! s : (Chapter10ResidueField v)ˣ →* Chapter10RingUnitGroup v,
      (∀ a, chapter10UnitReduction v (s a) = a) ∧
        (∀ a, (s a) ^ (Fintype.card (Chapter10ResidueField v) - 1) = 1) ∧
      (∀ a u, chapter10UnitReduction v u = a →
          u ^ (Fintype.card (Chapter10ResidueField v) - 1) = 1 →
            u = s a) := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_teichmuller_section_exists_unique
      (Chapter10ValuationRing v) hcomplete hDVR

def chapter10NegOneUnit (K : Type*) [Field K] : Kˣ :=
  Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
