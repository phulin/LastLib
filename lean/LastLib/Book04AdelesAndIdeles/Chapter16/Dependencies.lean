import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.AddChar
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace LastLib.Book04AdelesAndIdeles.Chapter16

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators NNReal nonZeroDivisors NumberField RestrictedProduct Topology

/-!
The book uses the usual number-field adeles and ideles.  The aliases in this
file keep the chapter-facing vocabulary separate from the canonical Mathlib
objects, so later declarations can be read in the order of the text.
-/

abbrev Chapter16FiniteAdeleRing (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

abbrev Chapter16AdeleRing (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (𝓞 K) K

abbrev Chapter16FiniteIdeles (K : Type*) [Field K] [NumberField K] :=
  (Chapter16FiniteAdeleRing K)ˣ

abbrev Chapter16Ideles (K : Type*) [Field K] [NumberField K] :=
  (Chapter16AdeleRing K)ˣ

abbrev Chapter16PrincipalAdeles (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing.principalSubgroup (𝓞 K) K

abbrev Chapter16AdditiveQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter16AdeleRing K ⧸ Chapter16PrincipalAdeles K

def chapter16ArchimedeanIntegerEmbedding (K : Type*) [Field K] [NumberField K] :
    (𝓞 K) →+ NumberField.InfiniteAdeleRing K where
  toFun := fun a => algebraMap K (NumberField.InfiniteAdeleRing K) (a : K)
  map_zero' := by simp
  map_add' := by simp

def chapter16ArchimedeanIntegerLattice (K : Type*) [Field K] [NumberField K] :
    AddSubgroup (NumberField.InfiniteAdeleRing K) :=
  (chapter16ArchimedeanIntegerEmbedding K).range

abbrev Chapter16LogarithmicUnitLattice (K : Type*) [Field K] [NumberField K] :=
  (NumberField.Units.unitLattice K).toAddSubgroup

def chapter16PrincipalIdeleHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter16Ideles K :=
  Units.map (algebraMap K (Chapter16AdeleRing K))

def chapter16PrincipalIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16Ideles K) :=
  (chapter16PrincipalIdeleHom K).range

instance chapter16PrincipalIdeles_normal
    (K : Type*) [Field K] [NumberField K] :
    (chapter16PrincipalIdeles K).Normal := by
  exact ⟨by
    intro n hn g
    rw [mul_assoc, mul_comm n g⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    exact hn⟩

abbrev Chapter16IdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter16Ideles K ⧸ chapter16PrincipalIdeles K

instance chapter16IdeleClassGroup_isMulCommutative
    (K : Type*) [Field K] [NumberField K] :
    IsMulCommutative (Chapter16IdeleClassGroup K) := by
  apply Function.Surjective.mul_comm
    (f := (QuotientGroup.mk' (chapter16PrincipalIdeles K)).toMulHom)
  · exact QuotientGroup.mk'_surjective (chapter16PrincipalIdeles K)
  · exact IsMulCommutative.of_comm (fun a b => mul_comm a b)

def chapter16PrincipalFiniteIdeleHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter16FiniteIdeles K :=
  Units.map (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K)

def chapter16PrincipalFiniteIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16FiniteIdeles K) :=
  (chapter16PrincipalFiniteIdeleHom K).range

def chapter16FiniteIdeleProjection (K : Type*) [Field K] [NumberField K] :
    Chapter16Ideles K →* Chapter16FiniteIdeles K :=
  Units.map ((RingHom.snd (NumberField.InfiniteAdeleRing K)
    (Chapter16FiniteAdeleRing K)).toMonoidHom)

theorem chapter16FiniteIdeleProjection_principal
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter16FiniteIdeleProjection K (chapter16PrincipalIdeleHom K a) =
      chapter16PrincipalFiniteIdeleHom K a := by
  sorry

def chapter16AdditiveTail (K : Type*) [Field K] [NumberField K]
    (x : Chapter16FiniteAdeleRing K) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    x v ∈ v.adicCompletionIntegers K

def chapter16LocalCompletionUnit (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : Prop :=
  ∃ u : (v.adicCompletionIntegers K)ˣ,
    ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = x

def chapter16IdeleUnitTail (K : Type*) [Field K] [NumberField K]
    (x : Chapter16Ideles K) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    Valued.v ((x : Chapter16AdeleRing K).2 v) = 1

abbrev Chapter16PositiveReals : Type := ℝ≥0ˣ

def chapter16IdeleModuleValue (K : Type*) [Field K] [NumberField K]
    (x : Chapter16Ideles K) : ℝ≥0 :=
  (∏ v : InfinitePlace K,
      (⟨‖((x : Chapter16AdeleRing K).1 v)‖, norm_nonneg _⟩ : ℝ≥0) ^ v.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (⟨‖((x : Chapter16AdeleRing K).2 v)‖, norm_nonneg _⟩ : ℝ≥0)

theorem chapter16IdeleModuleValue_ne_zero
    (K : Type*) [Field K] [NumberField K] (x : Chapter16Ideles K) :
    chapter16IdeleModuleValue K x ≠ 0 := by
  sorry

def chapter16IdeleModule (K : Type*) [Field K] [NumberField K] :
    Chapter16Ideles K →* Chapter16PositiveReals where
  toFun := fun x =>
    Units.mk0 (chapter16IdeleModuleValue K x) (chapter16IdeleModuleValue_ne_zero K x)
  map_one' := by sorry
  map_mul' := by sorry

def chapter16IdeleDegree (K : Type*) [Field K] [NumberField K]
    (x : Chapter16Ideles K) : ℝ :=
  -Real.log (chapter16IdeleModuleValue K x)

def chapter16IdeleDegreeHom (K : Type*) [Field K] [NumberField K] :
    Chapter16Ideles K →* Multiplicative ℝ where
  toFun := fun x => Multiplicative.ofAdd (chapter16IdeleDegree K x)
  map_one' := by sorry
  map_mul' := by sorry

def chapter16NormOneIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16Ideles K) :=
  (chapter16IdeleModule K).ker

def chapter16DegreeZeroIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16Ideles K) :=
  (chapter16IdeleDegreeHom K).ker

def chapter16NormOneClassSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16IdeleClassGroup K) :=
  Subgroup.map (QuotientGroup.mk' (chapter16PrincipalIdeles K))
    (chapter16NormOneIdeles K)

abbrev Chapter16NormOneClassGroup (K : Type*) [Field K] [NumberField K] :=
  chapter16NormOneClassSubgroup K

abbrev Chapter16DivisorGroup (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K) →₀ ℤ

def chapter16LocalValuationExponent (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : ℤ :=
  by
    classical
    exact if _hx : x = 0 then 0
      else (WithZero.unzero (by sorry : Valued.v x ≠ 0)).toAdd

def chapter16FiniteIdeleValuationValue (K : Type*) [Field K] [NumberField K]
    (x : Chapter16FiniteIdeles K) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  chapter16LocalValuationExponent K v ((x : Chapter16FiniteAdeleRing K) v)

theorem chapter16FiniteIdeleValuationValue_finite_support
    (K : Type*) [Field K] [NumberField K] (x : Chapter16FiniteIdeles K) :
    (Function.support (chapter16FiniteIdeleValuationValue K x)).Finite := by
  sorry

theorem chapter16FiniteIdeleValuation_is_divisor
    (K : Type*) [Field K] [NumberField K] (x : Chapter16FiniteIdeles K) :
    ∃ D : Chapter16DivisorGroup K,
      ∀ v, D v = chapter16FiniteIdeleValuationValue K x v := by
  sorry

def chapter16FiniteIdeleFractionalIdeal (K : Type*) [Field K] [NumberField K]
    (x : Chapter16FiniteIdeles K) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ chapter16FiniteIdeleValuationValue K x v

def chapter16FiniteIdeleFractionalIdealHom (K : Type*) [Field K] [NumberField K] :
    Chapter16FiniteIdeles K →* FractionalIdeal (𝓞 K)⁰ K where
  toFun := chapter16FiniteIdeleFractionalIdeal K
  map_one' := by sorry
  map_mul' := by sorry

def chapter16FiniteIdeleUnitSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16FiniteIdeles K) :=
  (chapter16FiniteIdeleFractionalIdealHom K).ker

def chapter16FiniteIdeleArithmeticSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter16FiniteIdeles K) :=
  chapter16PrincipalFiniteIdeles K ⊔ chapter16FiniteIdeleUnitSubgroup K

instance chapter16FiniteIdeleArithmeticSubgroup_normal
    (K : Type*) [Field K] [NumberField K] :
    (chapter16FiniteIdeleArithmeticSubgroup K).Normal := by
  exact ⟨by
    intro n hn g
    rw [mul_assoc, mul_comm n g⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    exact hn⟩

structure Chapter16Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : Ideal (𝓞 K)
  finitePart_ne_zero : finitePart ≠ 0
  realPlaces : Finset {w : InfinitePlace K // w.IsReal}

def chapter16ModulusFractionalPart (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.mk0 K
    ⟨m.finitePart, mem_nonZeroDivisors_iff_ne_zero.mpr m.finitePart_ne_zero⟩

def chapter16ModulusExponent (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v (chapter16ModulusFractionalPart K m)

def chapter16LocalRayCongruence (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : Prop :=
  (a : K) - 1 = 0 ∨
    (FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) = 0 ∧
      chapter16ModulusExponent K m v ≤
        FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((a : K) - 1)))

def chapter16RayCongruent (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) (a : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finitePart →
    chapter16LocalRayCongruence K m v a) ∧
    ∀ w ∈ m.realPlaces,
      0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((a : K) : w.1.Completion)

def chapter16CoprimeFractionalIdealSubgroup (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) :
    Subgroup ((FractionalIdeal (𝓞 K)⁰ K)ˣ) where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K),
    v.asIdeal ∣ m.finitePart → FractionalIdeal.count K v I = 0}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

def chapter16RayPrincipalSubgroup (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) :
    Subgroup (chapter16CoprimeFractionalIdealSubgroup K m) where
  carrier := {I | ∃ a : Kˣ,
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) (by sorry) ∧
      chapter16RayCongruent K m a}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

instance chapter16RayPrincipalSubgroup_normal
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :
    (chapter16RayPrincipalSubgroup K m).Normal := by
  exact ⟨by
    intro n hn g
    rw [mul_assoc, mul_comm n g⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    exact hn⟩

abbrev Chapter16RayClassGroup (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) :=
  chapter16CoprimeFractionalIdealSubgroup K m ⧸ chapter16RayPrincipalSubgroup K m

def chapter16CoprimeFiniteIdeles (K : Type*) [Field K] [NumberField K]
    (m : Chapter16Modulus K) : Subgroup (Chapter16FiniteIdeles K) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 K),
    v.asIdeal ∣ m.finitePart →
      FractionalIdeal.count K v (chapter16FiniteIdeleFractionalIdeal K x) = 0}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

def chapter16FiniteIdeleRayPrincipalSubgroup
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :
    Subgroup (chapter16CoprimeFiniteIdeles K m) where
  carrier := {x | ∃ a : Kˣ, ∃ u : chapter16FiniteIdeleUnitSubgroup K,
    (x : Chapter16FiniteIdeles K) =
      chapter16PrincipalFiniteIdeleHom K a * (u : Chapter16FiniteIdeles K) ∧
      chapter16RayCongruent K m a}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

instance chapter16FiniteIdeleRayPrincipalSubgroup_normal
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :
    (chapter16FiniteIdeleRayPrincipalSubgroup K m).Normal := by
  exact ⟨by
    intro n hn g
    rw [mul_assoc, mul_comm n g⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    exact hn⟩

abbrev Chapter16FiniteIdeleRayClassQuotient
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :=
  chapter16CoprimeFiniteIdeles K m ⧸ chapter16FiniteIdeleRayPrincipalSubgroup K m

def chapter16FiniteIdeleRayQuotientMap
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :
    chapter16CoprimeFiniteIdeles K m →*
      Chapter16FiniteIdeleRayClassQuotient K m :=
  QuotientGroup.mk' (chapter16FiniteIdeleRayPrincipalSubgroup K m)

abbrev Chapter16GeneralLinearAdeles (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n] :=
  Matrix.GeneralLinearGroup n (Chapter16AdeleRing K)

def chapter16FiniteGLnLevel (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n]
    (v : HeightOneSpectrum (𝓞 K)) :
    Set (Matrix.GeneralLinearGroup n (v.adicCompletion K)) :=
  {g | (∀ i j, g i j ∈ Set.range (fun a : v.adicCompletionIntegers K =>
      (a : v.adicCompletion K))) ∧
    ∀ i j, g⁻¹ i j ∈ Set.range (fun a : v.adicCompletionIntegers K =>
      (a : v.adicCompletion K))}

def chapter16FiniteGLnLevelSubgroup (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n]
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (Matrix.GeneralLinearGroup n (v.adicCompletion K)) where
  carrier := chapter16FiniteGLnLevel K n v
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

abbrev Chapter16FiniteGLnRestrictedProduct (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n] :=
  Πʳ v : HeightOneSpectrum (𝓞 K),
    [Matrix.GeneralLinearGroup n (v.adicCompletion K),
      chapter16FiniteGLnLevelSubgroup K n v]

/- LOCAL_DEPENDENCY_GUESS:
No earlier LastLib file supplies the coordinatewise extension norm package.
The fields below isolate exactly the full-idele, finite-idele, ideal, and
principal maps needed by the chapter's compatibility statements.
-/

structure Chapter16ExtensionNormData
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] where
  adeleNorm : Chapter16Ideles L →* Chapter16Ideles K
  finiteNorm : Chapter16FiniteIdeles L →* Chapter16FiniteIdeles K
  idealNorm : FractionalIdeal (𝓞 L)⁰ L →* FractionalIdeal (𝓞 K)⁰ K
  principalNorm : Lˣ →* Kˣ
  principalNorm_is_fieldNorm :
    principalNorm = Units.map (Algebra.norm K (S := L))
  finiteProjection_compatibility :
    ∀ x : Chapter16Ideles L,
      chapter16FiniteIdeleProjection K (adeleNorm x) =
        finiteNorm (chapter16FiniteIdeleProjection L x)

def chapter16ExtensionNormCompatible
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter16ExtensionNormData K L) : Prop :=
  (∀ _x : Chapter16Ideles L,
    chapter16IdeleModule K (N.adeleNorm _x) = chapter16IdeleModule L _x) ∧
  (∀ a : Lˣ,
    N.adeleNorm (chapter16PrincipalIdeleHom L a) =
      chapter16PrincipalIdeleHom K (N.principalNorm a)) ∧
  (∀ a : Lˣ,
    N.finiteNorm (chapter16PrincipalFiniteIdeleHom L a) =
      chapter16PrincipalFiniteIdeleHom K (N.principalNorm a)) ∧
  (∀ x : Chapter16FiniteIdeles L,
    N.idealNorm (chapter16FiniteIdeleFractionalIdeal L x) =
      chapter16FiniteIdeleFractionalIdeal K (N.finiteNorm x)) ∧
  N.principalNorm = Units.map (Algebra.norm K (S := L)) ∧
  (∀ x : Chapter16Ideles L,
    chapter16FiniteIdeleProjection K (N.adeleNorm x) =
      N.finiteNorm (chapter16FiniteIdeleProjection L x))

def chapter16HasCompactOpenFiniteLevel (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G)

def chapter16EverywhereLocallyNorm
    {ι : Type*} {Kloc : ι → Type*} {Lloc : ι → Type*}
    [∀ i, Group (Kloc i)] [∀ i, Group (Lloc i)]
    (localNorm : ∀ i, Lloc i →* Kloc i) (x : ∀ i, Kloc i) : Prop :=
  ∀ i, x i ∈ (localNorm i).range

def chapter16GlobalNormPrinciple
    {ι K L : Type*} {Kloc : ι → Type*} {Lloc : ι → Type*}
    [Group K] [Group L] [∀ i, Group (Kloc i)] [∀ i, Group (Lloc i)]
    (globalNorm : L →* K) (globalToLocal : K → (∀ i, Kloc i))
    (localNorm : ∀ i, Lloc i →* Kloc i) : Prop :=
  ∀ x : K, (∀ i, globalToLocal x i ∈ (localNorm i).range) → x ∈ globalNorm.range

def chapter16AdditiveAnnihilator
    {A : Type*} [CommRing A] (ψ : AddChar A Circle) (S : AddSubgroup A) : Set A :=
  {x | ∀ y ∈ S, ψ (x * y) = 1}

end

end LastLib.Book04AdelesAndIdeles.Chapter16
