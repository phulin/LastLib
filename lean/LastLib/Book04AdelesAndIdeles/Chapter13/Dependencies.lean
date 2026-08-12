import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# Chapter 13: shared interfaces

This file contains the small amount of shared notation used by the six source-order sections.
The canonical adelic rings come from `NumberField.AdeleRing`.  Mathlib does not yet expose the
idele class group, ray-class inverse system, or the global standard additive character in the
book-facing form, so those interfaces are kept here and are deliberately independent of the
chapter section files.
-/

open scoped BigOperators NumberField NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

abbrev Chapter13Adele (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (𝓞 K) K

abbrev Chapter13FiniteAdele (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

abbrev Chapter13InfiniteAdele (K : Type*) [Field K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K

abbrev Chapter13FiniteIdele (K : Type*) [Field K] [NumberField K] :=
  (Chapter13FiniteAdele K)ˣ

abbrev Chapter13InfiniteIdele (K : Type*) [Field K] [NumberField K] :=
  (Chapter13InfiniteAdele K)ˣ

abbrev Chapter13Idele (K : Type*) [Field K] [NumberField K] :=
  (Chapter13Adele K)ˣ

abbrev Chapter13LocalUnitSubgroup (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (v.adicCompletionIntegers K).unitGroup

/- DEPENDENCY_GUESS: the earlier Book 04 chapters are expected to provide the canonical idele
class-group construction and principal-idele map.  The full-adele unit group and the local
single-place bridges below keep this chapter aligned with that API until the class-group layer is
merged. -/

/- The following principal ideles are the multiplicative analogue of Mathlib's additive
`NumberField.AdeleRing.principalSubgroup`.  Their local components use the standard algebra maps. -/

def chapter13PrincipalFiniteIdeleValue (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ :=
  fun v => Units.map (algebraMap K (v.adicCompletion K)) a

def chapter13PrincipalFiniteIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter13FiniteIdele K :=
  Units.map (IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K)

def chapter13PrincipalIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter13Idele K :=
  Units.map (algebraMap K (Chapter13Adele K))

def chapter13FiniteIdeleCoordinate
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter13FiniteIdele K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ :=
  (RestrictedProduct.unitsEquiv
    (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => w.adicCompletion K) x) v

/- The following local embeddings are the canonical single-place maps after transporting local
units through the unit equivalences of the infinite and finite adele factors. -/

def chapter13InfiniteLocalIdele
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) : Chapter13Idele K := by
  sorry

def chapter13FiniteLocalIdele
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : Chapter13Idele K := by
  sorry

def chapter13PrincipalIdeleSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter13Idele K) :=
  (chapter13PrincipalIdele K).range

abbrev Chapter13IdeleClass (K : Type*) [Field K] [NumberField K] :=
  Chapter13Idele K ⧸ chapter13PrincipalIdeleSubgroup K

instance chapter13IdeleClassCommGroup
    (K : Type*) [Field K] [NumberField K] :
    CommGroup (Chapter13IdeleClass K) := by
  change CommGroup (Chapter13Idele K ⧸ chapter13PrincipalIdeleSubgroup K)
  infer_instance

abbrev Chapter13ClassCharacter (K : Type*) [Field K] [NumberField K] :=
  Chapter13IdeleClass K →ₜ* ℂˣ

/-! A restricted product of local multiplicative characters is called unramified when its local
character is trivial on the distinguished local unit group. -/

abbrev Chapter13ContinuousComplexCharacter (G : Type*) [Monoid G] [TopologicalSpace G] :=
  G →ₜ* ℂˣ

def chapter13TrivialOnSubgroup {G : Type*} [Group G] (H : Subgroup G)
    (χ : G →* ℂˣ) : Prop :=
  ∀ x : H, χ x = 1

def chapter13AdditiveAnnihilator {A : Type*} [NonUnitalNonAssocRing A]
    (ψ : AddChar A Circle) (H : AddSubgroup A) : AddSubgroup A := by
  refine
    { carrier := {y | ∀ x : H, ψ ((x : A) * y) = 1}
      zero_mem' := by sorry
      add_mem' := by sorry
      neg_mem' := by sorry }

abbrev Chapter13AdditiveDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] :=
  Additive (PontryaginDual (Multiplicative A))

abbrev Chapter13QModZ := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

abbrev Chapter13Padic (p : {p : ℕ // Nat.Prime p}) :=
  @Padic p.1 ⟨p.2⟩

abbrev Chapter13PadicInteger (p : {p : ℕ // Nat.Prime p}) :=
  @PadicInt p.1 ⟨p.2⟩

def chapter13RationalModIntegerCharacter : AddChar Chapter13QModZ Circle :=
  (AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
      (Real.fourierChar.compAddMonoidHom (Rat.castHom ℝ).toAddMonoidHom).toAddMonoidHom
      (by sorry)))⁻¹

/-!
`Chapter13RayClassSystem` is a book-facing inverse system of open finite-index subgroups of the
idele class group.  The `cofinal` field is the exact interface needed for the conductor and
directed-union statements; a later pass can identify its levels with the canonical ray class
groups once the earlier Chapters 10--12 expose their idelic class-group API.
-/

/- DEPENDENCY_GUESS: identify `Chapter13RayClassSystem` with the ray-class levels and their
canonical quotient maps from the earlier conductor chapters. -/

structure Chapter13RayClassSystem (K : Type*) [Field K] [NumberField K]
    (M : Type*) [Preorder M] where
  level : M → Subgroup (Chapter13IdeleClass K)
  level_open : ∀ m, IsOpen (level m : Set (Chapter13IdeleClass K))
  level_finite : ∀ m, Finite (Chapter13IdeleClass K ⧸ level m)
  directed : ∀ m n, ∃ l, level l ≤ level m ∧ level l ≤ level n
  cofinal : ∀ H : Subgroup (Chapter13IdeleClass K),
    IsOpen (H : Set (Chapter13IdeleClass K)) → ∃ m, level m ≤ H
  realPlaces :
    M → Finset {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal v}

abbrev Chapter13RayClassGroup {K : Type*} [Field K] [NumberField K]
    {M : Type*} [Preorder M] (S : Chapter13RayClassSystem K M) (m : M) :=
  Chapter13IdeleClass K ⧸ S.level m

abbrev Chapter13RayClassCharacter {K : Type*} [Field K] [NumberField K]
    {M : Type*} [Preorder M] (S : Chapter13RayClassSystem K M) (m : M) :=
  Chapter13RayClassGroup S m →* ℂˣ

/-!
The following two structures are intentionally hypotheses rather than disguised conclusions.  They
record the missing earlier interfaces used by the additive half of the chapter: a global standard
character and its local trace pairing. -/

/- DEPENDENCY_GUESS: the standard p-adic principal-part maps, the adelic trace, and the associated
continuity/finite-support proofs are expected from the earlier local and trace chapters. -/

structure Chapter13RationalPrincipalPartData (p : {p : ℕ // Nat.Prime p}) where
  principalPart : Chapter13Padic p →+ Chapter13QModZ
  principalPart_eq_zero_on_integers :
    ∀ x : Chapter13PadicInteger p, principalPart x = 0
  principalPart_nontrivial : ∃ x, principalPart x ≠ 0
  principalCharacter : AddChar (Chapter13Padic p) Circle
  principalCharacter_continuous : Continuous principalCharacter
  principalCharacter_trivial_on_integers :
    ∀ x : Chapter13PadicInteger p, principalCharacter x = 1
  principalCharacter_nontrivial_on_inverse_p :
    principalCharacter ((p.1 : Chapter13Padic p)⁻¹) ≠ 1
  principalCharacter_formula :
    ∀ x, principalCharacter x = chapter13RationalModIntegerCharacter (principalPart x)

structure Chapter13RationalStandardCharacterData where
  psiInfinity : AddChar ℝ Circle
  psiInfinity_eq_fourier : psiInfinity = Real.fourierChar
  finiteCoordinate : ∀ p : {p : ℕ // Nat.Prime p}, Chapter13Adele ℚ → Chapter13Padic p
  finiteCoordinate_integral :
    ∀ x : Chapter13Adele ℚ,
      ∀ᶠ p in Filter.cofinite, ‖finiteCoordinate p x‖ ≤ 1
  infinityCoordinate : Chapter13Adele ℚ → ℝ
  infinityCoordinate_principal :
    ∀ a : ℚ,
      infinityCoordinate (algebraMap ℚ (Chapter13Adele ℚ) a) = (a : ℝ)
  finiteCoordinate_principal :
    ∀ (p : {p : ℕ // Nat.Prime p}) (a : ℚ),
      finiteCoordinate p (algebraMap ℚ (Chapter13Adele ℚ) a) =
        (a : Chapter13Padic p)
  padic : ∀ p : {p : ℕ // Nat.Prime p}, Chapter13RationalPrincipalPartData p
  principalPart_balance :
    ∀ a : ℚ,
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) a =
        ∑ᶠ p,
          (padic p).principalPart
            (finiteCoordinate p (algebraMap ℚ (Chapter13Adele ℚ) a))

structure Chapter13AdelicTraceData (K : Type*) [Field K] [NumberField K] where
  trace : Chapter13Adele K →+ Chapter13Adele ℚ
  trace_continuous : Continuous trace
  trace_principal :
    ∀ a : K, trace (algebraMap K (Chapter13Adele K) a) =
      algebraMap ℚ (Chapter13Adele ℚ) (Algebra.trace ℚ K a)
  rationalCharacter : Chapter13RationalStandardCharacterData

structure Chapter13LocalSelfDualityData (F : Type*) [Field F] [TopologicalSpace F]
    [AddCommGroup F] where
  pairing : F → F → Circle
  pairing_add_left : ∀ x y z, pairing (x + y) z = pairing x z * pairing y z
  pairing_add_right : ∀ x y z, pairing x (y + z) = pairing x y * pairing x z
  pairing_continuous : Continuous (Function.uncurry pairing)
  pairing_left_nondegenerate : ∀ x, (∀ y, pairing x y = 1) → x = 0
  pairing_right_nondegenerate : ∀ y, (∀ x, pairing x y = 1) → y = 0

end
end LastLib.Book04AdelesAndIdeles.Chapter13
