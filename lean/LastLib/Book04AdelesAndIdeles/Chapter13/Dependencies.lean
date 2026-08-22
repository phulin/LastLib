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
import LastLib.Book04AdelesAndIdeles.Chapter04.Section06AdelicTrace
import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

/-!
# Chapter 13: shared interfaces

This file contains the small amount of shared notation used by the six source-order sections.
The canonical adelic and idele carriers are reused from Chapter 9.  The remaining interfaces here
are limited to chapter-13 character and additive-trace data that are not supplied by those earlier
chapters.
-/

open scoped BigOperators NumberField NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

abbrev Chapter13Adele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11AdeleRing K

abbrev Chapter13FiniteAdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11FiniteAdeleRing K

abbrev Chapter13InfiniteAdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K

abbrev Chapter13FiniteIdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11FiniteIdeleGroup K

abbrev Chapter13InfiniteIdele (K : Type*) [Field K] [NumberField K] :=
  (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ

abbrev Chapter13Idele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11IdeleGroup K

abbrev Chapter13PositiveReal : Type :=
  LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09PositiveReal

abbrev Chapter13LocalUnitSubgroup (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (v.adicCompletionIntegers K).unitGroup

/- The following local bridge uses the standard algebra maps, while the principal ideles themselves
are the canonical Chapter 9 construction. -/

def chapter13PrincipalFiniteIdeleValue (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ :=
  fun v => Units.map (algebraMap K (v.adicCompletion K)) a

abbrev chapter13PrincipalFiniteIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter13FiniteIdele K :=
  LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FinitePrincipalIdele K

abbrev chapter13PrincipalIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter13Idele K :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11PrincipalIdeleHom (K := K)

def chapter13FiniteIdeleCoordinate
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter13FiniteIdele K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ :=
  (RestrictedProduct.unitsEquiv
    (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => w.adicCompletion K) x) v

theorem chapter13PrincipalIdele_infinite_coordinate
    (K : Type*) [Field K] [NumberField K] (a : Kˣ)
    (v : NumberField.InfinitePlace K) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13PrincipalIdele K a)).1)) v =
      Units.map (algebraMap K v.Completion) a := by
  sorry

theorem chapter13PrincipalIdele_finite_coordinate
    (K : Type*) [Field K] [NumberField K]
    (a : Kˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13PrincipalIdele K a)).2) v =
      chapter13PrincipalFiniteIdeleValue K a v := by
  sorry

theorem chapter13FiniteIdeleCoordinate_principal
    (K : Type*) [Field K] [NumberField K] (a : Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteIdeleCoordinate K (chapter13PrincipalFiniteIdele K a) v =
      chapter13PrincipalFiniteIdeleValue K a v := by
  sorry

theorem chapter13FiniteIdeleCoordinate_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Continuous (fun x : Chapter13FiniteIdele K =>
      chapter13FiniteIdeleCoordinate K x v) := by
  sorry

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

theorem chapter13InfiniteLocalIdele_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13InfiniteLocalIdele K v x)).1)) v = x := by
  sorry

theorem chapter13InfiniteLocalIdele_coordinate_off
    (K : Type*) [Field K] [NumberField K]
    (v w : NumberField.InfinitePlace K) (x : (v.Completion)ˣ) (hvw : w ≠ v) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13InfiniteLocalIdele K v x)).1)) w = 1 := by
  sorry

theorem chapter13InfiniteLocalIdele_finite_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x : (v.Completion)ˣ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13InfiniteLocalIdele K v x)).2) w = 1 := by
  sorry

theorem chapter13InfiniteLocalIdele_one
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    chapter13InfiniteLocalIdele K v 1 = 1 := by
  sorry

theorem chapter13InfiniteLocalIdele_mul
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (x y : (v.Completion)ˣ) :
    chapter13InfiniteLocalIdele K v (x * y) =
      chapter13InfiniteLocalIdele K v x * chapter13InfiniteLocalIdele K v y := by
  sorry

theorem chapter13InfiniteLocalIdele_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    Continuous (chapter13InfiniteLocalIdele K v) := by
  sorry

def chapter13InfiniteLocalIdeleHom
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) :
    (v.Completion)ˣ →ₜ* Chapter13Idele K :=
  { toMonoidHom :=
      { toFun := chapter13InfiniteLocalIdele K v
        map_one' := chapter13InfiniteLocalIdele_one K v
        map_mul' := chapter13InfiniteLocalIdele_mul K v }
    continuous_toFun := chapter13InfiniteLocalIdele_continuous K v }

theorem chapter13FiniteLocalIdele_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).2) v = x := by
  sorry

theorem chapter13FiniteLocalIdele_coordinate_off
    (K : Type*) [Field K] [NumberField K]
    (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (hvw : w ≠ v) :
    chapter13FiniteIdeleCoordinate K
        ((MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).2) w = 1 := by
  sorry

theorem chapter13FiniteLocalIdele_infinite_coordinate
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (w : NumberField.InfinitePlace K) :
    (MulEquiv.piUnits
      ((MulEquiv.prodUnits (chapter13FiniteLocalIdele K v x)).1)) w = 1 := by
  sorry

theorem chapter13FiniteLocalIdele_one
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chapter13FiniteLocalIdele K v 1 = 1 := by
  sorry

theorem chapter13FiniteLocalIdele_mul
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x y : (v.adicCompletion K)ˣ) :
    chapter13FiniteLocalIdele K v (x * y) =
      chapter13FiniteLocalIdele K v x * chapter13FiniteLocalIdele K v y := by
  sorry

theorem chapter13FiniteLocalIdele_continuous
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Continuous (chapter13FiniteLocalIdele K v) := by
  sorry

def chapter13FiniteLocalIdeleHom
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* Chapter13Idele K :=
  { toMonoidHom :=
      { toFun := chapter13FiniteLocalIdele K v
        map_one' := chapter13FiniteLocalIdele_one K v
        map_mul' := chapter13FiniteLocalIdele_mul K v }
    continuous_toFun := chapter13FiniteLocalIdele_continuous K v }

abbrev chapter13PrincipalIdeleSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter13Idele K) :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11PrincipalIdeleSubgroup (K := K)

abbrev Chapter13IdeleClass (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11IdeleClassGroup K

instance chapter13IdeleClassCommGroup
    (K : Type*) [Field K] [NumberField K] :
    CommGroup (Chapter13IdeleClass K) := by
  change CommGroup
    (LastLib.Book04AdelesAndIdeles.Chapter11.Chapter11IdeleClassGroup K)
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

theorem chapter13_mem_additiveAnnihilator_iff
    {A : Type*} [NonUnitalNonAssocRing A]
    (ψ : AddChar A Circle) (H : AddSubgroup A) (y : A) :
    y ∈ chapter13AdditiveAnnihilator ψ H ↔
      ∀ x : H, ψ ((x : A) * y) = 1 :=
  Iff.rfl

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

/- The ray levels are the canonical Chapter 11 moduli and quotients.  Keeping these aliases here
lets the character statements use chapter-13 names without replacing the established ray-class
API by a generic system of unrelated open subgroups. -/

abbrev Chapter13RayModulus (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter11.RayModulus K

abbrev Chapter13RayClassGroup {K : Type*} [Field K] [NumberField K]
    (m : Chapter13RayModulus K) :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11RayClassGroup m

abbrev Chapter13RayClassCharacter {K : Type*} [Field K] [NumberField K]
    (m : Chapter13RayModulus K) :=
  Chapter13RayClassGroup m →* ℂˣ

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
      ∀ᶠ p in Filter.cofinite,
        ∃ z : Chapter13PadicInteger p, (z : Chapter13Padic p) = finiteCoordinate p x
  finiteCoordinate_continuous :
    ∀ p, Continuous (finiteCoordinate p)
  finiteCoordinate_additive :
    ∀ p x y, finiteCoordinate p (x + y) =
      finiteCoordinate p x + finiteCoordinate p y
  infinityCoordinate : Chapter13Adele ℚ → ℝ
  infinityCoordinate_continuous : Continuous infinityCoordinate
  infinityCoordinate_additive :
    ∀ x y, infinityCoordinate (x + y) = infinityCoordinate x + infinityCoordinate y
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
  localTraceData :
    LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04AdelicTraceData ℚ K
  trace : Chapter13Adele K →+ Chapter13Adele ℚ
  trace_continuous : Continuous trace
  trace_eq_localTraceData :
    trace =
      LastLib.Book04AdelesAndIdeles.Chapter04.chapter04AdelicTrace localTraceData
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
  /- The pairing map is the local character parametrization.  Nondegeneracy only gives
  injectivity; surjectivity and openness are the genuinely additional local-duality inputs. -/
  pairingMap : F →ₜ+ Chapter13AdditiveDual F
  pairingMap_apply : ∀ y x, pairingMap y x = pairing x y
  pairingMap_surjective : Function.Surjective pairingMap
  pairingMap_isOpenMap : IsOpenMap pairingMap

end
end LastLib.Book04AdelesAndIdeles.Chapter13
