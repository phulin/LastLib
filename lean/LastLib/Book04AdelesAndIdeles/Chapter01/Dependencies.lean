import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Algebra.Module.Basic
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section04LocalizationsOfDedekindDomains

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open scoped BigOperators nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

/-!
Shared book-facing names for Chapter 1.  The definitions are deliberately thin
interfaces over the canonical number-field, fractional-ideal, completion, and
mixed-embedding constructions.
-/

abbrev chapter01Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev chapter01RingOfIntegers (K : Type*) [Field K] [NumberField K] :=
  𝓞 K

abbrev chapter01FractionalIdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ

abbrev chapter01ClassGroup (K : Type*) [Field K] [NumberField K] :=
  ClassGroup (𝓞 K)

def chapter01PrincipalFractionalIdealHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* chapter01FractionalIdealGroup K :=
  toPrincipalIdeal (𝓞 K) K

def chapter01PrincipalFractionalIdealSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup (chapter01FractionalIdealGroup K) :=
  (chapter01PrincipalFractionalIdealHom K).range

def chapter01IdealClassGroupEquiv (K : Type*) [Field K] [NumberField K] :
    chapter01ClassGroup K ≃*
      chapter01FractionalIdealGroup K ⧸
        chapter01PrincipalFractionalIdealSubgroup K :=
  ClassGroup.equiv K

def chapter01PrincipalFractionalIdeal {K : Type*} [Field K] [NumberField K]
    (x : K) : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ x

def chapter01AbsoluteIdealNorm {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) : ℕ :=
  Ideal.absNorm I

abbrev chapter01ResidueField {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Type _ :=
  (𝓞 K) ⧸ v.asIdeal

def chapter01Order {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : ℤ :=
  FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)

def chapter01UnitOrder {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Kˣ → ℤ :=
  fun x => chapter01Order v (x : K)

def chapter01FractionalIdealOrder {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) : ℤ :=
  FractionalIdeal.count K v I

def chapter01FractionalIdealIntegralOutside {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (I : FractionalIdeal (𝓞 K)⁰ K) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ S →
    0 ≤ chapter01FractionalIdealOrder v I

def chapter01LocalFractionalIdealBall {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) : Set (v.adicCompletion K) :=
  {y | Valued.v y ≤ WithZero.exp (-chapter01FractionalIdealOrder v I)}

def chapter01IsAlgebraicInteger {K : Type*} [Field K] [NumberField K] (x : K) : Prop :=
  IsIntegral ℤ x

def chapter01LocalNeighborhood {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (m : ℤ) :
    Set (v.adicCompletion K) :=
  {y | Valued.v y ≤ WithZero.exp (-m)}

abbrev chapter01CompletionResidueField {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  IsLocalRing.ResidueField (v.adicCompletionIntegers K)

def chapter01CompletionMaximalIdeal {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)

def chapter01LocallyClose {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : v.adicCompletion K) (m : ℤ) : Prop :=
  x - y ∈ chapter01LocalNeighborhood v m

abbrev chapter01FiniteAdeleRing (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

abbrev chapter01MinkowskiSpace (K : Type*) [Field K] [NumberField K] :=
  NumberField.mixedEmbedding.mixedSpace K

abbrev chapter01MinkowskiEmbedding (K : Type*) [Field K] [NumberField K] :
    K →+* chapter01MinkowskiSpace K :=
  NumberField.mixedEmbedding K

abbrev chapter01RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev chapter01ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def chapter01ComplexAreaScale (z : ℂ) : ℝ :=
  ‖z‖ ^ 2

def chapter01Discriminant (K : Type*) [Field K] [NumberField K] : ℤ :=
  NumberField.discr K

abbrev chapter01IdealLattice (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) :=
  NumberField.mixedEmbedding.idealLattice K I

end

end LastLib.Book04AdelesAndIdeles.Chapter01
