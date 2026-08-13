import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial
open scoped BigOperators

universe u v w

/-!
## Shared interfaces for Chapter 7

Mathlib has the scheme, sheaf-of-modules, finite-presentation, locally-free,
short-exact, and polynomial primitives used below, but it does not yet expose
the book's full projective/ample/cohomology package or a Hilbert-polynomial API.
The small records in this file keep the remaining choices explicit while
reusing the preceding tensor-power carrier where it is already available.
-/

abbrev chapter07BaseScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of k)

/-! The standard grading on the polynomial ring in `r + 1` variables. -/
noncomputable def chapter07ProjectiveSpaceGrading
    (k : Type u) [Field k] (r : ℕ) :
    ℕ → Submodule k (MvPolynomial (Fin (r + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k

/-!
`AlgebraicGeometry.Proj` is the pinned Mathlib construction of projective
spectrum.  We expose the standard polynomial-ring model so later interfaces
can name a closed subscheme of `ℙ^r` without introducing a second projective
space type.
-/
noncomputable def chapter07ProjectiveSpace
    (k : Type u) [Field k] (r : ℕ) : Scheme.{u} :=
  letI : GradedAlgebra (chapter07ProjectiveSpaceGrading k r) :=
    MvPolynomial.gradedAlgebra
  AlgebraicGeometry.«Proj» (chapter07ProjectiveSpaceGrading k r)

/-! The standard structure morphism of the polynomial projective space over
`Spec k`.  The degree-zero part of the grading is used explicitly rather than
being identified with `k` by definitional equality. -/
noncomputable def chapter07ProjectiveSpaceToBase
    (k : Type u) [Field k] (r : ℕ) :
    chapter07ProjectiveSpace k r ⟶ chapter07BaseScheme k :=
  letI : GradedAlgebra (chapter07ProjectiveSpaceGrading k r) :=
    MvPolynomial.gradedAlgebra
  AlgebraicGeometry.Proj.toSpecZero (chapter07ProjectiveSpaceGrading k r) ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom'
            (chapter07ProjectiveSpaceGrading k r)).comp
          (algebraMap k (MvPolynomial (Fin (r + 1)) k))))

/- LOCAL_DEPENDENCY_GUESS: the projectivity predicate should be replaced by
the relative projective-morphism API developed in the preceding Book 8
chapters.  The certificate below records the actual closed immersion into a
standard projective space over the displayed base. -/
structure Chapter07ProjectivePresentation
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ chapter07BaseScheme k) where
  embeddingDimension : ℕ
  embedding : X ⟶ chapter07ProjectiveSpace k embeddingDimension
  closedImmersion : IsClosedImmersion embedding
  compatibleWithBase :
    embedding ≫ chapter07ProjectiveSpaceToBase k embeddingDimension = f

def Chapter07ProjectiveOver
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ chapter07BaseScheme k) : Prop :=
  Nonempty (Chapter07ProjectivePresentation k f)

/-!
Mathlib's locally-free predicate is used for the line-bundle part.  The
rank-one condition is expressed using one-element locally free generators;
the current sheaf API does not package invertible sheaves under that name.
-/
def Chapter07RankOneLocallyFree {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
    ∀ i : q.I, Nonempty ((q.generators i).I ≃ Unit)

structure Chapter07LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  locallyFree : sheaf.IsLocallyFree
  rank_one : Chapter07RankOneLocallyFree sheaf

noncomputable def chapter07LineBundlePower
    {X : Scheme.{u}} (L : Chapter07LineBundle X) (q : ℕ) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04TensorPower
    L.sheaf q

structure Chapter07CoherentSheaf (X : Scheme.{u}) where
  sheaf : X.Modules
  finitePresentation : sheaf.IsFinitePresentation

/- LOCAL_DEPENDENCY_GUESS: the preceding coherent-sheaf chapters should
replace this certificate by their canonical support and Krull-dimension API. -/
structure Chapter07SupportDimensionCertificate
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) where
  dimension : ℕ
  isSupportDimension : Prop

/- LOCAL_DEPENDENCY_GUESS: preceding chapters should replace the remaining
tautological-bundle marker in `Chapter07VeryAmplePower` by the canonical
`𝒪(1)` on relative Proj and its identification with a tensor power. -/
structure Chapter07VeryAmplePower
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ chapter07BaseScheme k)
    (L : Chapter07LineBundle X) (q : ℕ) where
  embeddingDimension : ℕ
  embedding : X ⟶ chapter07ProjectiveSpace k embeddingDimension
  closedImmersion : IsClosedImmersion embedding
  compatibleWithBase :
    embedding ≫ chapter07ProjectiveSpaceToBase k embeddingDimension = f
  targetLineBundle : Chapter07LineBundle (chapter07ProjectiveSpace k embeddingDimension)
  identifiesPullback :
    chapter07LineBundlePower L q ≅
      (Scheme.Modules.pullback embedding).obj targetLineBundle.sheaf
  targetLineBundleIsTautological : Prop

def Chapter07AmpleLineBundle
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ chapter07BaseScheme k)
    (L : Chapter07LineBundle X) : Prop :=
  ∃ q : ℕ, 0 < q ∧ Nonempty (Chapter07VeryAmplePower k f L q)

structure Chapter07PolarizedScheme (k : Type u) [Field k] where
  X : Scheme.{u}
  structureMap : X ⟶ chapter07BaseScheme k
  projective : Chapter07ProjectiveOver k structureMap
  L : Chapter07LineBundle X
  ample : Chapter07AmpleLineBundle k structureMap L

def chapter07ForwardDifference (f : ℤ → ℤ) : ℤ → ℤ :=
  fun n => f (n + 1) - f n

def chapter07IteratedForwardDifference : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | d + 1, f =>
      chapter07ForwardDifference (chapter07IteratedForwardDifference d f)

/-!
The cohomology profile records the finite-dimensional `k`-vector spaces
`H^i(X, F ⊗ L^n)`.  The integer bound is the finite-support input needed to
write Euler characteristics as ordinary finite sums; `vanishes_above` keeps
the corresponding geometric assertion available to later proofs.  The
finite-difference field is the numerical input supplied by the support
filtration in the Euler-characteristic polynomial argument.
-/
structure Chapter07HilbertSetup
    (k : Type u) [Field k]
    (C : Chapter07PolarizedScheme k) where
  F : Chapter07CoherentSheaf C.X
  cohomology : ℕ → ℤ → ModuleCat k
  cohomologicalBound : ℕ
  finiteDimensional : ∀ (i : ℕ) (n : ℤ), Module.Finite k (cohomology i n)
  vanishes_above :
    ∀ (i : ℕ) (n : ℤ), cohomologicalBound ≤ i → IsZero (cohomology i n)
  /- Serre vanishing is the input that turns the finite alternating sum into
  the degree-zero Hilbert function in high degree. -/
  higherCohomologyVanishesEventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : ℕ, 0 < i →
      IsZero (cohomology i (n : ℤ))
  eulerCharacteristicDifferenceOrder : ℕ
  eulerCharacteristicForwardDifferenceVanishes :
    ∀ n : ℤ,
      chapter07IteratedForwardDifference
          eulerCharacteristicDifferenceOrder
          (fun m : ℤ =>
            ∑ i ∈ Finset.range cohomologicalBound,
              (-1 : ℤ) ^ i * (Module.finrank k (cohomology i m) : ℤ)) n = 0
  cohomology_vanishes_when_sheaf_is_zero :
    IsZero F.sheaf → ∀ (i : ℕ) (n : ℤ), IsZero (cohomology i n)
  /- LOCAL_DEPENDENCY_GUESS: replace this marker by the canonical
  identification of the profile with H^i(X, F ⊗ L^n). -/
  cohomologyRepresentsTwistedSheaf : Prop

noncomputable def chapter07HilbertFunction
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℕ) : ℕ :=
  Module.finrank k (S.cohomology 0 (n : ℤ))

noncomputable def chapter07EulerCharacteristicAtInteger
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℤ) : ℤ :=
  ∑ i ∈ Finset.range S.cohomologicalBound,
    (-1 : ℤ) ^ i * (Module.finrank k (S.cohomology i n) : ℤ)

noncomputable def chapter07EulerCharacteristic
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℕ) : ℤ :=
  chapter07EulerCharacteristicAtInteger S (n : ℤ)

@[simp] theorem chapter07_eulerCharacteristicAtInteger_nat
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℕ) :
    chapter07EulerCharacteristicAtInteger S (n : ℤ) =
      chapter07EulerCharacteristic S n :=
  rfl

/-! A polynomial over `ℚ` is integer-valued when it takes integral values at
all integer arguments, including negative ones. -/
def Chapter07IntegerValuedOnIntegers (P : Polynomial ℚ) : Prop :=
  ∀ n : ℤ, ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ)

def Chapter07PolynomialMatchesEventually
    (P : Polynomial ℚ) (f : ℕ → ℤ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P.eval (n : ℚ) = (f n : ℚ)

/-! The binomial basis used by graded resolutions.  The product is the
polynomial identity
`binom(t + r - a, r) = ∏_{i=1}^r (t + i - a) / r!`.
-/
def chapter07BinomialPolynomial (r a : ℕ) : Polynomial ℚ :=
  Polynomial.C ((Nat.factorial r : ℚ)⁻¹) *
    ∏ i ∈ Finset.range r,
      (Polynomial.X +
        Polynomial.C ((((i : ℤ) + 1 - (a : ℤ) : ℤ) : ℚ)))

theorem chapter07_binomialPolynomial_eval
    (r a n : ℕ) (ha : a ≤ n) :
    (chapter07BinomialPolynomial r a).eval (n : ℚ) =
      (Nat.choose (n + r - a) r : ℚ) := by
  sorry

/-! Exactness is kept at Mathlib's sheaf-module level, while the coherent
certificates ensure that each term is in the class to which the Hilbert API
applies. -/
structure Chapter07ShortExactSequence
    {X : Scheme.{u}}
    (A B D : Chapter07CoherentSheaf X) where
  injection : A.sheaf ⟶ B.sheaf
  projection : B.sheaf ⟶ D.sheaf
  comp_zero : injection ≫ projection = 0
  exact : (ShortComplex.mk injection projection comp_zero).Exact

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
