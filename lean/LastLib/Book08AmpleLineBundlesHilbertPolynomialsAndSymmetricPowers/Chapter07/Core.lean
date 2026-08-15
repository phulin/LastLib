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

/-! The standard grading on the polynomial ring in `r + 1` variables.  The
following name is retained for the Chapter 7 polynomial-model interface; the
scheme and its tautological bundle use the canonical projective-space package
from Chapter 2 below. -/
noncomputable def chapter07ProjectiveSpaceGrading
    (k : Type u) [Field k] (r : ℕ) :
    ℕ → Submodule k (MvPolynomial (Fin (r + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k

/-! The standard projective-space model and its structure morphism. -/
abbrev chapter07ProjectiveSpace
    (k : Type u) [Field k] (r : ℕ) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpace
    (AlgebraicGeometry.Spec (.of k)) r

abbrev chapter07ProjectiveSpaceToBase
    (k : Type u) [Field k] (r : ℕ) :
    chapter07ProjectiveSpace k r ⟶ chapter07BaseScheme k :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceProjection
    (AlgebraicGeometry.Spec (.of k)) r

/-!
Chapter 4 already supplies the canonical finite locally free rank-one
interface.  Keep the Chapter 7 name as a compatibility abbreviation rather
than introducing a second, weaker notion of line bundle.
-/
abbrev Chapter07RankOneLocallyFree {X : Scheme.{u}} (M : X.Modules) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04IsInvertible M

abbrev Chapter07LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle X

/-! The standard `𝓞(1)` on the projective-space model. -/
noncomputable def chapter07ProjectiveSpaceTautologicalLineBundle
    (k : Type u) [Field k] (r : ℕ) :
    Chapter07LineBundle (chapter07ProjectiveSpace k r) :=
  { sheaf :=
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceTwistingLine
        (AlgebraicGeometry.Spec (.of k)) r).carrier
    isInvertible :=
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04_isInvertible_of_chapter02Invertible
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceTwistingLine
          (AlgebraicGeometry.Spec (.of k)) r).invertible }

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

noncomputable def chapter07LineBundlePower
    {X : Scheme.{u}} (L : Chapter07LineBundle X) (q : ℕ) : X.Modules :=
  (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04LineBundleTensorPower
    L q).sheaf

structure Chapter07CoherentSheaf (X : Scheme.{u}) where
  sheaf : X.Modules
  coherent : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteTypeQuasiCoherent sheaf
  finitePresentation : sheaf.IsFinitePresentation

/-! A dimension certificate is tied to the actual stalkwise support of the
coherent sheaf through the preceding chapter's Krull-dimension predicate. -/
structure Chapter07SupportDimensionCertificate
    {X : Scheme.{u}} (F : Chapter07CoherentSheaf X) where
  dimension : ℕ
  dimension_has_supportDimension :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04SheafHasSupportDimension
      F.sheaf dimension

/-!
The preceding chapter's very-ample witness already contains an immersion into
a finite projective bundle and the pullback identification with its
tautological line bundle.  Specialize it to the canonical tensor power rather
than adding an unconnected `Prop` marker for tautologicality.
-/
abbrev Chapter07VeryAmplePower
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ chapter07BaseScheme k)
    (L : Chapter07LineBundle X) (q : ℕ) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04VeryAmpleWitness
    f
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04LineBundleTensorPower
      L q)

def Chapter07AmpleLineBundle
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ chapter07BaseScheme k)
    (L : Chapter07LineBundle X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Ample
    f L

structure Chapter07PolarizedScheme (k : Type u) [Field k] where
  X : Scheme.{u}
  structureMap : X ⟶ chapter07BaseScheme k
  projective : Chapter07ProjectiveOver k structureMap
  L : Chapter07LineBundle X
  ample : Chapter07AmpleLineBundle k structureMap L

noncomputable def chapter07TwistedSheaf
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (F : Chapter07CoherentSheaf C.X) (n : ℕ) : C.X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Tensor
    F.sheaf (chapter07LineBundlePower C.L n)

/-!
The canonical cohomology object supplied by Chapter 4 is an additive-group
object.  Over a field, the Hilbert function needs a compatible scalar module,
not merely an isomorphic additive group.  This comparison records a scalar
action on that canonical object and a genuine module isomorphism to the
field-valued cohomology module used by the Hilbert function.
-/
structure Chapter07FieldCohomologyComparison
    (k : Type u) [Field k]
    {X : Scheme.{u}} (F : X.Modules) (i : ℕ)
    (M : ModuleCat.{u + 1} k) where
  cohomologyModule : Module k
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Cohomology
      F i)
  linearIso :
    letI := cohomologyModule
    M ≅ ModuleCat.of k
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Cohomology
        F i)

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
  cohomology : ℕ → ℤ → ModuleCat.{u + 1} k
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
  /- The nonnegative part of the profile is identified with the earlier
  canonical cohomology of `F ⊗ L^n` together with a field-aware comparison.
  Thus the scalar-module presentation used by `finrank` is explicitly tied to
  the geometric cohomology object, rather than only to an additive-group
  isomorphism. -/
  cohomologyRepresentsTwistedSheaf :
    ∀ (i n : ℕ),
      Chapter07FieldCohomologyComparison k
        (chapter07TwistedSheaf F n) i (cohomology i (n : ℤ))

/-! The displayed finrank is the finrank of the field-aware geometric
cohomology comparison carried by the setup. -/
noncomputable def chapter07GeometricCohomologyFinrank
    {k : Type u} [Field k]
    {X : Scheme.{u}} {F : X.Modules} {i : ℕ}
    {M : ModuleCat.{u + 1} k}
    (_comparison : Chapter07FieldCohomologyComparison k F i M) : ℕ :=
  Module.finrank k M

noncomputable def chapter07HilbertFunction
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℕ) : ℕ :=
  chapter07GeometricCohomologyFinrank
    (S.cohomologyRepresentsTwistedSheaf 0 n)

@[simp] theorem chapter07_hilbertFunction_eq_geometricCohomologyFinrank
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℕ) :
    chapter07HilbertFunction S n =
      chapter07GeometricCohomologyFinrank
        (S.cohomologyRepresentsTwistedSheaf 0 n) := by
  rfl

noncomputable def chapter07EulerCharacteristicAtInteger
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C) (n : ℤ) : ℤ :=
  ∑ i ∈ Finset.range S.cohomologicalBound,
    (-1 : ℤ) ^ i * (Module.finrank k (S.cohomology i n) : ℤ)

/-!
The support-filtration proof of the degree theorem has a numerical boundary
which is not present in the pinned scheme API: the first difference order is
one larger than the support dimension, and the top difference is a positive
integer.  Recording that intermediate certificate keeps the later theorem
statements honest without assuming their desired polynomial conclusion.
-/
structure Chapter07HilbertPolynomialDimensionCertificate
    {k : Type u} [Field k]
    {C : Chapter07PolarizedScheme k}
    (S : Chapter07HilbertSetup k C)
    (D : Chapter07SupportDimensionCertificate S.F) where
  differenceOrder_eq : S.eulerCharacteristicDifferenceOrder = D.dimension + 1
  topDifference_positive :
    ∃ e : ℕ, 0 < e ∧ ∀ n : ℤ,
      chapter07IteratedForwardDifference D.dimension
        (fun m : ℤ => chapter07EulerCharacteristicAtInteger S m) n = e

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
  simp only [chapter07BinomialPolynomial, Polynomial.eval_mul,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  have hshift (x : ℕ) :
      ((n : ℤ) : ℚ) + (((x : ℤ) + 1 - (a : ℤ) : ℤ) : ℚ) =
        ((n - a : ℕ) : ℚ) + (x : ℚ) + 1 := by
    rw [Nat.cast_sub ha]
    push_cast
    ring
  have hprod :
      (∏ x ∈ Finset.range r,
        (((n : ℤ) : ℚ) + (((x : ℤ) + 1 - (a : ℤ) : ℤ) : ℚ))) =
        ((n - a + 1).ascFactorial r : ℚ) := by
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Finset.prod_range_succ, ih, Nat.ascFactorial_succ, hshift]
        push_cast
        ring
  have hindex : n - a + r = n + r - a := by omega
  rw [hprod, Nat.ascFactorial_eq_factorial_mul_choose, hindex]
  have hfac : (r.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  rw [Nat.cast_mul]
  field_simp

/-! Exactness is kept at Mathlib's sheaf-module level, while the coherent
certificates ensure that each term is in the class to which the Hilbert API
applies. -/
structure Chapter07ShortExactSequence
    {X : Scheme.{u}}
    (A B D : Chapter07CoherentSheaf X) where
  injection : A.sheaf ⟶ B.sheaf
  projection : B.sheaf ⟶ D.sheaf
  comp_zero : injection ≫ projection = 0
  injection_mono : Mono injection
  projection_epi : Epi projection
  exact : (ShortComplex.mk injection projection comp_zero).Exact

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter07
