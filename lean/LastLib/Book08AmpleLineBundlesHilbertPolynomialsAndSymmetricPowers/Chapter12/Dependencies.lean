import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.HilbertPoly

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

/-!
Shared interfaces for Chapter 12.

The pinned Mathlib checkout supplies schemes, ideal sheaves, pullbacks, and the
usual finiteness properties, but it does not yet supply the relative Hilbert
scheme, relative symmetric powers, or the book's relative-projectivity and
very-ampleness predicates. The small interfaces below keep those seams
explicit. They are dependency interfaces, not replacement proofs of the
geometric theorems stated later in the chapter.
-/

abbrev Chapter12NumericalPolynomial := Polynomial ℚ

/- LOCAL_DEPENDENCY_GUESS: the preceding projectivity, quasi-projectivity,
  invertibility, and relative-dimension chapters should replace these
  book-facing predicates by their canonical definitions. -/
def chapter12IsProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop := by
  sorry

def chapter12IsQuasiProjectiveMorphism {X S : Scheme} (f : X ⟶ S) : Prop := by
  sorry

def chapter12IsInvertibleSheaf {X : Scheme} (L : X.Modules) : Prop := by
  sorry

def chapter12IsRelativelyVeryAmple {X S : Scheme} (f : X ⟶ S)
    (L : X.Modules) : Prop := by
  sorry

def chapter12IsProjectiveSpaceOver (X S : Scheme) (r : ℕ) : Prop := by
  sorry

def chapter12HasRelativeDimension {X S : Scheme} (f : X ⟶ S) (r : ℕ) : Prop := by
  sorry

/-- A book-facing relatively very ample invertible sheaf. -/
structure Chapter12RelativeVeryAmple {X S : Scheme} (f : X ⟶ S) where
  /-- The underlying sheaf of modules. -/
  lineBundle : X.Modules
  /-- The invertibility interface supplied by the line-bundle chapters. -/
  lineBundle_invertible : chapter12IsInvertibleSheaf lineBundle
  /-- The relative very-ampleness interface supplied by the projective chapters. -/
  relativelyVeryAmple : chapter12IsRelativelyVeryAmple f lineBundle

/-- The standing projective, finitely presented, polarized family of Section 12.1. -/
structure Chapter12ProjectiveFamilySetup where
  base : Scheme
  total : Scheme
  structureMap : total ⟶ base
  base_locally_noetherian : IsLocallyNoetherian base
  structureMap_finite_presentation : LocallyOfFinitePresentation structureMap
  /-- This is the missing relative-projective predicate. -/
  structureMap_projective : chapter12IsProjectiveMorphism structureMap
  polarization : Chapter12RelativeVeryAmple structureMap

attribute [instance] Chapter12ProjectiveFamilySetup.base_locally_noetherian
attribute [instance] Chapter12ProjectiveFamilySetup.structureMap_finite_presentation

/-- A projective-space embedding used by the Grassmannian construction. -/
structure Chapter12ProjectiveEmbedding (D : Chapter12ProjectiveFamilySetup) where
  r : ℕ
  ambient : Scheme
  ambientMap : ambient ⟶ D.base
  embedding : D.total ⟶ ambient
  over : embedding ≫ ambientMap = D.structureMap
  closed : IsClosedImmersion embedding
  /-- The identification of `ambient` with `ℙ^r_D.base`. -/
  ambient_is_projective_space :
    chapter12IsProjectiveSpaceOver ambient D.base r

/-- An object of the category of schemes over a fixed base. -/
abbrev Chapter12SchemeOver (S : Scheme) := Over S

/-- The base change `X_T` used throughout the functor definitions. -/
def chapter12BaseChange (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) : Scheme :=
  pullback D.structureMap T.hom

/-- The projection `X_T ⟶ X`. -/
def chapter12BaseChangeToTotal (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) : chapter12BaseChange D T ⟶ D.total :=
  pullback.fst D.structureMap T.hom

/-- The projection `X_T ⟶ T`. -/
def chapter12BaseChangeToTest (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) : chapter12BaseChange D T ⟶ T.left :=
  pullback.snd D.structureMap T.hom

@[simp]
theorem chapter12BaseChange_condition (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) :
    chapter12BaseChangeToTotal D T ≫ D.structureMap =
      chapter12BaseChangeToTest D T ≫ T.hom := by
  exact pullback.condition

/-- A geometric point, represented by a point with values in a field. -/
structure Chapter12GeometricPoint (T : Scheme) where
  K : Type*
  [field : Field K]
  point : Spec (.of K) ⟶ T

attribute [instance] Chapter12GeometricPoint.field

/-- The scheme-theoretic projection of a closed family to its test scheme. -/
def chapter12FamilyProjection (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base)
    (I : (chapter12BaseChange D T).IdealSheafData) : I.subscheme ⟶ T.left :=
  I.subschemeι ≫ chapter12BaseChangeToTest D T

/-- A closed subscheme of `X_T`, represented by its ideal sheaf. -/
structure Chapter12ClosedFamily (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) where
  ideal : (chapter12BaseChange D T).IdealSheafData
  flat : Flat (chapter12FamilyProjection D T ideal)
  finitePresentation : LocallyOfFinitePresentation (chapter12FamilyProjection D T ideal)

/- LOCAL_DEPENDENCY_GUESS: the preceding cohomology/Hilbert-polynomial
  chapters should provide the canonical fiber Hilbert function. The function
  below records only the numerical interface needed by this chapter. -/

/-- The fiberwise length interface used to state finite locally free rank. -/
structure Chapter12FiberLengthTheory where
  fiberLength : {X T : Scheme} → (f : X ⟶ T) →
    Chapter12GeometricPoint T → ℕ

/-- The numerical Hilbert function attached to a closed family and a geometric fiber. -/
structure Chapter12HilbertPolynomialTheory (D : Chapter12ProjectiveFamilySetup) where
  fiberHilbertFunction : {T : Chapter12SchemeOver D.base} →
    Chapter12ClosedFamily D T → Chapter12GeometricPoint T.left → ℕ → ℕ

/-- Eventual agreement of a fiber Hilbert function with a polynomial. -/
def chapter12HasFiberHilbertPolynomial
    {D : Chapter12ProjectiveFamilySetup}
    (H : Chapter12HilbertPolynomialTheory D)
    {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
    (t : Chapter12GeometricPoint T.left) (P : Chapter12NumericalPolynomial) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    P.eval (n : ℚ) = (H.fiberHilbertFunction Z t n : ℚ)

/-- The inclusion of the closed family in the base change. -/
def chapter12FamilyInclusion (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    Z.ideal.subscheme ⟶ chapter12BaseChange D T :=
  Z.ideal.subschemeι

/-- The underlying scheme of a closed family. -/
abbrev chapter12FamilyCarrier (D : Chapter12ProjectiveFamilySetup)
    (T : Chapter12SchemeOver D.base) (Z : Chapter12ClosedFamily D T) : Scheme :=
  Z.ideal.subscheme

theorem chapter12FamilyInclusion_isClosedImmersion
    (D : Chapter12ProjectiveFamilySetup) (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    IsClosedImmersion (chapter12FamilyInclusion D T Z) := by
  change IsClosedImmersion Z.ideal.subschemeι
  infer_instance

theorem chapter12Family_isFlat
    (D : Chapter12ProjectiveFamilySetup) (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    Flat (chapter12FamilyProjection D T Z.ideal) := by
  exact Z.flat

theorem chapter12Family_isFinitelyPresented
    (D : Chapter12ProjectiveFamilySetup) (T : Chapter12SchemeOver D.base)
    (Z : Chapter12ClosedFamily D T) :
    LocallyOfFinitePresentation (chapter12FamilyProjection D T Z.ideal) := by
  exact Z.finitePresentation

/-- A family satisfying the fixed fiber-polynomial condition. -/
structure Chapter12HilbertFamily (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (T : Chapter12SchemeOver D.base) (P : Chapter12NumericalPolynomial) where
  closed : Chapter12ClosedFamily D T
  fiber_polynomial : ∀ t : Chapter12GeometricPoint T.left,
    chapter12HasFiberHilbertPolynomial H closed t P

/- The inverse-image construction is canonical, but its preservation of flatness,
  finite presentation, and the numerical polynomial is a theorem rather than a
  reducible term. We expose that theorem as the dependency seam and define the
  pullback operation by choice. -/

theorem chapter12_pullback_family_exists
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (Z : Chapter12HilbertFamily D H U P) :
    Nonempty (Chapter12HilbertFamily D H T P) := by
  sorry

/-- Scheme-theoretic inverse image of a Hilbert family along a map of tests. -/
noncomputable def chapter12PullbackFamily
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (Z : Chapter12HilbertFamily D H U P) :
    Chapter12HilbertFamily D H T P :=
  Classical.choice (chapter12_pullback_family_exists D H g Z)

theorem chapter12PullbackFamily_id
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial} {T : Chapter12SchemeOver D.base}
    (Z : Chapter12HilbertFamily D H T P) :
    chapter12PullbackFamily D H (𝟙 T) Z = Z := by
  sorry

theorem chapter12PullbackFamily_comp
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T U V : Chapter12SchemeOver D.base} (g : T ⟶ U) (h : U ⟶ V)
    (Z : Chapter12HilbertFamily D H V P) :
    chapter12PullbackFamily D H g (chapter12PullbackFamily D H h Z) =
      chapter12PullbackFamily D H (g ≫ h) Z := by
  sorry

/-- The constant numerical polynomial `d`. -/
def chapter12ConstantPolynomial (d : ℕ) : Chapter12NumericalPolynomial :=
  Polynomial.C (d : ℚ)

@[simp]
theorem chapter12ConstantPolynomial_eval (d n : ℕ) :
    (chapter12ConstantPolynomial d).eval (n : ℚ) = (d : ℚ) := by
  simp [chapter12ConstantPolynomial]

/-- A finite locally free morphism of rank `d`, with the fiber-length interface explicit. -/
structure Chapter12FiniteLocallyFreeRank
    (L : Chapter12FiberLengthTheory)
    {X T : Scheme} (f : X ⟶ T) (d : ℕ) : Prop where
  finite : IsFinite f
  flat : Flat f
  finitePresentation : LocallyOfFinitePresentation f
  rank : ∀ t : Chapter12GeometricPoint T, L.fiberLength f t = d

/- LOCAL_DEPENDENCY_GUESS: the preceding Hilbert-polynomial chapters should
  supply these two standard comparison theorems. They connect the numerical
  fiber Hilbert polynomial with geometric fiber length and use projectivity to
  turn constant zero-dimensional fibers into a finite morphism. -/
structure Chapter12HilbertLengthCompatibility
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (L : Chapter12FiberLengthTheory) : Prop where
  polynomial_iff_fiber_length :
    ∀ {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
      (t : Chapter12GeometricPoint T.left) (d : ℕ),
      chapter12HasFiberHilbertPolynomial H Z t (chapter12ConstantPolynomial d) ↔
        L.fiberLength (chapter12FamilyProjection D T Z.ideal) t = d
  finite_of_constant_fiber_length :
    ∀ {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
      (d : ℕ),
      (∀ t : Chapter12GeometricPoint T.left,
        L.fiberLength (chapter12FamilyProjection D T Z.ideal) t = d) →
        IsFinite (chapter12FamilyProjection D T Z.ideal)

/-!
The ideal-sheaf representation is the set-valued part of the functor: an
object is an ideal sheaf, not an arbitrary quotient object with a chosen
isomorphic presentation.
-/

theorem chapter12_family_ideal_kernel
    (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base}
    (Z : Chapter12ClosedFamily D T) :
    (chapter12FamilyInclusion D T Z).ker = Z.ideal := by
  simp [chapter12FamilyInclusion]

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
