import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

/-!
## Shared interfaces for Chapter 2

Mathlib's `reesAlgebra` is the canonical subalgebra of `R[X]` with coefficient `n` in `I^n`.
The chapter adds the grading, sheaf, and normalization interfaces that are not bundled by the
pinned checkout.  These interfaces keep the actual algebraic carrier visible to later proofs.
-/

/-- The ring-level Rees algebra used throughout this chapter. -/
abbrev Chapter02ReesAlgebra (R : Type u) [CommRing R] (I : Ideal R) :=
  reesAlgebra I

/-- The elementary non-zero-divisor predicate used in the principal-ideal example. -/
def Chapter02NonZeroDivisor {R : Type u} [Semiring R] (f : R) : Prop :=
  ∀ ⦃a : R⦄, f * a = 0 → a = 0

theorem chapter02_nonZeroDivisor_iff_isRegular
    {R : Type u} [CommSemiring R] (f : R) :
    Chapter02NonZeroDivisor f ↔ IsRegular f := by
  sorry

/-- A book-facing package for an internally graded algebra. -/
structure Chapter02GradedAlgebra
    (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] where
  component : ℕ → Submodule R A
  graded : GradedAlgebra component

/-- A coherent ideal sheaf, reusing the earlier module-sheaf interface. -/
structure Chapter02CoherentIdealSheaf (X : Scheme.{u}) where
  carrier : X.Modules
  inclusion : carrier ⟶ SheafOfModules.unit X.ringCatSheaf
  inclusion_mono : Mono inclusion
  quasiCoherent : carrier.IsQuasicoherent
  finiteType : carrier.IsFiniteType

/-- Tensor product of two module sheaves, with sheafification made explicit. -/
noncomputable def chapter02Tensor
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj M.val N.val)

/-- The sheaf-theoretic tensor powers used for the sheafified Rees algebra. -/
noncomputable def chapter02TensorPower
    {X : Scheme.{u}} (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => chapter02Tensor (chapter02TensorPower M n) M

/- A categorical carrier for the multiplication and unit maps of a graded sheaf algebra. -/
structure Chapter02SheafGradedAlgebraData
    (X : Scheme.{u}) (component : ℕ → X.Modules) where
  multiplication : ∀ m n, chapter02Tensor (component m) (component n) ⟶ component (m + n)
  unit : SheafOfModules.unit X.ringCatSheaf ⟶ component 0

def Chapter02SheafFiniteTypeAlgebra
    (X : Scheme.{u}) (component : ℕ → X.Modules) : Prop :=
  (component 1).IsFiniteType ∧
    ∀ n, Nonempty (component n ≅ chapter02TensorPower (component 1) n)

/- The finite-normalization consequence of the excellence hypothesis used in this chapter. -/
def Chapter02FiniteNormalizationProperty
    (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [Algebra.FiniteType R S], Module.Finite R S

/- A relative-Proj presentation over an affine base, used for projectivity witnesses. -/
structure Chapter02AffineProjectivePresentation
    (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) where
  A : Type u
  [commRingA : CommRing A]
  [algebraA : Algebra R A]
  component : ℕ → Submodule R A
  [graded : GradedAlgebra component]
  degreeZeroEquiv : R ≃+* (component 0)
  iso : X ≅ AlgebraicGeometry.«Proj» component
  iso_over :
    iso.hom ≫ AlgebraicGeometry.Proj.toSpecZero component ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom degreeZeroEquiv.toRingHom) = f

/-- Invertibility of an ideal as an `R`-module. -/
def Chapter02InvertibleIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  Nonempty (Module.Invertible R I)

/-- The finite-type surface hypothesis not supplied by the pinned scheme API. -/
structure Chapter02ExcellentFiniteTypeSurface
    (R : Type u) [CommRing R] : Prop where
  excellent : Chapter02FiniteNormalizationProperty R
  finiteTypeSurface : ringKrullDim R = 2

/-- Regularity of all local rings, using Mathlib's canonical local regularity class. -/
def Chapter02RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x).carrier

/-- A surface predicate kept abstract because the pinned API has no scheme-dimension class. -/
def Chapter02RegularSurface (X : Scheme.{u}) : Prop :=
  Chapter02RegularScheme X ∧
    ∀ U : X.affineOpens, U.1.Nonempty →
      ringKrullDim (X.presheaf.obj (Opposite.op U.1)).carrier = 2

/- The geometric data retained by the chapter's local blowup interface. -/
structure Chapter02OrdinaryBlowupAtPointData
    (X Y : Scheme.{u}) (x : X) where
  morphism : Y ⟶ X
  center : X.IdealSheafData
  center_support : (center.support : Set X) = ({x} : Set X)
  exceptionalLocus : Set Y
  exceptionalLocus_maps_to_center :
    ∀ y : Y, y ∈ exceptionalLocus → morphism y = x

def Chapter02OrdinaryBlowupAtPoint
    (X Y : Scheme.{u}) (x : X) : Prop :=
  Nonempty (Chapter02OrdinaryBlowupAtPointData X Y x)

/- A normalization certificate records the normal source and its birational map. -/
structure Chapter02SchemeNormalizationData (X Y : Scheme.{u}) where
  morphism : Y ⟶ X
  normal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y).carrier
  birational : Scheme.Birational Y X

def Chapter02SchemeNormalization
    (X Y : Scheme.{u}) : Prop :=
  Nonempty (Chapter02SchemeNormalizationData X Y)

/-- A local package for the ordinary blowup warning at a regular closed point. -/
structure Chapter02RegularSurfaceClosedPoint where
  scheme : Scheme.{u}
  point : scheme
  pointClosed : IsClosed ({point} : Set scheme)
  regularSurface : Chapter02RegularSurface scheme
  ordinaryBlowup : Scheme.{u}
  ordinaryBlowupIsBlowupAtPoint :
    Chapter02OrdinaryBlowupAtPoint scheme ordinaryBlowup point

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
