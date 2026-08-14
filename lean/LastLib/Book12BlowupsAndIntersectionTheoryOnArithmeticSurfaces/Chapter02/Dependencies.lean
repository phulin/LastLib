import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section02EffectiveCartierDivisors

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

/-- A coherent ideal sheaf, with its canonical affine finite-generation condition. -/
structure Chapter02CoherentIdealSheaf (X : Scheme.{u}) where
  ideal : X.IdealSheafData
  finiteType : ∀ U : X.affineOpens, (ideal.ideal U).FG

instance {X : Scheme.{u}} : Coe (Chapter02CoherentIdealSheaf X) X.IdealSheafData :=
  ⟨Chapter02CoherentIdealSheaf.ideal⟩

/-- The module of sections of a coherent ideal sheaf, obtained from its ideal-sheaf kernel. -/
noncomputable abbrev Chapter02CoherentIdealSheaf.carrier
    {X : Scheme.{u}} (I : Chapter02CoherentIdealSheaf X) : X.Modules :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.chapter02IdealOminusD
    I.ideal

/-- The canonical module carrier of the `n`th ideal power. -/
noncomputable abbrev Chapter02CoherentIdealSheaf.powerCarrier
    {X : Scheme.{u}} (I : Chapter02CoherentIdealSheaf X) (n : ℕ) : X.Modules :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.chapter02IdealOminusD
    (I.ideal ^ n)

/- An ideal-sheaf version of invertibility: local principal generators are required to be
regular, which is the hypothesis used by the blowup universal property. -/
def Chapter02IsInvertibleIdealSheaf
    {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    I.ideal U = Ideal.span {a} ∧ IsRegular a

/-- Tensor product of two module sheaves, with sheafification made explicit. -/
noncomputable abbrev chapter02Tensor
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.chapter01SheafTensor M N

/-- The functorial map on the sheafified tensor carrier. -/
noncomputable abbrev chapter02SheafTensorMap
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    chapter02Tensor M N ⟶ chapter02Tensor M' N' := by
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.chapter01SheafTensorMap f g

/-- The associator for the sheafified tensor carrier. -/
noncomputable abbrev chapter02SheafTensorAssociator
    {X : Scheme.{u}} (M N P : X.Modules) :
    chapter02Tensor (chapter02Tensor M N) P ≅
      chapter02Tensor M (chapter02Tensor N P) := by
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.chapter01SheafTensorAssociator M N P

/-- The left unitor for the sheafified tensor carrier. -/
noncomputable abbrev chapter02SheafTensorLeftUnitor
    {X : Scheme.{u}} (M : X.Modules) :
    chapter02Tensor (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.chapter01SheafTensorLeftUnitor M

/-- The right unitor for the sheafified tensor carrier. -/
noncomputable abbrev chapter02SheafTensorRightUnitor
    {X : Scheme.{u}} (M : X.Modules) :
    chapter02Tensor M (SheafOfModules.unit X.ringCatSheaf) ≅ M := by
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.chapter01SheafTensorRightUnitor M

/-- The symmetry for the sheafified tensor carrier. -/
noncomputable abbrev chapter02SheafTensorSymmetry
    {X : Scheme.{u}} (M N : X.Modules) :
    chapter02Tensor M N ≅ chapter02Tensor N M := by
  exact
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.chapter01SheafTensorSymmetry M N

/-! The sheaf-theoretic tensor powers used for the sheafified Rees algebra. -/
noncomputable def chapter02TensorPower
    {X : Scheme.{u}} (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => chapter02Tensor (chapter02TensorPower M n) M

/- A commutative graded-algebra carrier for sheaves of modules.  The coherence fields are
   explicit because the pinned sheaf API does not package a monoidal algebra object. -/
structure Chapter02SheafGradedAlgebraData
    (X : Scheme.{u}) (component : ℕ → X.Modules) where
  multiplication : ∀ m n, chapter02Tensor (component m) (component n) ⟶ component (m + n)
  unit : SheafOfModules.unit X.ringCatSheaf ⟶ component 0
  unit_left : ∀ n,
    chapter02SheafTensorMap unit (𝟙 (component n)) ≫
        multiplication 0 n ≫
        eqToHom (congrArg component (Nat.zero_add n) : component (0 + n) = component n) =
      (chapter02SheafTensorLeftUnitor (component n)).hom
  unit_right : ∀ n,
    chapter02SheafTensorMap (𝟙 (component n)) unit ≫
        multiplication n 0 ≫
        eqToHom (congrArg component (Nat.add_zero n) : component (n + 0) = component n) =
      (chapter02SheafTensorRightUnitor (component n)).hom
  multiplication_assoc : ∀ m n k,
    chapter02SheafTensorMap (multiplication m n) (𝟙 (component k)) ≫
        multiplication (m + n) k ≫
        eqToHom (congrArg component (Nat.add_assoc m n k) :
          component ((m + n) + k) = component (m + (n + k))) =
      (chapter02SheafTensorAssociator (component m) (component n) (component k)).hom ≫
        chapter02SheafTensorMap (𝟙 (component m)) (multiplication n k) ≫
        multiplication m (n + k)
  multiplication_comm : ∀ m n,
    multiplication m n =
      (chapter02SheafTensorSymmetry (component m) (component n)).hom ≫
        multiplication n m ≫
        eqToHom (congrArg component (Nat.add_comm n m) :
          component (n + m) = component (m + n))

/- A finite-type graded algebra is finitely generated in the homogeneous sense.  The pinned
  sheaf API has no graded-algebra finite-generation predicate, so we retain both the componentwise
  finite-type condition and the degree-one generation certificate used by the Rees construction. -/
def Chapter02SheafFiniteTypeAlgebra
    (X : Scheme.{u}) (component : ℕ → X.Modules) : Prop :=
  (∀ n, (component n).IsFiniteType) ∧
    ∀ n, ∃ e : chapter02TensorPower (component 1) n ⟶ component n, Epi e

/- The finite-normalization consequence of the excellence hypothesis used in this chapter.  The
extension algebra is required to be finite type over the ambient algebra, rather than requiring the
integral closure itself to be finite type; the latter would make this hypothesis unable to express
the normalization theorem. -/
def Chapter02FiniteNormalizationProperty
    (R : Type u) [CommRing R] : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsDomain A] [IsDomain B] [Algebra.FiniteType R A] [Algebra.FiniteType A B],
    Module.Finite A (integralClosure A B)

/- A relative-Proj presentation over an affine base, used for projectivity witnesses. -/
structure Chapter02AffineProjectivePresentation
    (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) where
  A : Type u
  [commRingA : CommRing A]
  [algebraA : Algebra R A]
  [finiteTypeA : Algebra.FiniteType R A]
  component : ℕ → Submodule R A
  [graded : GradedAlgebra component]
  degreeZeroEquiv : R ≃+* (component 0)
  degreeZeroEquiv_algebraMap : ∀ r, algebraMap R A r = (degreeZeroEquiv r : A)
  iso : X ≅ AlgebraicGeometry.«Proj» component
  iso_over :
    iso.hom ≫ AlgebraicGeometry.Proj.toSpecZero component ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom degreeZeroEquiv.toRingHom) = f

/-- Invertibility of an ideal as an `R`-module. -/
def Chapter02InvertibleIdeal {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  Nonempty (Module.Invertible R I)

/-- The finite-type surface hypothesis not supplied by the pinned scheme API. -/
structure Chapter02ExcellentFiniteTypeSurface
    (R : Type u) [CommRing R] where
  base : Type u
  [baseCommRing : CommRing base]
  [baseAlgebra : Algebra base R]
  [finiteTypeOverBase : Algebra.FiniteType base R]
  excellent : Chapter02FiniteNormalizationProperty R
  surfaceDimension : ringKrullDim R = 2

/-- Regularity of all local rings, using Mathlib's canonical local regularity class. -/
def Chapter02RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x).carrier

/-- A surface predicate kept abstract because the pinned API has no scheme-dimension class.

The dimension condition is phrased as ``at most two everywhere and attained on an affine open``.
Requiring every nonempty affine open to have dimension exactly two would incorrectly exclude
ordinary two-dimensional local schemes: a principal open can have smaller dimension. -/
def Chapter02RegularSurface (X : Scheme.{u}) : Prop :=
  IsIntegral X ∧
    IsLocallyNoetherian X ∧
    Chapter02RegularScheme X ∧
    (∀ (U : X.affineOpens), Set.Nonempty (U : Set X) →
      ringKrullDim (X.presheaf.obj (Opposite.op U.1)).carrier ≤ 2) ∧
    ∃ (U : X.affineOpens), Set.Nonempty (U : Set X) ∧
      ringKrullDim (X.presheaf.obj (Opposite.op U.1)).carrier = 2

/- The geometric data retained by the chapter's local blowup interface. -/
structure Chapter02OrdinaryBlowupAtPointData
    (X Y : Scheme.{u}) (x : X) where
  morphism : Y ⟶ X
  center : X.IdealSheafData
  center_support : (center.support : Set X) = ({x} : Set X)
  center_eq_pointIdeal :
    center = Scheme.IdealSheafData.vanishingIdeal center.support
  tautological : Y.IdealSheafData
  tautological_eq_pullback : tautological = center.comap morphism
  tautological_isInvertible : Chapter02IsInvertibleIdealSheaf tautological
  universal : ∀ {T : Scheme.{u}} (g : T ⟶ X),
    Chapter02IsInvertibleIdealSheaf (center.comap g) →
      ∃! h : T ⟶ Y, h ≫ morphism = g

def Chapter02OrdinaryBlowupAtPoint
    (X Y : Scheme.{u}) (x : X) : Prop :=
  Nonempty (Chapter02OrdinaryBlowupAtPointData X Y x)

/- A normalization certificate records the normal source and its birational map. -/
structure Chapter02SchemeNormalizationData (X Y : Scheme.{u}) where
  morphism : Y ⟶ X
  finite : IsFinite morphism
  integral : IsIntegral Y
  locallyNoetherian : IsLocallyNoetherian Y
  integralMap : IsIntegralHom morphism
  normal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y).carrier
  birational :
    ∃ p : Scheme.PartialIso Y X,
      p.iso.hom ≫ p.target.ι = p.source.ι ≫ morphism

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
