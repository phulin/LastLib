import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Core
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Section04LocalityAndProjectivity

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry BigOperators DirectSum

universe u v

/-! ## Shared resolution interfaces -/

def chapter08RegularLocus (X : Scheme.{u}) : Set X :=
  {x | IsRegularLocalRing (X.presheaf.stalk x)}

@[simp]
theorem chapter08_mem_regularLocus_iff {X : Scheme.{u}} {x : X} :
    x ∈ chapter08RegularLocus X ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

def chapter08SingularLocus (X : Scheme.{u}) : Set X :=
  (chapter08RegularLocus X)ᶜ

theorem chapter08_mem_singularLocus_iff {X : Scheme.{u}} {x : X} :
    x ∈ chapter08SingularLocus X ↔ ¬ IsRegularLocalRing (X.presheaf.stalk x) := by
  rfl

def Chapter08SurfaceDimensionBound (X : Scheme.{u}) : Prop :=
  ∀ x : X, Order.coheight x ≤ 2

structure Chapter08ExcellentSurfaceInput (X : Scheme.{u}) : Prop where
  reduced : IsReduced X
  noetherian : IsNoetherian X
  excellent : Chapter01ExcellentScheme X
  dimension_le_two : Chapter08SurfaceDimensionBound X

theorem chapter08_excellentSurfaceInput_noetherian
    {X : Scheme.{u}} (hX : Chapter08ExcellentSurfaceInput X) :
    IsNoetherian X :=
  hX.noetherian

structure Chapter08NormalNoetherianSurface (X : Scheme.{u}) : Prop where
  normal : Chapter07NormalIntegralScheme X
  noetherian : IsNoetherian X
  dimension_le_two : Chapter08SurfaceDimensionBound X

structure Chapter08FiniteNormalization (X : Scheme.{u}) where
  carrier : Scheme.{u}
  map : carrier ⟶ X
  finite : IsFinite map
  integral : IsIntegralHom map
  normal : Chapter03NormalScheme carrier
  birational : Chapter07Birational map

def Chapter08ClosedNowhereDenseCenter
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Prop :=
  IsClosed I.support ∧ IsNowhereDense I.support

theorem chapter08_coherentIdeal_support_is_closed
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) :
    IsClosed I.support :=
  chapter07_coherentIdeal_support_isClosed I

/- The inductive chain is the source-facing refinement of Chapter 07's projective modification
   chain: blowup constructors carry the nowhere-dense center condition, while normalization
   constructors carry the integral, birational, and finite hypotheses. -/
inductive Chapter08ResolutionModification :
    {Y X : Scheme.{u}} → (Y ⟶ X) → Prop
  | blowup {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
      (B : Chapter07Blowup I)
      (hcenter : Chapter08ClosedNowhereDenseCenter I) :
      Chapter08ResolutionModification B.projection
  | normalization {Y X : Scheme.{u}} (f : Y ⟶ X)
      (hfinite : IsFinite f)
      (hnormalization : Chapter07RelativeNormalizationMorphism f) :
      Chapter08ResolutionModification f
  | comp {Z Y X : Scheme.{u}} {g : Z ⟶ Y} {f : Y ⟶ X}
      (hg : Chapter08ResolutionModification g)
      (hf : Chapter08ResolutionModification f) :
      Chapter08ResolutionModification (g ≫ f)

structure Chapter08ResolutionData (X : Scheme.{u}) (U : X.Opens) where
  carrier : Scheme.{u}
  map : carrier ⟶ X
  regular : Chapter04RegularScheme carrier
  proper : IsProper map
  birational : Chapter07Birational map
  modification : Chapter08ResolutionModification map
  isIso_over_U : IsIso (map ∣_ U)

structure Chapter08ProjectiveResolutionData (X : Scheme.{u}) (U : X.Opens)
    extends Chapter08ResolutionData X U where
  projective : Chapter07IsProjectiveMorphism map

def Chapter08LocallyFiniteSet {X : Scheme.{u}} (s : Set X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (s ∩ (U : Set X)).Finite

def Chapter08ClosedPointSet {X : Scheme.{u}} (s : Set X) : Prop :=
  ∀ x : X, x ∈ s → IsClosed ({x} : Set X)

structure Chapter08NormalArithmeticSurface where
  surface : Chapter07ArithmeticSurface
  normalModel : Chapter08NormalNoetherianSurface surface.model
  excellentModel : Chapter01ExcellentScheme surface.model

def chapter08ArithmeticSurfaceSingularLocus
    (M : Chapter08NormalArithmeticSurface) : Set M.surface.model :=
  chapter08SingularLocus M.surface.model

def chapter08ArithmeticSurfaceRegularLocus
    (M : Chapter08NormalArithmeticSurface) : Set M.surface.model :=
  chapter08RegularLocus M.surface.model

/-! ## Local algebra interfaces used by the decreasing invariant -/

def chapter08MaximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] : Ideal A :=
  IsLocalRing.maximalIdeal A

def chapter08MaximalIdealPowerQuotient
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Type u :=
  A ⧸ (chapter08MaximalIdeal A ^ (n + 1) : Ideal A)

def chapter08RingQuotientLength
    (A : Type u) [CommRing A] (J : Ideal A) : ℕ∞ :=
  Module.length A (A ⧸ J)

def chapter08AssociatedGradedPiece
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) : Type u :=
  (chapter08MaximalIdeal A ^ n : Submodule A A) ⧸
    (chapter08MaximalIdeal A ^ (n + 1) : Submodule A A).comap
      (chapter08MaximalIdeal A ^ n : Submodule A A).subtype

abbrev chapter08AssociatedGraded
    (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  ⨁ n : ℕ, chapter08AssociatedGradedPiece A n

def chapter08AssociatedGradedMk
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ)
    (a : (chapter08MaximalIdeal A ^ n : Submodule A A)) :
    chapter08AssociatedGradedPiece A n :=
  Submodule.Quotient.mk a

theorem chapter08_associatedGraded_mk_eq_zero_iff
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ)
    (a : (chapter08MaximalIdeal A ^ n : Submodule A A)) :
    chapter08AssociatedGradedMk A n a = 0 ↔
      (a : A) ∈ (chapter08MaximalIdeal A ^ (n + 1) : Ideal A) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: Mathlib supplies the graded pieces as quotients but not the ring
   multiplication on their external direct sum in the pinned snapshot.  This is the minimal
   reusable associated-graded interface; its multiplication is not used to smuggle in any
   resolution conclusion. -/
structure Chapter08AssociatedGradedRingData
    (A : Type u) [CommRing A] [IsLocalRing A] where
  commRing : CommRing (chapter08AssociatedGraded A)

theorem chapter08_associatedGraded_ring_exists
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Nonempty (Chapter08AssociatedGradedRingData A) := by
  sorry

noncomputable instance chapter08AssociatedGradedCommRing
    (A : Type u) [CommRing A] [IsLocalRing A] :
    CommRing (chapter08AssociatedGraded A) :=
  (Classical.choice (chapter08_associatedGraded_ring_exists A)).commRing

abbrev Chapter08ZariskiTangentSpace
    (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  CotangentSpace A →ₗ[ResidueField A] ResidueField A

structure Chapter08ResidueFieldExtension
    (A : Type u) [CommRing A] [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (ResidueField A) K] where
  finite : FiniteDimensional (ResidueField A) K
  unramified : Prop

abbrev chapter08ExtendedTangentSpace
    (A : Type u) [CommRing A] [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (ResidueField A) K] : Type u :=
  Chapter08ZariskiTangentSpace A ⊗[ResidueField A] K

def chapter08TranslationPreservesCone
    {K T : Type u} [Field K] [AddCommGroup T] [Module K T]
    (C : Set T) (W : Submodule K T) : Prop :=
  ∀ w : T, w ∈ W → (fun z : T => z + w) '' C = C

/-! The `identification` field records the pinned local bridge from the tangent-cone construction
to the chosen affine set of tangent directions. -/
structure Chapter08DirectrixProfile
    (A : Type u) [CommRing A] [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (ResidueField A) K] where
  extension : Chapter08ResidueFieldExtension A K
  cone : Set (chapter08ExtendedTangentSpace A K)
  identification : Prop
  directrix : Submodule K (chapter08ExtendedTangentSpace A K)
  directrix_preserves :
    chapter08TranslationPreservesCone cone directrix
  maximal : ∀ W : Submodule K (chapter08ExtendedTangentSpace A K),
    chapter08TranslationPreservesCone cone W →
      Module.finrank K W ≤ Module.finrank K directrix

def chapter08DirectrixDimension
    {A : Type u} [CommRing A] [IsLocalRing A]
    {K : Type u} [Field K] [Algebra (ResidueField A) K]
    (D : Chapter08DirectrixProfile A K) : ℕ :=
  Module.finrank K D.directrix

def chapter08ElementOrder
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) : ℕ∞ :=
  sSup (Set.range fun n : {n : ℕ // a ∈ (chapter08MaximalIdeal A ^ n : Ideal A)} =>
    (n.1 : ℕ∞))

def Chapter08MaximalOrderGenerated
    {A : Type u} [CommRing A] [IsLocalRing A]
    (I : Ideal A) : Prop :=
  ∃ E : Set A, E.Nonempty ∧ I = Ideal.span E ∧
    ∃ q : ℕ∞, (∀ a, a ∈ E → chapter08ElementOrder A a = q) ∧
      (∀ q' : ℕ∞, (∀ a, a ∈ E → chapter08ElementOrder A a = q') → q' ≤ q)

def Chapter08MPrimaryIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A) : Prop :=
  I.radical = chapter08MaximalIdeal A

def Chapter08UnmixedLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] : Prop :=
  ∀ p : Ideal A, p ∈ Module.associatedPrimes A A →
    ringKrullDim (A ⧸ p) = ringKrullDim A

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
