import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.NoetherianSpace
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section02RelativeEffectiveCartierDivisors
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section02SingleCoversAndAffineReduction

/-!
## Chapter 16 dependencies

This file contains only interfaces shared by the four source sections.  The pinned Mathlib tree
does not yet package generalized elliptic curves, PEL structures, or their moduli functors, so the
small records below make those missing inputs explicit instead of hiding them in theorem
hypotheses.  Finiteness and positivity are deliberately routed through the earlier Book 8 APIs.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v w

abbrev Chapter16FpqcMorphism {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.IsFpqcMorphism p

abbrev Chapter16FppfCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.FppfCoveringFamily F

abbrev Chapter16FpqcCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.FpqcCoveringFamily F

theorem chapter16_fpqcMorphism_iff {S T : Scheme.{u}} (p : T ⟶ S) :
    Chapter16FpqcMorphism p ↔ Flat p ∧ QuasiCompact p ∧ Surjective p := Iff.rfl

abbrev Chapter16FiniteLocallyFreeProfile {X Y : Scheme.{u}} (q : X ⟶ Y) (d : ℕ) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiniteLocallyFreeProfile
    q d

abbrev Chapter16FiniteLocallyFreeMorphism {X Y : Scheme.{u}} (q : X ⟶ Y) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiniteLocallyFreeMorphism
    q

abbrev Chapter16LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.LineBundle X

abbrev Chapter16IsAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter16LineBundle X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsAmple f L

abbrev Chapter16IsProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsProjectiveMorphism f

/-! ### Fixed coefficient algebras -/

/- The involution is written out rather than relying on a competing `StarRing` wrapper.  In the
 applications the carrier is finite as a `ℤ`-module; this is weaker and more useful than making the
 underlying type finite. -/
structure Chapter16FiniteAlgebraWithInvolution where
  carrier : Type u
  [ring : CommRing carrier]
  finite : Module.Finite ℤ carrier
  star : carrier → carrier
  star_zero : star 0 = 0
  star_one : star 1 = 1
  star_add : ∀ a b, star (a + b) = star a + star b
  star_mul : ∀ a b, star (a * b) = star b * star a
  star_star : ∀ a, star (star a) = a

namespace Chapter16FiniteAlgebraWithInvolution

variable (O : Chapter16FiniteAlgebraWithInvolution)

instance : CommRing O.carrier := O.ring

@[simp] theorem star_zero : O.star 0 = 0 := O.star_zero

@[simp] theorem star_one : O.star 1 = 1 := O.star_one

theorem star_add (a b : O.carrier) : O.star (a + b) = O.star a + O.star b := O.star_add a b

theorem star_mul (a b : O.carrier) : O.star (a * b) = O.star b * O.star a := O.star_mul a b

@[simp] theorem star_star (a : O.carrier) : O.star (O.star a) = a := O.star_star a

end Chapter16FiniteAlgebraWithInvolution

/-! ### Basic descent certificates -/

/-!
The overlap isomorphism and cocycle are kept as book-facing fields because the canonical
pullback-whiskering of an arbitrary structured object is not a single Mathlib structure.  The
carrier map and the overlap maps are nevertheless concrete scheme morphisms, so this record can be
refined without changing any theorem statements.
-/
structure Chapter16SchemeDescentDatum {S T : Scheme.{u}} (g : T ⟶ S) where
  cover : Chapter16FpqcMorphism g
  carrier : Scheme.{u}
  structureMap : carrier ⟶ T
  overlap : Scheme.{u} := pullback g g
  overlapFst : overlap ⟶ T := pullback.fst g g
  overlapSnd : overlap ⟶ T := pullback.snd g g
  overlapIso :
    pullback structureMap overlapFst ≅ pullback structureMap overlapSnd
  overlapIsoOver :
    overlapIso.hom ≫ pullback.snd structureMap overlapSnd =
      pullback.snd structureMap overlapFst
  cocycle : Prop

/- The canonical Mathlib descent-data object remains available for functors whose structured
 objects have already been packaged as a pseudofunctor. -/
structure Chapter16CanonicalDescentData
    {S : Scheme.{u}} {I : Type v}
    (family : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.SchemeFamily S I)
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u}) where
  covering : Chapter16FpqcCoveringFamily family
  data : F.DescentData family.map

structure Chapter16FieldExtension (k K : Type u) [Field k] [Field K] where
  algebra : Algebra k K
  injective : Function.Injective (algebraMap k K)

structure Chapter16EulerCharacteristicData where
  dimension : ℕ → ℕ
  cohomologicalBound : ℕ
  vanishesAbove : ∀ i, cohomologicalBound < i → dimension i = 0

def chapter16EulerCharacteristic (C : Chapter16EulerCharacteristicData) : ℤ :=
  ∑ i in Finset.range (C.cohomologicalBound + 1),
    (-1 : ℤ) ^ i * (C.dimension i : ℤ)

def chapter16ArithmeticGenus (C : Chapter16EulerCharacteristicData) : ℤ :=
  1 - chapter16EulerCharacteristic C

theorem chapter16_euler_characteristic_formula (C : Chapter16EulerCharacteristicData) :
    chapter16EulerCharacteristic C =
      ∑ i in Finset.range (C.cohomologicalBound + 1),
        (-1 : ℤ) ^ i * (C.dimension i : ℤ) := rfl

theorem chapter16_euler_characteristic_congr
    (C D : Chapter16EulerCharacteristicData)
    (hbound : C.cohomologicalBound = D.cohomologicalBound)
    (hdim : ∀ i, C.dimension i = D.dimension i) :
    chapter16EulerCharacteristic C = chapter16EulerCharacteristic D := by
  sorry

theorem chapter16_arithmetic_genus_congr
    (C D : Chapter16EulerCharacteristicData)
    (h : chapter16EulerCharacteristic C = chapter16EulerCharacteristic D) :
    chapter16ArithmeticGenus C = chapter16ArithmeticGenus D := by
  simp [chapter16ArithmeticGenus, h]

/-! ### Finite component and plane-node interfaces -/

structure Chapter16ComponentIndex (X : Scheme.{u}) (m : ℕ) where
  component : Fin m → Set X
  nonempty : ∀ i, (component i).Nonempty
  pairwise_distinct : Pairwise (fun i j => component i ≠ component j)
  covers : (Set.univ : Set X) = ⋃ i, component i

def Chapter16MeetsEveryComponent {X : Scheme.{u}} {m : ℕ}
    (C : Chapter16ComponentIndex X m) (D : Set X) : Prop :=
  ∀ i, (D ∩ C.component i).Nonempty

theorem chapter16_meetsEveryComponent_iff {X : Scheme.{u}} {m : ℕ}
    (C : Chapter16ComponentIndex X m) (D : Set X) :
    Chapter16MeetsEveryComponent C D ↔ ∀ i, (D ∩ C.component i).Nonempty := Iff.rfl

/- LOCAL_DEPENDENCY_GUESS: the pinned tree has etale morphisms and affine scheme models, but no
 packaged plane-node certificate.  This record is the minimal local interface for the uv = 0
 assertion used by the polygon descent argument. -/
structure Chapter16PlaneNodeModel (X : Scheme.{u}) (k : Type u)
    [Field k] [IsAlgClosed k] where
  point : X
  neighborhood : Scheme.{u}
  neighborhoodMap : neighborhood ⟶ X
  etale : Etale neighborhoodMap
  model : neighborhood ≅
    Spec (CommRingCat.of
      (MvPolynomial (Fin 2) k ⧸
        Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))))
  pointInImage : point ∈ Set.range neighborhoodMap

structure Chapter16FiberComponentData (X : Scheme.{u}) (m : ℕ) where
  index : Chapter16ComponentIndex X m
  next : Fin m → Fin m
  next_bijective : Function.Bijective next
  incidence : Prop

/-! ### Linear algebra used by determinant and pairing conditions -/

structure Chapter16PerfectAlternatingPairing (R M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] where
  pairing : M →ₗ[R] (M →ₗ[R] R)
  perfect : Function.Bijective pairing
  alternating : ∀ x, pairing x x = 0

def Chapter16Isotropic {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (P : Chapter16PerfectAlternatingPairing R M) (N : Submodule R M) : Prop :=
  ∀ x ∈ N, ∀ y ∈ N, P.pairing x y = 0

structure Chapter16SimilitudePairing (R M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M] where
  pairing : M →ₗ[R] (M →ₗ[R] R)
  factor : R
  similitude : Prop

/- LOCAL_DEPENDENCY_GUESS: a sheaf-level Lie algebra is not exposed by the pinned Mathlib API in a
 form shared by the earlier chapters.  The module-level record below keeps finite freeness and the
 characteristic-polynomial equation explicit until that API is reconciled. -/
structure Chapter16LieDeterminantData (O : Chapter16FiniteAlgebraWithInvolution)
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] where
  lieModule : M
  action : O.carrier → Module.End R M
  prescribed : O.carrier → Polynomial R
  characteristic_polynomial : ∀ a, (action a).charpoly = prescribed a

def Chapter16Isogeny {X Y : Scheme.{u}} (φ : X ⟶ Y) : Prop :=
  IsFinite φ ∧ Flat φ ∧ LocallyOfFinitePresentation φ ∧ Surjective φ

theorem chapter16_isogeny_iff {X Y : Scheme.{u}} (φ : X ⟶ Y) :
    Chapter16Isogeny φ ↔
      IsFinite φ ∧ Flat φ ∧ LocallyOfFinitePresentation φ ∧ Surjective φ := Iff.rfl

theorem chapter16_reflects_equality_after_faithful_map
    {α β : Type u} (e : α → β) (he : Function.Injective e)
    {x y : α} (h : e x = e y) : x = y :=
  he h

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
