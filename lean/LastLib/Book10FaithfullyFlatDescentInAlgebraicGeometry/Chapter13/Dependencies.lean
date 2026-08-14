import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Torsor.Defs
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.RingTheory.RootsOfUnity.Basic
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter08.Section03EffectivityAndFullFaithfulness
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section04SeparatednessAndQuasiCompactness
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

/-!
# Book 10, Chapter 13: torsors

This file contains the shared categorical interfaces for the four source sections.  Schemes over
`S` are represented by objects of `Over S`, and an `S`-group scheme by a group object in that
cartesian monoidal category.  Right actions are written explicitly so that the order of the
noncommutative cocycle is visible in the later section.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry MonObj

universe u v

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

abbrev Chapter13SchemeOver (S : Scheme.{u}) := Over S

abbrev Chapter13GroupScheme (S : Scheme.{u}) := Grp (Over S)

/-- A single fpqc cover, with the surjectivity and quasi-compactness made explicit. -/
def Chapter13FpqcCover {T S : Scheme.{u}} (f : T ⟶ S) : Prop :=
  Flat f ∧ Surjective f ∧ QuasiCompact f

/-- An fppf cover.  Surjectivity is included because a torsor must have local points. -/
def Chapter13FppfCover {T S : Scheme.{u}} (f : T ⟶ S) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f

/-- Finite locally free, expressed by the finite-flat-lfp package used by the rank API. -/
def Chapter13FiniteLocallyFree {T S : Scheme.{u}} (f : T ⟶ S) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f

/-- Constant rank `n` is a useful specialization of finite locally free. -/
def Chapter13FiniteLocallyFreeOfRank {T S : Scheme.{u}} (f : T ⟶ S) (n : ℕ) : Prop :=
  Chapter13FiniteLocallyFree f ∧ ∀ s : S, Scheme.Hom.finrank f s = n

/-- Positive rank is stated pointwise, so disconnected bases are not forced to have one rank. -/
def Chapter13FiniteLocallyFreeOfPositiveRank {T S : Scheme.{u}} (f : T ⟶ S) : Prop :=
  Chapter13FiniteLocallyFree f ∧ ∀ s : S, 0 < Scheme.Hom.finrank f s

def Chapter13SameFiniteLocallyFreeRank {T U S : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ S) : Prop :=
  ∀ s : S, Scheme.Hom.finrank f s = Scheme.Hom.finrank g s

/-! ### Actions -/

/-- A right action of an internal group object on an object over the same base. -/
structure Chapter13RightAction {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    (P : Chapter13SchemeOver S) where
  act : P ⊗ G.X ⟶ P
  one_act :
    (ρ_ P).inv ≫ (𝟙 P ⊗ₘ η[G.X]) ≫ act = 𝟙 P
  mul_act :
    (act ⊗ₘ 𝟙 G.X) ≫ act =
      (α_ P G.X G.X).hom ≫ (𝟙 P ⊗ₘ μ[G.X]) ≫ act

/-- A left action, used for contracted products. -/
structure Chapter13LeftAction {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    (X : Chapter13SchemeOver S) where
  act : G.X ⊗ X ⟶ X
  one_act :
    (λ_ X).inv ≫ (η[G.X] ⊗ₘ 𝟙 X) ≫ act = 𝟙 X
  mul_act :
    (μ[G.X] ⊗ₘ 𝟙 X) ≫ act =
      (α_ G.X G.X X).hom ≫ (𝟙 G.X ⊗ₘ act) ≫ act

/-- The regular right action of a group scheme on itself. -/
noncomputable def chapter13RegularRightAction {S : Scheme.{u}}
    (G : Chapter13GroupScheme S) : Chapter13RightAction G G.X where
  act := μ[G.X]
  one_act := by simp [MonoidalCategory.tensorHom_def]
  mul_act := by simp [MonoidalCategory.tensorHom_def, MonObj.mul_assoc]

/-- The regular left action of a group scheme on itself. -/
noncomputable def chapter13RegularLeftAction {S : Scheme.{u}}
    (G : Chapter13GroupScheme S) : Chapter13LeftAction G G.X where
  act := μ[G.X]
  one_act := by simp [MonoidalCategory.tensorHom_def]
  mul_act := by simp [MonoidalCategory.tensorHom_def, MonObj.mul_assoc]

/-- The scheme morphism `(p,g) ↦ (p,p·g)` attached to a right action. -/
noncomputable def chapter13TorsorComparisonMap {S : Scheme.{u}}
    {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) :
    pullback P.hom G.X.hom ⟶ pullback P.hom P.hom :=
  (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst P G.X) A.act).left

/-- The simply-transitive clause of the torsor definition. -/
def Chapter13TorsorIdentity {S : Scheme.{u}}
    {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) : Prop :=
  IsIso (chapter13TorsorComparisonMap A)

/-- An equivariant isomorphism of right `G`-spaces. -/
structure Chapter13EquivariantIso {S : Scheme.{u}}
    {G : Chapter13GroupScheme S} {P Q : Chapter13SchemeOver S}
    (Paction : Chapter13RightAction G P) (Qaction : Chapter13RightAction G Q) where
  iso : P ≅ Q
  equivariant :
    (iso.hom ⊗ₘ 𝟙 G.X) ≫ Qaction.act = Paction.act ≫ iso.hom

/-- A torsor before a topology has been chosen. -/
structure Chapter13TorsorData {S : Scheme.{u}} (G : Chapter13GroupScheme S) where
  carrier : Chapter13SchemeOver S
  action : Chapter13RightAction G carrier
  identity : Chapter13TorsorIdentity action

structure Chapter13FpqcTorsor {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    extends Chapter13TorsorData G where
  cover : Chapter13FpqcCover carrier.hom

structure Chapter13FppfTorsor {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    extends Chapter13TorsorData G where
  cover : Chapter13FppfCover carrier.hom

/-- Pullback of a group scheme along a morphism of bases. -/
noncomputable def chapter13BaseChangedGroup {S T : Scheme.{u}}
    (G : Chapter13GroupScheme S) (t : T ⟶ S) : Chapter13GroupScheme T :=
  (Over.pullback t).mapGrp.obj G

/-- The canonical pulled-back right action. -/
noncomputable def chapter13BaseChangedRightAction {S T : Scheme.{u}}
    {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) (t : T ⟶ S) :
    Chapter13RightAction (chapter13BaseChangedGroup G t) ((Over.pullback t).obj P) where
  act :=
    (CartesianMonoidalCategory.prodComparisonIso (Over.pullback t) P G.X).inv ≫
      (Over.pullback t).map A.act
  one_act := by
    dsimp [chapter13BaseChangedGroup]
    rw [← Functor.Monoidal.μ_of_cartesianMonoidalCategory (Over.pullback t) P G.X]
    change
      (ρ_ ((Over.pullback t).obj P)).inv ≫
          (𝟙 _ ⊗ₘ ((Functor.LaxMonoidal.ε (Over.pullback t)) ≫
            (Over.pullback t).map η[G.X])) ≫
        Functor.LaxMonoidal.μ (Over.pullback t) P G.X ≫
          (Over.pullback t).map A.act = 𝟙 _
    simp [MonoidalCategory.tensorHom_def, ← Functor.map_comp]
    simpa [MonoidalCategory.tensorHom_def] using congrArg ((Over.pullback t).map) A.one_act
  mul_act := by
    dsimp [chapter13BaseChangedGroup]
    rw [← Functor.Monoidal.μ_of_cartesianMonoidalCategory (Over.pullback t) P G.X]
    change
      ((Functor.LaxMonoidal.μ (Over.pullback t) P G.X ≫ (Over.pullback t).map A.act) ⊗ₘ
          𝟙 ((Over.pullback t).obj G.X)) ≫
          Functor.LaxMonoidal.μ (Over.pullback t) P G.X ≫
            (Over.pullback t).map A.act =
        (α_ ((Over.pullback t).obj P) ((Over.pullback t).obj G.X)
            ((Over.pullback t).obj G.X)).hom ≫
          (𝟙 _ ⊗ₘ (Functor.LaxMonoidal.μ (Over.pullback t) G.X G.X ≫
            (Over.pullback t).map μ[G.X])) ≫
            Functor.LaxMonoidal.μ (Over.pullback t) P G.X ≫
              (Over.pullback t).map A.act
    simp [MonoidalCategory.tensorHom_def, ← Functor.map_comp]
    have hA :
        A.act ▷ G.X ≫ A.act =
          (α_ P G.X G.X).hom ≫ (𝟙 P ⊗ₘ μ[G.X]) ≫ A.act := by
      simpa [MonoidalCategory.tensorHom_def] using A.mul_act
    rw [hA]
    simp [Functor.map_comp]

/-- A local trivialization of a right action after base change. -/
structure Chapter13TorsorLocalTrivialization {S T : Scheme.{u}}
    {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) (t : T ⟶ S) where
  iso : Chapter13EquivariantIso
    (chapter13BaseChangedRightAction A t)
    (chapter13RegularRightAction (chapter13BaseChangedGroup G t))

/-- A finite locally free sheaf, shared by the examples and associated bundles. -/
structure Chapter13FiniteLocallyFreeSheaf (S : Scheme.{u}) where
  sheaf : S.Modules
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteLocallyFree
      sheaf

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
