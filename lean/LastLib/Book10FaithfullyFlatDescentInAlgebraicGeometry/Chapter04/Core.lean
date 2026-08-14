import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Sites.Descent.DescentData

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v v' u'

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-- The single-map faithfully flat condition used before adding quasi-compactness. -/
def Chapter04FaithfullyFlatCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ Surjective p

/-- In this chapter a single cover is an fpqc morphism. -/
def Chapter04Cover {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Chapter04FaithfullyFlatCover p ∧ QuasiCompact p

theorem chapter04Cover_faithfullyFlat {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter04Cover p) : Chapter04FaithfullyFlatCover p :=
  hp.1

theorem chapter04Cover_flat {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter04Cover p) : Flat p :=
  hp.1.1

theorem chapter04Cover_surjective {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter04Cover p) : Surjective p :=
  hp.1.2

theorem chapter04Cover_quasiCompact {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter04Cover p) : QuasiCompact p :=
  hp.2

/-- The double overlap `T ×ₛ T` of a map `p : T ⟶ S`. -/
def chapter04PairProduct {S T : Scheme.{u}} (p : T ⟶ S) : Scheme.{u} :=
  pullback p p

/-- The first projection from the double overlap. -/
def chapter04P1 {S T : Scheme.{u}} (p : T ⟶ S) : chapter04PairProduct p ⟶ T :=
  pullback.fst p p

/-- The second projection from the double overlap. -/
def chapter04P2 {S T : Scheme.{u}} (p : T ⟶ S) : chapter04PairProduct p ⟶ T :=
  pullback.snd p p

/-- The iterated pullback `(T ×ₛ T) ×ₛ T`, used as the triple overlap. -/
def chapter04TripleProduct {S T : Scheme.{u}} (p : T ⟶ S) : Scheme.{u} :=
  pullback (chapter04P1 p ≫ p) p

/-- The projection of the triple overlap onto its first two factors. -/
def chapter04P12 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04TripleProduct p ⟶ chapter04PairProduct p :=
  pullback.fst (chapter04P1 p ≫ p) p

/-- The projection of the triple overlap onto its third factor. -/
def chapter04P3 {S T : Scheme.{u}} (p : T ⟶ S) : chapter04TripleProduct p ⟶ T :=
  pullback.snd (chapter04P1 p ≫ p) p

/-- The projection of the triple overlap onto its second and third factors. -/
def chapter04P23 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04TripleProduct p ⟶ chapter04PairProduct p :=
  pullback.lift (chapter04P12 p ≫ chapter04P2 p) (chapter04P3 p) (by
    rw [Category.assoc, ← pullback.condition_assoc]
    simp [chapter04P12, chapter04P3, Category.assoc])

/-- The projection of the triple overlap onto its first and third factors. -/
def chapter04P13 {S T : Scheme.{u}} (p : T ⟶ S) :
    chapter04TripleProduct p ⟶ chapter04PairProduct p :=
  pullback.lift (chapter04P12 p ≫ chapter04P1 p) (chapter04P3 p) (by
    simp [chapter04P12, chapter04P3, Category.assoc])

/-- The all-level Čech nerve supplied by Mathlib's simplicial construction. -/
noncomputable def chapter04CechNerve {S T : Scheme.{u}} (p : T ⟶ S) :
    SimplicialObject Scheme :=
  (Arrow.mk p).cechNerve

/-- The object of the Čech nerve in simplicial degree `n`. -/
abbrev Chapter04NerveLevel {S T : Scheme.{u}} (p : T ⟶ S) (n : ℕ) : Scheme :=
  (chapter04CechNerve p).obj (Opposite.op (SimplexCategory.mk n))

/-- The map on Čech-nerve levels induced by a simplex morphism. -/
def chapter04NerveMap {S T : Scheme.{u}} (p : T ⟶ S) {m n : ℕ}
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    Chapter04NerveLevel p n ⟶ Chapter04NerveLevel p m :=
  (chapter04CechNerve p).map α.op

/-- An object-valued pullback formalism, represented by a pseudofunctor to categories. -/
abbrev Chapter04FiberObject
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    (X : Scheme.{u}) :=
  F.obj (.mk (Opposite.op X))

/-- The pullback functor attached to a scheme morphism in the formalism `F`. -/
abbrev Chapter04PullbackFunctor
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {X Y : Scheme.{u}} (f : Y ⟶ X) : Chapter04FiberObject F X ⥤ Chapter04FiberObject F Y :=
  (F.map f.op.toLoc).toFunctor

/-- Mathlib's general descent-data object, specialized to a singleton cover. -/
abbrev Chapter04SingleDescentData
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S) :=
  F.DescentData (fun _ : PUnit => p)

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
