import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Section02ObjectsIsomorphismsAndCocycles

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v v' u'

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-! ## 4.3 Morphisms and full faithfulness -/

/-- Morphisms between singleton descent data, using Mathlib's canonical category. -/
abbrev Chapter04DescentMorphism
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p} :=
  D ⟶ D'

/-- The map on the object over `T` underlying a descent morphism. -/
def chapter04DescentMorphismMap
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p} (φ : Chapter04DescentMorphism F) :
    chapter04DescentObject F D ⟶ chapter04DescentObject F D' :=
  φ.hom PUnit.unit

theorem chapter04DescentMorphism_compatibility
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p} (φ : Chapter04DescentMorphism F) :
    (Chapter04PullbackFunctor F (chapter04P2 p)).map (chapter04DescentMorphismMap F φ) ≫
        (chapter04DescentIsomorphism F D').hom =
      (chapter04DescentIsomorphism F D).hom ≫
        (Chapter04PullbackFunctor F (chapter04P1 p)).map (chapter04DescentMorphismMap F φ) := by
  sorry

@[ext]
theorem chapter04DescentMorphism_ext
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p}
    {φ ψ : Chapter04DescentMorphism F}
    (h : chapter04DescentMorphismMap F φ = chapter04DescentMorphismMap F ψ) :
    φ = ψ := by
  sorry

@[simp]
theorem chapter04DescentMorphism_map_id
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    chapter04DescentMorphismMap F (𝟙 D) = 𝟙 (chapter04DescentObject F D) := by
  rfl

@[simp]
theorem chapter04DescentMorphism_map_comp
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D₁ D₂ D₃ : Chapter04SingleDescentData F p}
    (φ : D₁ ⟶ D₂) (ψ : D₂ ⟶ D₃) :
    chapter04DescentMorphismMap F (φ ≫ ψ) =
      chapter04DescentMorphismMap F φ ≫ chapter04DescentMorphismMap F ψ := by
  rfl

/-- The equalizer condition on a map over `T` for the canonical data. -/
def Chapter04CompatibleHom
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) (u : E ⟶ E') : Prop :=
  (Chapter04PullbackFunctor F (chapter04P2 p)).map u ≫
      (chapter04DescentIsomorphism F (chapter04CanonicalDescentDatum F p E')).hom =
    (chapter04DescentIsomorphism F (chapter04CanonicalDescentDatum F p E)).hom ≫
      (Chapter04PullbackFunctor F (chapter04P1 p)).map u

/-- The Hom-set equalizer encoded as a subtype. -/
def Chapter04CompatibleHomSet
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) :=
  {u : E ⟶ E' // Chapter04CompatibleHom F p E E' u}

/-- Full faithfulness identifies downstairs maps with compatible upstairs maps. -/
theorem chapter04CanonicalHomEquiv
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (hF : Chapter04DescentIsFullyFaithful F p)
    (E E' : Chapter04FiberObject F S) :
    (E ⟶ E') ≃ Chapter04CompatibleHomSet F p E E' := by
  sorry

theorem chapter04CanonicalMorphism_is_compatible
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) (u : E ⟶ E') :
    Chapter04CompatibleHom F p E E' u := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
