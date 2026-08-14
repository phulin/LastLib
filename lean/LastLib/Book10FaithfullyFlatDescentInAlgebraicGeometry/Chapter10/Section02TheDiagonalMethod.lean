import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies

/-!
## 10.2 The diagonal method

This file records the diagonal characterizations and the descent bridges for closed immersions,
open immersions, and isomorphisms.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/-- The diagonal of a scheme morphism. -/
abbrev chapter10Diagonal {X S : Scheme.{u}} (f : X ⟶ S) :
    X ⟶ pullback f f :=
  pullback.diagonal f

/-- Separatedness is the closed-immersion condition on the diagonal. -/
theorem chapter10_separated_iff_diagonal_closedImmersion {X S : Scheme.{u}} (f : X ⟶ S) :
    IsSeparated f ↔ IsClosedImmersion (chapter10Diagonal f) := by
  sorry

/-- Quasi-separatedness is exactly quasi-compactness of the diagonal. -/
theorem chapter10_quasiSeparated_iff_diagonal_quasiCompact {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔ QuasiCompact (chapter10Diagonal f) := by
  sorry

/-- The source's unramified condition is locally finite type plus open diagonal. -/
theorem chapter10_unramified_iff_diagonal_openImmersion {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10Unramified f ↔
      LocallyOfFiniteType f ∧ IsOpenImmersion (chapter10Diagonal f) := by
  rfl

/-- Comparison with Mathlib's formally-unramified condition. -/
theorem chapter10_unramified_iff_formallyUnramified {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10Unramified f ↔ LocallyOfFiniteType f ∧ FormallyUnramified f := by
  sorry

/-- A morphism is a monomorphism exactly when its diagonal is an isomorphism. -/
theorem chapter10_monomorphism_iff_diagonal_isIso {X S : Scheme.{u}} (f : X ⟶ S) :
    Mono f ↔ IsIso (chapter10Diagonal f) := by
  sorry

/-- The canonical map from the diagonal object after base change to the original diagonal object.
It is the pullback comparison induced by the two projections to `X` and by `p : T ⟶ S`. -/
def chapter10DiagonalBaseChangeTargetMap {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) :
    pullback (chapter10BaseChangeMorphism f p) (chapter10BaseChangeMorphism f p) ⟶
      pullback f f :=
  pullback.map (chapter10BaseChangeMorphism f p) (chapter10BaseChangeMorphism f p) f f
    (chapter10BaseChangeToSource f p) (chapter10BaseChangeToSource f p) p
    (chapter10BaseChange_condition f p).symm (chapter10BaseChange_condition f p).symm

/-- Diagonals commute with arbitrary base change, up to the canonical pullback comparison. -/
theorem chapter10_diagonal_commutes_with_baseChange {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) :
    Nonempty (Arrow.mk (chapter10Diagonal (chapter10BaseChangeMorphism f p)) ≅
      Arrow.mk (pullback.snd (chapter10Diagonal f)
        (chapter10DiagonalBaseChangeTargetMap f p))) := by
  sorry

/-- Any diagonal property stable under base change remains stable for the base-changed morphism. -/
theorem chapter10_diagonal_property_baseChange
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hf : P (chapter10Diagonal f)) : P (chapter10Diagonal (chapter10BaseChangeMorphism f p)) := by
  sorry

/-- Separatedness descends from an fpqc base change through the closed diagonal. -/
theorem chapter10_separated_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsSeparated (chapter10BaseChangeMorphism f p)) :
    IsSeparated f := by
  sorry

/-- Quasi-separatedness descends from an fpqc base change through the quasi-compact diagonal. -/
theorem chapter10_quasiSeparated_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : QuasiSeparated (chapter10BaseChangeMorphism f p)) :
    QuasiSeparated f := by
  sorry

/-- Monomorphisms descend from an fpqc base change through the diagonal isomorphism. -/
theorem chapter10_monomorphism_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : Mono (chapter10BaseChangeMorphism f p)) :
    Mono f := by
  sorry

/-- Smooth morphisms carry the local finite-presentation hypothesis used by the fiber criterion. -/
theorem chapter10_smooth_has_local_finite_presentation {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Smooth f) : LocallyOfFinitePresentation f := by
  sorry

/-- Étale morphisms carry the local finite-presentation hypothesis. -/
theorem chapter10_etale_has_local_finite_presentation {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Etale f) : LocallyOfFinitePresentation f := by
  sorry

/-- A closed immersion descends from its fpqc pullback. -/
theorem chapter10_closedImmersion_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsClosedImmersion (chapter10BaseChangeMorphism f p)) :
    IsClosedImmersion f := by
  sorry

/-- An isomorphism descends from its fpqc pullback. -/
theorem chapter10_isomorphism_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsIso (chapter10BaseChangeMorphism f p)) : IsIso f := by
  sorry

/-- A flat, locally finitely presented monomorphism is an open immersion. -/
theorem chapter10_openImmersion_of_flat_of_local_finite_presentation_of_mono
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) (hmono : Mono f) :
    IsOpenImmersion f := by
  sorry

/-- Open immersions descend from compatible fpqc-local open data. -/
theorem chapter10_openImmersion_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsOpenImmersion (chapter10BaseChangeMorphism f p)) :
    IsOpenImmersion f := by
  sorry

/-- The image argument for the open-immersion descent theorem: flat locally finitely presented maps
are open, so a descended monomorphism identifies its source with an open image. -/
theorem chapter10_openImmersion_image_argument {X S : Scheme.{u}} (f : X ⟶ S)
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) (hmono : Mono f) :
    IsOpen (Set.range f.base) ∧ IsOpenImmersion f := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
