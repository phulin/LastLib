import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Section02QuotientsAndEquations

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/-- An affine scheme over `T` together with its overlap isomorphism over `T ×_S T`. -/
structure Chapter07AffineSchemeWithDescentData
    {T S : Scheme.{u}} (p : T ⟶ S) where
  X : Scheme.{u}
  map : X ⟶ T
  affine : IsAffineHom map
  overlapIso :
    pullback map (pullback.fst p p) ≅ pullback map (pullback.snd p p)
  overlap_over :
    overlapIso.hom ≫ pullback.snd map (pullback.snd p p) =
      pullback.snd map (pullback.fst p p)
  /- LOCAL_DEPENDENCY_GUESS: replace this named field with the exact triple-pullback cocycle
  equation from the earlier scheme-descent interface when that interface is available. -/
  cocycle : Prop

/-- The output of effective affine descent. -/
structure Chapter07AffineDescentResult
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter07AffineSchemeWithDescentData p) where
  Y : Scheme.{u}
  map : Y ⟶ S
  affine : IsAffineHom map
  comparison : pullback map p ≅ D.X
  comparison_over :
    comparison.hom ≫ D.map = pullback.snd map p

/-- A morphism of affine descent data, including the overlap compatibility condition. -/
structure Chapter07AffineCompatibleMorphism
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D E : Chapter07AffineSchemeWithDescentData p) where
  map : D.X ⟶ E.X
  over : map ≫ E.map = D.map
  compatible_on_overlap :
    pullback.map D.map (pullback.fst p p) E.map (pullback.fst p p)
        map (𝟙 _) (𝟙 _) (by simpa using over.symm) (by simp) ≫ E.overlapIso.hom =
      D.overlapIso.hom ≫
        pullback.map D.map (pullback.snd p p) E.map (pullback.snd p p)
          map (𝟙 _) (𝟙 _) (by simpa using over.symm) (by simp)

/-- A descended morphism together with its comparison compatibility. -/
structure Chapter07AffineDescentMorphism
    {T S : Scheme.{u}} {p : T ⟶ S}
    {D E : Chapter07AffineSchemeWithDescentData p}
    (RD : Chapter07AffineDescentResult D) (RE : Chapter07AffineDescentResult E)
    (u : Chapter07AffineCompatibleMorphism D E) where
  map : RD.Y ⟶ RE.Y
  over : map ≫ RE.map = RD.map
  comparison_commutes :
    RD.comparison.hom ≫ u.map =
      pullback.map RD.map p RE.map p map (𝟙 _) (𝟙 _) (by simpa using over.symm) (by simp) ≫
        RE.comparison.hom

theorem chapter07_affine_descent_effective
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p) :
    Nonempty (Chapter07AffineDescentResult D) := by
  sorry

theorem chapter07_affine_descent_affineness
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R : Chapter07AffineDescentResult D) : IsAffineHom R.map :=
  R.affine

theorem chapter07_affine_morphism_descends
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D E : Chapter07AffineSchemeWithDescentData p)
    (RD : Chapter07AffineDescentResult D)
    (RE : Chapter07AffineDescentResult E)
    (u : Chapter07AffineCompatibleMorphism D E) :
    Nonempty (Chapter07AffineDescentMorphism RD RE u) := by
  sorry

theorem chapter07_affine_morphism_descends_uniquely
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D E : Chapter07AffineSchemeWithDescentData p)
    (RD : Chapter07AffineDescentResult D)
    (RE : Chapter07AffineDescentResult E)
    (u : Chapter07AffineCompatibleMorphism D E)
    (f g : Chapter07AffineDescentMorphism RD RE u) : f.map = g.map := by
  sorry

/-- The affine theorem over `Spec A`/`Spec B`, expressed through the affine algebra comparison.

The tensor-product algebra on the right is the canonical affine pullback. -/
theorem chapter07_affine_descent_on_affine_base
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (D : Chapter07AlgebraDescentData A B C) :
    Nonempty (Chapter07AlgebraDescentResult A B C) := by
  exact chapter07_algebra_structure_descends D hff

theorem chapter07_affineness_descends_under_fpqc
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ S), IsAffineHom f := by
  obtain ⟨R⟩ := chapter07_affine_descent_effective hp D
  exact ⟨R.Y, R.map, R.affine⟩

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
