import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Section01DescentOfAlgebraStructures

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

noncomputable section

def chapter07PairProduct {T S : Scheme.{u}} (p : T ⟶ S) : Scheme.{u} :=
  pullback p p

def chapter07P1 {T S : Scheme.{u}} (p : T ⟶ S) : chapter07PairProduct p ⟶ T :=
  pullback.fst p p

def chapter07P2 {T S : Scheme.{u}} (p : T ⟶ S) : chapter07PairProduct p ⟶ T :=
  pullback.snd p p

def chapter07TripleProduct {T S : Scheme.{u}} (p : T ⟶ S) : Scheme.{u} :=
  pullback (chapter07P1 p ≫ p) p

def chapter07P12 {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07TripleProduct p ⟶ chapter07PairProduct p :=
  pullback.fst (chapter07P1 p ≫ p) p

def chapter07P3 {T S : Scheme.{u}} (p : T ⟶ S) : chapter07TripleProduct p ⟶ T :=
  pullback.snd (chapter07P1 p ≫ p) p

def chapter07P23 {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07TripleProduct p ⟶ chapter07PairProduct p :=
  pullback.lift (chapter07P12 p ≫ chapter07P2 p) (chapter07P3 p)
    (by sorry)

def chapter07P13 {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07TripleProduct p ⟶ chapter07PairProduct p :=
  pullback.lift (chapter07P12 p ≫ chapter07P1 p) (chapter07P3 p)
    (by sorry)

theorem chapter07P23_fst {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07P23 p ≫ chapter07P1 p = chapter07P12 p ≫ chapter07P2 p := by sorry

theorem chapter07P23_snd {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07P23 p ≫ chapter07P2 p = chapter07P3 p := by sorry

theorem chapter07P13_fst {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07P13 p ≫ chapter07P1 p = chapter07P12 p ≫ chapter07P1 p := by sorry

theorem chapter07P13_snd {T S : Scheme.{u}} (p : T ⟶ S) :
    chapter07P13 p ≫ chapter07P2 p = chapter07P3 p := by sorry

/- The following transport is the scheme-level pullback of the overlap isomorphism along a
triple-overlap map.  The explicit construction keeps the cocycle tied to `overlapIso` rather than
allowing an unrelated proposition to stand in for it. -/
noncomputable def chapter07AffineTransport
    {T S X : Scheme.{u}} (p : T ⟶ S) (map : X ⟶ T)
    (overlapIso :
      pullback map (pullback.fst p p) ≅ pullback map (pullback.snd p p))
    (overlap_over :
      overlapIso.hom ≫ pullback.snd map (pullback.snd p p) =
        pullback.snd map (pullback.fst p p))
    (h : chapter07TripleProduct p ⟶ chapter07PairProduct p) :
    pullback map (h ≫ chapter07P1 p) ⟶ pullback map (h ≫ chapter07P2 p) := by
  let sourceToOverlap :
      pullback map (h ≫ chapter07P1 p) ⟶ pullback map (chapter07P1 p) :=
    pullback.map map (h ≫ chapter07P1 p) map (chapter07P1 p)
      (𝟙 _) h (𝟙 _) (by simp) (by simp)
  let sourceToBaseChanged :
    pullback map (h ≫ chapter07P1 p) ⟶
        pullback (pullback.snd map (chapter07P1 p)) h :=
    pullback.lift sourceToOverlap (pullback.snd map (h ≫ chapter07P1 p)) (by sorry)
  let baseChangedOverlap :
      pullback (pullback.snd map (chapter07P1 p)) h ⟶
        pullback (pullback.snd map (chapter07P2 p)) h :=
    pullback.map (pullback.snd map (chapter07P1 p)) h
      (pullback.snd map (chapter07P2 p)) h
      overlapIso.hom (𝟙 _) (𝟙 _) overlap_over.symm (by simp)
  let targetFromBaseChanged :
      pullback (pullback.snd map (chapter07P2 p)) h ⟶
        pullback map (h ≫ chapter07P2 p) :=
    pullback.lift
      (pullback.fst (pullback.snd map (chapter07P2 p)) h ≫
        pullback.fst map (chapter07P2 p))
      (pullback.snd (pullback.snd map (chapter07P2 p)) h) (by sorry)
  exact sourceToBaseChanged ≫ baseChangedOverlap ≫ targetFromBaseChanged

/- The cocycle is the equality of the two transports around the triple overlap, with the
canonical equalities of the middle and target pullbacks made explicit. -/
def Chapter07AffineDescentCocycle
    {T S X : Scheme.{u}} (p : T ⟶ S) (map : X ⟶ T)
    (overlapIso :
      pullback map (pullback.fst p p) ≅ pullback map (pullback.snd p p))
    (overlap_over :
      overlapIso.hom ≫ pullback.snd map (pullback.snd p p) =
        pullback.snd map (pullback.fst p p)) : Prop :=
  let t12 := chapter07AffineTransport p map overlapIso overlap_over (chapter07P12 p)
  let t23 := chapter07AffineTransport p map overlapIso overlap_over (chapter07P23 p)
  let t13 := chapter07AffineTransport p map overlapIso overlap_over (chapter07P13 p)
  let hsource :
      pullback map (chapter07P12 p ≫ chapter07P1 p) =
        pullback map (chapter07P13 p ≫ chapter07P1 p) :=
    congrArg (fun f : chapter07TripleProduct p ⟶ T => pullback map f)
      (chapter07P13_fst p).symm
  let hmiddle :
      pullback map (chapter07P12 p ≫ chapter07P2 p) =
        pullback map (chapter07P23 p ≫ chapter07P1 p) :=
    congrArg (fun f : chapter07TripleProduct p ⟶ T => pullback map f)
      (chapter07P23_fst p).symm
  let htarget :
      pullback map (chapter07P23 p ≫ chapter07P2 p) =
        pullback map (chapter07P13 p ≫ chapter07P2 p) :=
    congrArg (fun f : chapter07TripleProduct p ⟶ T => pullback map f)
      ((chapter07P23_snd p).trans (chapter07P13_snd p).symm)
  t12 ≫ eqToHom hmiddle ≫ t23 ≫ eqToHom htarget =
    eqToHom hsource ≫ t13

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
  cocycle : Chapter07AffineDescentCocycle p map overlapIso overlap_over

/-- Compatibility of a comparison with the canonical overlap datum on a pullback.

The two equations before `commutes` characterize the canonical overlap isomorphism: it is
over the pair overlap and preserves the underlying point of `Y`.  The final equation says
that the comparison is an isomorphism of descent data, rather than merely an isomorphism of
schemes over `T`. -/
def Chapter07AffineComparisonCompatible
    {T S : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter07AffineSchemeWithDescentData p)
    {Y : Scheme.{u}} (map : Y ⟶ S)
    (comparison : pullback map p ≅ D.X)
    (comparison_over : comparison.hom ≫ D.map = pullback.snd map p) : Prop :=
  ∃ overlap :
      pullback (pullback.snd map p) (chapter07P1 p) ≅
        pullback (pullback.snd map p) (chapter07P2 p),
    overlap.hom ≫ pullback.snd (pullback.snd map p) (chapter07P2 p) =
      pullback.snd (pullback.snd map p) (chapter07P1 p) ∧
    overlap.hom ≫ pullback.fst (pullback.snd map p) (chapter07P2 p) ≫
          pullback.fst map p =
      pullback.fst (pullback.snd map p) (chapter07P1 p) ≫ pullback.fst map p ∧
    pullback.map (pullback.snd map p) (chapter07P1 p) D.map (chapter07P1 p)
        comparison.hom (𝟙 _) (𝟙 _) (by simpa using comparison_over.symm) (by simp) ≫
        D.overlapIso.hom =
      overlap.hom ≫
        pullback.map (pullback.snd map p) (chapter07P2 p) D.map (chapter07P2 p)
          comparison.hom (𝟙 _) (𝟙 _) (by simpa using comparison_over.symm) (by simp)

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
  comparison_compatible :
    Chapter07AffineComparisonCompatible D map comparison comparison_over

/-- Two affine descents of the same datum, including the comparison which makes the
isomorphism an isomorphism of descended objects rather than an abstract scheme isomorphism. -/
structure Chapter07AffineDescentResultEquivalence
    {T S : Scheme.{u}} {p : T ⟶ S}
    {D : Chapter07AffineSchemeWithDescentData p}
    (R R' : Chapter07AffineDescentResult D) where
  equivalence : R.Y ≅ R'.Y
  over : equivalence.hom ≫ R'.map = R.map
  comparison_commutes :
    R.comparison.hom =
      pullback.map R.map p R'.map p equivalence.hom (𝟙 _) (𝟙 _)
        (by simpa using over.symm) (by simp) ≫ R'.comparison.hom

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

/-- Affine morphisms descend along quasi-compact, faithfully flat, surjective morphisms. -/
instance chapter07_isAffineHom_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong
      (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  sorry

/-- Affineness of an open descends through a finite faithfully flat morphism. -/
theorem chapter07_affine_of_finite_faithfullyFlat_preimage_affine
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hqfinite : IsFinite q)
    (hqff : Flat q ∧ Surjective q) (U : X.Opens)
    (hpreimage : IsAffineOpen (q ⁻¹ᵁ U)) : IsAffineOpen U := by
  sorry

theorem chapter07_affine_descent_affineness
    {T S : Scheme.{u}} {p : T ⟶ S}
    (_hp : Chapter07FpqcMorphism p)
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
    (f g : Chapter07AffineDescentMorphism RD RE u) : f.map = g.map := by sorry

theorem chapter07_affine_descent_result_unique_up_to_equivalence
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R R' : Chapter07AffineDescentResult D) :
    Nonempty (Chapter07AffineDescentResultEquivalence R R') := by
  sorry

theorem chapter07_affine_descent_result_equivalence_unique
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p)
    (R R' : Chapter07AffineDescentResult D)
    (e e' : Chapter07AffineDescentResultEquivalence R R') :
    e = e' := by sorry

/-- The affine theorem over `Spec A`/`Spec B`, expressed through the affine algebra comparison.

The tensor-product algebra on the right is the canonical affine pullback. -/
theorem chapter07_affine_descent_on_affine_base
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (D : Chapter07AlgebraDescentData A B C) :
    Nonempty (Chapter07AlgebraDescentResult D) := by
  exact chapter07_algebra_structure_descends D hff

theorem chapter07_affineness_descends_under_fpqc
    {T S : Scheme.{u}} {p : T ⟶ S}
    (hp : Chapter07FpqcMorphism p)
    (D : Chapter07AffineSchemeWithDescentData p) :
    Nonempty (Chapter07AffineDescentResult D) := by
  exact chapter07_affine_descent_effective hp D

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
