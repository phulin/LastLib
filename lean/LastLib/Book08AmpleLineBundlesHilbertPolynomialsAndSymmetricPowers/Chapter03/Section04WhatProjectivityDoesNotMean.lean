import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Section02ElementaryPermanenceProperties
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Section03SeparatednessFiniteTypeAndProperness

/-!
## 3.4 What projectivity does not mean

The statements in this section make the relative nature of projectivity and the limits of
fiberwise tests explicit.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

variable {X S T : Scheme.{u}}

/-- Projectivity over a projective base composes to projectivity over the smaller base. -/
theorem chapter03_projective_over_projective_base (f : X ⟶ S) (g : S ⟶ T)
    (hf : chapter03Projective f) (hg : chapter03Projective g) :
    chapter03Projective (f ≫ g) :=
  chapter03_projective_comp f g hf hg

/-- The affine line over a field, viewed as relative affine space. -/
def chapter03AffineLine (k : Type u) [Field k] : Scheme.{u} :=
  chapter03AffineSpace (Spec (CommRingCat.of k)) 1

/-- The structure morphism of the affine line over a field. -/
def chapter03AffineLineProjection (k : Type u) [Field k] :
    chapter03AffineLine k ⟶ Spec (CommRingCat.of k) :=
  chapter03AffineSpaceProjection (Spec (CommRingCat.of k)) 1

/-- The affine line over a field is not proper over that field. -/
theorem chapter03_affineLine_not_proper (k : Type u) [Field k] :
    ¬ IsProper (chapter03AffineLineProjection k) := by
  intro h
  have hfinite : IsFinite (chapter03AffineLineProjection k) := by
    apply (IsFinite.iff_isProper_and_isAffineHom).2
    exact ⟨h, by
      dsimp [chapter03AffineLineProjection, chapter03AffineLine, chapter03AffineSpace]
      have : IsAffine (AlgebraicGeometry.AffineSpace
          (ULift.{u} (Fin 1)) (Spec (CommRingCat.of k))) := by infer_instance
      have : IsAffine (Spec (CommRingCat.of k)) := by infer_instance
      change IsAffineHom
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1))
          (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
      exact isAffineHom_of_isAffine _⟩
  let : IsFinite (chapter03AffineLineProjection k) := hfinite
  let : IsFinite (chapter03AffineSpaceProjection
      (Spec (CommRingCat.of k)) 1) := hfinite
  have hi : IsIntegralHom (chapter03AffineSpaceProjection
      (Spec (CommRingCat.of k)) 1) := by
    infer_instance
  apply (AffineSpace.not_isIntegralHom
    (n := ULift.{u} (Fin 1)) (S := Spec (CommRingCat.of k)))
  change IsIntegralHom (chapter03AffineSpaceProjection
    (Spec (CommRingCat.of k)) 1)
  exact hi

/-- The affine line over a field is not projective over that field. -/
theorem chapter03_affineLine_not_projective (k : Type u) [Field k] :
    ¬ chapter03Projective (chapter03AffineLineProjection k) := by
  intro h
  exact chapter03_affineLine_not_proper k (chapter03_projective_isProper _ h)

/-- The affine line is nevertheless quasi-projective as the standard projective-space open. -/
theorem chapter03_affineLine_quasiProjective (k : Type u) [Field k] :
    chapter03QuasiProjective (chapter03AffineLineProjection k) := by
  exact chapter03_affineSpace_quasiProjective (Spec (CommRingCat.of k)) 1

/-- A projective morphism over a projective base need not be projective over a smaller base. -/
def chapter03ProjectivityCanDependOnBase : Prop :=
  ∃ (X S T : Scheme.{u}) (f : X ⟶ S) (g : S ⟶ T),
    chapter03Projective f ∧ ¬ chapter03Projective (f ≫ g) ∧ ¬ chapter03Projective g

theorem chapter03_projectivity_can_depend_on_base :
    chapter03ProjectivityCanDependOnBase := by
  sorry

/-- Fiberwise projectivity means projectivity after passage to every residue-field fiber. -/
def chapter03FiberwiseProjective (f : X ⟶ S) : Prop :=
  ∀ s : S, chapter03Projective (f.fiberToSpecResidueField s)

/-- A projective morphism is fiberwise projective. -/
theorem chapter03_projective_fiberwiseProjective (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03FiberwiseProjective f := by
  intro s
  exact chapter03_projective_baseChange f (S.fromSpecResidueField s) hf

/-- The source's fiberwise-projectivity warning, with all data quantified explicitly. -/
def chapter03FiberwiseProjectivityIsInsufficient : Prop :=
  ∃ (X S : Scheme.{u}) (f : X ⟶ S),
    chapter03FiberwiseProjective f ∧ ¬ chapter03Projective f

theorem chapter03_fiberwiseProjectivity_is_insufficient :
    chapter03FiberwiseProjectivityIsInsufficient := by
  sorry

/-- Properness alone does not force projectivity in general. -/
def chapter03ProperNeedNotBeProjective : Prop :=
  ∃ (X S : Scheme.{u}) (f : X ⟶ S),
    IsProper f ∧ ¬ chapter03Projective f

theorem chapter03_proper_need_not_be_projective :
    chapter03ProperNeedNotBeProjective := by
  sorry

/-- A proper family can have fiberwise ample line bundle data without relative ampleness. -/
def chapter03ProperFiberwiseAmpleButNotRelativelyAmple : Prop :=
  ∃ (X S : Scheme.{u}) (f : X ⟶ S) (L : Chapter03LineBundle X),
    IsProper f ∧ chapter03FiberwiseAmple f L ∧ ¬ chapter03RelativelyAmple f L

theorem chapter03_proper_fiberwiseAmple_but_not_relativelyAmple :
    chapter03ProperFiberwiseAmpleButNotRelativelyAmple := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
