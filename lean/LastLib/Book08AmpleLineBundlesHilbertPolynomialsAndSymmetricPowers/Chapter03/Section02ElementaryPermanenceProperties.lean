import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Section01DefinitionsThatSurviveChangeOfBase

/-!
## 3.2 Elementary permanence properties

This section records the functorial operations on the two predicates and the Segre interface used
by the product and composition statements.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01

noncomputable section

universe u

variable {X Y Z S T : Scheme.{u}}

/-- The product of two morphisms over the same base. -/
def chapter03ProductOver (f : X ⟶ S) (g : Y ⟶ S) :
    Limits.pullback f g ⟶ S :=
  Limits.pullback.fst f g ≫ f

/-- Either projection computes the structure map of the fiber product. -/
theorem chapter03_productOver_eq_snd (f : X ⟶ S) (g : Y ⟶ S) :
    chapter03ProductOver f g = Limits.pullback.snd f g ≫ g := by
  sorry

/-- The projective bundle construction is compatible with pullback of its base. -/
theorem chapter03_relativeProjectiveBundle_baseChange
    (g : T ⟶ S) (E : S.Modules) (hE : chapter03FiniteLocallyFree E) :
    Nonempty (Chapter03RelativeProjectiveBundle T ((Scheme.Modules.pullback g).obj E)) := by
  sorry

/-- The base-change comparison for the canonical relative projective-bundle interface. -/
theorem chapter03_relativeProjectiveBundle_baseChange_compatibility
    (g : T ⟶ S) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ∃ (Q : Chapter03RelativeProjectiveBundle T ((Scheme.Modules.pullback g).obj E))
      (e : Limits.pullback P.projection g ⟶ Q.carrier),
      IsIso e ∧ e ≫ Q.projection = Limits.pullback.snd P.projection g := by
  sorry

/-- Projectivity is stable under arbitrary base change. -/
theorem chapter03_projective_baseChange (f : X ⟶ S) (g : T ⟶ S)
    (hf : chapter03Projective f) :
    chapter03Projective (Limits.pullback.fst f g) := by
  sorry

/-- Quasi-projectivity is stable under arbitrary base change. -/
theorem chapter03_quasiProjective_baseChange (f : X ⟶ S) (g : T ⟶ S)
    (hf : chapter03QuasiProjective f) :
    chapter03QuasiProjective (Limits.pullback.fst f g) := by
  sorry

/-- Projective morphisms are quasi-projective. -/
theorem chapter03_projective_quasiProjective (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03QuasiProjective f := by
  sorry

/-- Products of projective morphisms over a common base are projective. -/
theorem chapter03_projective_product (f : X ⟶ S) (g : Y ⟶ S)
    (hf : chapter03Projective f) (hg : chapter03Projective g) :
    chapter03Projective (chapter03ProductOver f g) := by
  sorry

/-- Products of quasi-projective morphisms over a common base are quasi-projective. -/
theorem chapter03_quasiProjective_product (f : X ⟶ S) (g : Y ⟶ S)
    (hf : chapter03QuasiProjective f) (hg : chapter03QuasiProjective g) :
    chapter03QuasiProjective (chapter03ProductOver f g) := by
  sorry

/-- A finite locally free model for the tensor product of two sheaves.

The preceding chapter supplies the book-facing sheaf tensor operation.  The explicit isomorphism
keeps this interface tied to that operation instead of recording an unconstrained proposition. -/
structure Chapter03TensorProductModule (S : Scheme.{u})
    (E F : S.Modules) where
  module : S.Modules
  finiteLocallyFree : chapter03FiniteLocallyFree module
  tensorProductIso : module ≅ chapter01SheafTensor E F

/-- The data of the relative Segre immersion. -/
structure Chapter03SegreData {S : Scheme.{u}} {E F : S.Modules}
    (P : Chapter03RelativeProjectiveBundle S E)
    (Q : Chapter03RelativeProjectiveBundle S F)
    (R : Chapter03TensorProductModule S E F)
    (B : Chapter03RelativeProjectiveBundle S R.module) where
  embedding : Limits.pullback P.projection Q.projection ⟶ B.carrier
  isClosedImmersion : IsClosedImmersion embedding
  overBase : embedding ≫ B.projection = chapter03ProductOver P.projection Q.projection

/-- The Segre map is a closed immersion into the projective bundle of the tensor product. -/
theorem chapter03_segre_embedding (S : Scheme.{u}) (E F : S.Modules)
    (hE : chapter03FiniteLocallyFree E) (hF : chapter03FiniteLocallyFree F)
    (P : Chapter03RelativeProjectiveBundle S E)
    (Q : Chapter03RelativeProjectiveBundle S F) :
    ∃ (R : Chapter03TensorProductModule S E F)
      (B : Chapter03RelativeProjectiveBundle S R.module),
      Nonempty (Chapter03SegreData P Q R B) := by
  sorry

/-- Composition of projective morphisms is projective. -/
theorem chapter03_projective_comp (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : chapter03Projective f) (hg : chapter03Projective g) :
    chapter03Projective (f ≫ g) := by
  sorry

/-- Composition of quasi-projective morphisms is quasi-projective. -/
theorem chapter03_quasiProjective_comp (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : chapter03QuasiProjective f) (hg : chapter03QuasiProjective g) :
    chapter03QuasiProjective (f ≫ g) := by
  sorry

/-- A projective morphism is locally projective on the target. -/
theorem chapter03_locallyProjective_of_projective (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03LocallyProjective f := by
  sorry

/-- A quasi-projective morphism is locally quasi-projective on the target. -/
theorem chapter03_locallyQuasiProjective_of_quasiProjective (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) : chapter03LocallyQuasiProjective f := by
  sorry

/-- On a quasi-compact base, local projectivity globalizes after enlarging the ambient bundle. -/
theorem chapter03_projective_iff_locallyProjective [CompactSpace S] (f : X ⟶ S) :
    chapter03Projective f ↔ chapter03LocallyProjective f := by
  sorry

/-- On a quasi-compact base, local quasi-projectivity globalizes after enlarging the ambient
bundle. -/
theorem chapter03_quasiProjective_iff_locallyQuasiProjective [CompactSpace S] (f : X ⟶ S) :
    chapter03QuasiProjective f ↔ chapter03LocallyQuasiProjective f := by
  sorry

/-- Local embeddings into standard projective spaces over the members of a target cover. -/
def chapter03LocallyInStandardProjectiveSpace (f : X ⟶ S) : Prop :=
    ∃ (r : ℕ) (𝒰 : S.OpenCover.{u}),
    ∀ i : 𝒰.I₀,
      ∃ j : ((f ⁻¹ᵁ (𝒰.f i).opensRange).toScheme ⟶
          chapter03ProjectiveSpace (𝒰.f i).opensRange.toScheme r),
        IsClosedImmersion j ∧
          j ≫ chapter03ProjectiveSpaceProjection (𝒰.f i).opensRange.toScheme r =
            f ∣_ (𝒰.f i).opensRange

/-- Over a quasi-compact base, finite locally free bundles may be replaced locally by some
standard projective space. -/
theorem chapter03_projective_iff_locallyStandardProjectiveSpace [CompactSpace S]
    (f : X ⟶ S) :
    chapter03Projective f ↔ chapter03LocallyInStandardProjectiveSpace f := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
