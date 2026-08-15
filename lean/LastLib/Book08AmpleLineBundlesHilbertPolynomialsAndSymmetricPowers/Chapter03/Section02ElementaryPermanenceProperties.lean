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
  exact Limits.pullback.condition

/-- The projective bundle construction is compatible with pullback of its base. -/
theorem chapter03_relativeProjectiveBundle_baseChange
    (g : T ⟶ S) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E) :
    Nonempty (Chapter03RelativeProjectiveBundle T ((Scheme.Modules.pullback g).obj E)) := by
  let M : Chapter02QuasiCoherentModule S :=
    chapter03QuasiCoherentModule S E _hE
  have hM : Chapter02FiniteLocallyFreeModule M := _hE
  let MT : Chapter02QuasiCoherentModule T :=
    chapter02PullbackQuasiCoherentModule g M
  have hMT : Chapter02FiniteLocallyFreeModule MT :=
    chapter02_pullback_preserves_finite_locally_free_module g M hM
  obtain ⟨Q⟩ := chapter02_finite_relative_projective_bundle_exists T MT hMT
  exact ⟨{ module := MT, module_carrier := rfl,
    finiteLocallyFree := hMT, canonical := Q }⟩

/-- The base-change comparison for the canonical relative projective-bundle interface. -/
theorem chapter03_relativeProjectiveBundle_baseChange_compatibility
    (g : T ⟶ S) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ∃ (Q : Chapter03RelativeProjectiveBundle T ((Scheme.Modules.pullback g).obj E))
      (e : Limits.pullback P.projection g ⟶ Q.carrier),
      IsIso e ∧ e ≫ Q.projection = Limits.pullback.snd P.projection g := by
  subst E
  have hP : Chapter02FiniteLocallyFreeModule P.module := P.finiteLocallyFree
  obtain ⟨Q, e, he, hbase⟩ :=
    chapter02_relative_projective_bundle_base_change_exists
      g P.module hP P.canonical
  have hQ : Chapter02FiniteLocallyFreeModule
      (chapter02PullbackQuasiCoherentModule g P.module) :=
    chapter02_pullback_preserves_finite_locally_free_module g P.module hP
  let Q₃ : Chapter03RelativeProjectiveBundle T
      ((Scheme.Modules.pullback g).obj P.module.carrier) :=
    { module := chapter02PullbackQuasiCoherentModule g P.module
      module_carrier := rfl
      finiteLocallyFree := hQ
      canonical := Q }
  exact ⟨Q₃, e, he, hbase⟩

/-- Projectivity is stable under arbitrary base change. -/
theorem chapter03_projective_baseChange (f : X ⟶ S) (g : T ⟶ S)
    (hf : chapter03Projective f) :
    chapter03Projective (Limits.pullback.snd f g) := by
  obtain ⟨P⟩ := hf
  let P₃ : Chapter03RelativeProjectiveBundle S P.module.carrier :=
    { module := P.module
      module_carrier := rfl
      finiteLocallyFree := P.ambient.finiteLocallyFree
      canonical := P.ambient }
  obtain ⟨Q, e, he, hebase⟩ :=
    chapter03_relativeProjectiveBundle_baseChange_compatibility
      g P.module.carrier P₃.finiteLocallyFree P₃
  let u : Limits.pullback f g ⟶ Limits.pullback P.ambient.projection g :=
    Limits.pullback.lift
      (Limits.pullback.fst f g ≫ P.embedding)
      (Limits.pullback.snd f g)
      (by
        rw [Category.assoc, P.overBase]
        exact Limits.pullback.condition)
  have hu : IsClosedImmersion u := by
    let h₁ : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g f := (IsPullback.of_hasPullback f g).flip
    let h₂ : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection g).flip
    have h₁' : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g (P.embedding ≫ P.ambient.projection) := by
      simpa [P.overBase] using h₁
    have hvcond : Limits.pullback.snd f g ≫ g =
        (Limits.pullback.fst f g ≫ P.embedding) ≫ P.ambient.projection := by
        rw [Category.assoc, P.overBase]
        exact Limits.pullback.condition.symm
    let v := h₂.lift (Limits.pullback.snd f g)
      (Limits.pullback.fst f g ≫ P.embedding) hvcond
    have huv : u = v := by
      ext
      · dsimp [v]
        rw [h₂.lift_snd]
        exact Limits.pullback.lift_fst _ _ _
      · dsimp [v]
        rw [h₂.lift_fst]
        exact Limits.pullback.lift_snd _ _ _
    rw [huv]
    have hpb : IsPullback v (Limits.pullback.fst f g)
        (Limits.pullback.fst P.ambient.projection g) P.embedding := by
      simpa [v] using (IsPullback.of_right' h₁' h₂)
    exact MorphismProperty.of_isPullback hpb.flip P.isClosedImmersion
  let : IsClosedImmersion u := hu
  let : IsIso e := he
  refine ⟨{
    module := Q.module
    ambient := Q.canonical
    embedding := u ≫ e
    isClosedImmersion := by infer_instance
    overBase := ?_ }⟩
  rw [Category.assoc, hebase]
  change u ≫ Limits.pullback.snd P.ambient.projection g = Limits.pullback.snd f g
  dsimp [u]
  apply Limits.pullback.lift_snd

/-- Quasi-projectivity is stable under arbitrary base change. -/
theorem chapter03_quasiProjective_baseChange (f : X ⟶ S) (g : T ⟶ S)
    (hf : chapter03QuasiProjective f) :
    chapter03QuasiProjective (Limits.pullback.snd f g) := by
  obtain ⟨P⟩ := hf
  let P₃ : Chapter03RelativeProjectiveBundle S P.module.carrier :=
    { module := P.module
      module_carrier := rfl
      finiteLocallyFree := P.ambient.finiteLocallyFree
      canonical := P.ambient }
  obtain ⟨Q, e, he, hebase⟩ :=
    chapter03_relativeProjectiveBundle_baseChange_compatibility
      g P.module.carrier P₃.finiteLocallyFree P₃
  let u : Limits.pullback f g ⟶ Limits.pullback P.ambient.projection g :=
    Limits.pullback.lift
      (Limits.pullback.fst f g ≫ P.embedding)
      (Limits.pullback.snd f g)
      (by
        rw [Category.assoc, P.overBase]
        exact Limits.pullback.condition)
  have hu : IsImmersion u := by
    let h₁ : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g f := (IsPullback.of_hasPullback f g).flip
    let h₂ : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection g).flip
    have h₁' : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g (P.embedding ≫ P.ambient.projection) := by
      simpa [P.overBase] using h₁
    have hvcond : Limits.pullback.snd f g ≫ g =
        (Limits.pullback.fst f g ≫ P.embedding) ≫ P.ambient.projection := by
      rw [Category.assoc, P.overBase]
      exact Limits.pullback.condition.symm
    let v := h₂.lift (Limits.pullback.snd f g)
      (Limits.pullback.fst f g ≫ P.embedding) hvcond
    have huv : u = v := by
      ext
      · dsimp [v]
        rw [h₂.lift_snd]
        exact Limits.pullback.lift_fst _ _ _
      · dsimp [v]
        rw [h₂.lift_fst]
        exact Limits.pullback.lift_snd _ _ _
    rw [huv]
    have hpb : IsPullback v (Limits.pullback.fst f g)
        (Limits.pullback.fst P.ambient.projection g) P.embedding := by
      simpa [v] using (IsPullback.of_right' h₁' h₂)
    exact MorphismProperty.of_isPullback hpb.flip P.isImmersion
  let : IsImmersion u := hu
  let : IsIso e := he
  refine ⟨{
    module := Q.module
    ambient := Q.canonical
    embedding := u ≫ e
    isImmersion := by infer_instance
    overBase := ?_ }⟩
  rw [Category.assoc, hebase]
  change u ≫ Limits.pullback.snd P.ambient.projection g = Limits.pullback.snd f g
  dsimp [u]
  apply Limits.pullback.lift_snd

/-- Projective morphisms are quasi-projective. -/
theorem chapter03_projective_quasiProjective (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03QuasiProjective f := by
  apply Nonempty.elim hf
  intro P
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  exact ⟨{ module := P.module, ambient := P.ambient, embedding := P.embedding, isImmersion := by infer_instance, overBase := P.overBase }⟩

private theorem chapter03_projective_precomp_iso {X' X S : Scheme.{u}}
    (e : X' ≅ X) (f : X ⟶ S) (hf : chapter03Projective f) :
    chapter03Projective (e.hom ≫ f) := by
  obtain ⟨P⟩ := hf
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  exact ⟨{ module := P.module, ambient := P.ambient, embedding := e.hom ≫ P.embedding, isClosedImmersion := by infer_instance, overBase := by simp [Category.assoc, P.overBase] }⟩

private theorem chapter03_quasiProjective_precomp_iso {X' X S : Scheme.{u}}
    (e : X' ≅ X) (f : X ⟶ S) (hf : chapter03QuasiProjective f) :
    chapter03QuasiProjective (e.hom ≫ f) := by
  obtain ⟨P⟩ := hf
  let : IsImmersion P.embedding := P.isImmersion
  exact ⟨{ module := P.module, ambient := P.ambient, embedding := e.hom ≫ P.embedding, isImmersion := by infer_instance, overBase := by simp [Category.assoc, P.overBase] }⟩

/-- Products of projective morphisms over a common base are projective. -/
theorem chapter03_projective_product (f : X ⟶ S) (g : Y ⟶ S)
    (hf : chapter03Projective f) (hg : chapter03Projective g) :
    chapter03Projective (chapter03ProductOver f g) := by
  obtain ⟨P⟩ := hf
  obtain ⟨Q⟩ := hg
  obtain ⟨R, B, hD⟩ := chapter02_relative_segre_embedding P.ambient Q.ambient
  obtain ⟨D⟩ := hD
  let v : Limits.pullback f g ⟶
      Limits.pullback P.ambient.projection g :=
    Limits.pullback.lift
      (Limits.pullback.fst f g ≫ P.embedding)
      (Limits.pullback.snd f g)
      (by
        rw [Category.assoc, P.overBase]
        exact Limits.pullback.condition)
  have hv : IsClosedImmersion v := by
    let h₁ : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g f := (IsPullback.of_hasPullback f g).flip
    let h₂ : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection g).flip
    have h₁' : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g (P.embedding ≫ P.ambient.projection) := by
      simpa [P.overBase] using h₁
    have hvcond : Limits.pullback.snd f g ≫ g =
        (Limits.pullback.fst f g ≫ P.embedding) ≫ P.ambient.projection := by
      rw [Category.assoc, P.overBase]
      exact Limits.pullback.condition.symm
    let v' := h₂.lift (Limits.pullback.snd f g)
      (Limits.pullback.fst f g ≫ P.embedding) hvcond
    have hvv' : v = v' := by
      ext
      · dsimp [v']
        rw [h₂.lift_snd]
        exact Limits.pullback.lift_fst _ _ _
      · dsimp [v']
        rw [h₂.lift_fst]
        exact Limits.pullback.lift_snd _ _ _
    rw [hvv']
    have hpb : IsPullback v' (Limits.pullback.fst f g)
        (Limits.pullback.fst P.ambient.projection g) P.embedding := by
      simpa [v'] using (IsPullback.of_right' h₁' h₂)
    exact MorphismProperty.of_isPullback hpb.flip P.isClosedImmersion
  let w : Limits.pullback P.ambient.projection g ⟶
      Limits.pullback P.ambient.projection Q.ambient.projection :=
    Limits.pullback.lift
      (Limits.pullback.fst P.ambient.projection g)
      (Limits.pullback.snd P.ambient.projection g ≫ Q.embedding)
      (by
        rw [Category.assoc, Q.overBase]
        exact Limits.pullback.condition)
  have hw : IsClosedImmersion w := by
    let h₁ : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection g).flip
    let h₂ : IsPullback
        (Limits.pullback.snd P.ambient.projection Q.ambient.projection)
        (Limits.pullback.fst P.ambient.projection Q.ambient.projection)
        Q.ambient.projection P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection Q.ambient.projection).flip
    have h₁' : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g
        (Q.embedding ≫ Q.ambient.projection) := by
      simpa [Q.overBase] using h₁
    have hwcond : Limits.pullback.fst P.ambient.projection g ≫
        P.ambient.projection =
        (Limits.pullback.snd P.ambient.projection g ≫ Q.embedding) ≫
          Q.ambient.projection := by
      rw [Category.assoc, Q.overBase]
      exact Limits.pullback.condition
    let w' := h₂.lift (Limits.pullback.fst P.ambient.projection g)
      (Limits.pullback.snd P.ambient.projection g ≫ Q.embedding) hwcond
    have hww' : w = w' := by
      ext
      · dsimp [w']
        rw [h₂.lift_fst]
        exact Limits.pullback.lift_fst _ _ _
      · dsimp [w']
        rw [h₂.lift_snd]
        exact Limits.pullback.lift_snd _ _ _
    rw [hww']
    have hpb : IsPullback w' (Limits.pullback.fst P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection Q.ambient.projection)
        Q.embedding := by
      simpa [w'] using (IsPullback.of_right' h₁' h₂)
    exact MorphismProperty.of_isPullback hpb.flip Q.isClosedImmersion
  let : IsClosedImmersion v := hv
  let : IsClosedImmersion w := hw
  let : IsClosedImmersion D.embedding := D.isClosedImmersion
  refine ⟨{ module := B.module, ambient := B,
    embedding := v ≫ w ≫ D.embedding,
    isClosedImmersion := by infer_instance, overBase := ?_ }⟩
  simp only [Category.assoc, D.overBase]
  rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst, P.overBase]

/-- Products of quasi-projective morphisms over a common base are quasi-projective. -/
theorem chapter03_quasiProjective_product (f : X ⟶ S) (g : Y ⟶ S)
    (hf : chapter03QuasiProjective f) (hg : chapter03QuasiProjective g) :
    chapter03QuasiProjective (chapter03ProductOver f g) := by
  obtain ⟨P⟩ := hf
  obtain ⟨Q⟩ := hg
  obtain ⟨R, B, hD⟩ := chapter02_relative_segre_embedding P.ambient Q.ambient
  obtain ⟨D⟩ := hD
  let v : Limits.pullback f g ⟶
      Limits.pullback P.ambient.projection g :=
    Limits.pullback.lift
      (Limits.pullback.fst f g ≫ P.embedding)
      (Limits.pullback.snd f g)
      (by
        rw [Category.assoc, P.overBase]
        exact Limits.pullback.condition)
  have hv : IsImmersion v := by
    let h₁ : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g f := (IsPullback.of_hasPullback f g).flip
    let h₂ : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection g).flip
    have h₁' : IsPullback (Limits.pullback.snd f g) (Limits.pullback.fst f g)
        g (P.embedding ≫ P.ambient.projection) := by
      simpa [P.overBase] using h₁
    have hvcond : Limits.pullback.snd f g ≫ g =
        (Limits.pullback.fst f g ≫ P.embedding) ≫ P.ambient.projection := by
      rw [Category.assoc, P.overBase]
      exact Limits.pullback.condition.symm
    let v' := h₂.lift (Limits.pullback.snd f g)
      (Limits.pullback.fst f g ≫ P.embedding) hvcond
    have hvv' : v = v' := by
      ext
      · dsimp [v']
        rw [h₂.lift_snd]
        exact Limits.pullback.lift_fst _ _ _
      · dsimp [v']
        rw [h₂.lift_fst]
        exact Limits.pullback.lift_snd _ _ _
    rw [hvv']
    have hpb : IsPullback v' (Limits.pullback.fst f g)
        (Limits.pullback.fst P.ambient.projection g) P.embedding := by
      simpa [v'] using (IsPullback.of_right' h₁' h₂)
    exact MorphismProperty.of_isPullback hpb.flip P.isImmersion
  let w : Limits.pullback P.ambient.projection g ⟶
      Limits.pullback P.ambient.projection Q.ambient.projection :=
    Limits.pullback.lift
      (Limits.pullback.fst P.ambient.projection g)
      (Limits.pullback.snd P.ambient.projection g ≫ Q.embedding)
      (by
        rw [Category.assoc, Q.overBase]
        exact Limits.pullback.condition)
  have hw : IsImmersion w := by
    let h₁ : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection g).flip
    let h₂ : IsPullback
        (Limits.pullback.snd P.ambient.projection Q.ambient.projection)
        (Limits.pullback.fst P.ambient.projection Q.ambient.projection)
        Q.ambient.projection P.ambient.projection :=
      (IsPullback.of_hasPullback P.ambient.projection Q.ambient.projection).flip
    have h₁' : IsPullback (Limits.pullback.snd P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection g) g
        (Q.embedding ≫ Q.ambient.projection) := by
      simpa [Q.overBase] using h₁
    have hwcond : Limits.pullback.fst P.ambient.projection g ≫
        P.ambient.projection =
        (Limits.pullback.snd P.ambient.projection g ≫ Q.embedding) ≫
          Q.ambient.projection := by
      rw [Category.assoc, Q.overBase]
      exact Limits.pullback.condition
    let w' := h₂.lift (Limits.pullback.fst P.ambient.projection g)
      (Limits.pullback.snd P.ambient.projection g ≫ Q.embedding) hwcond
    have hww' : w = w' := by
      ext
      · dsimp [w']
        rw [h₂.lift_fst]
        exact Limits.pullback.lift_fst _ _ _
      · dsimp [w']
        rw [h₂.lift_snd]
        exact Limits.pullback.lift_snd _ _ _
    rw [hww']
    have hpb : IsPullback w' (Limits.pullback.fst P.ambient.projection g)
        (Limits.pullback.fst P.ambient.projection Q.ambient.projection)
        Q.embedding := by
      simpa [w'] using (IsPullback.of_right' h₁' h₂)
    exact MorphismProperty.of_isPullback hpb.flip Q.isImmersion
  let : IsImmersion v := hv
  let : IsImmersion w := hw
  let : IsImmersion D.embedding := D.isClosedImmersion
  refine ⟨{ module := B.module, ambient := B,
    embedding := v ≫ w ≫ D.embedding,
    isImmersion := by infer_instance, overBase := ?_ }⟩
  simp only [Category.assoc, D.overBase]
  rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst, P.overBase]

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
  pullbackTwistingLineIso :
    (Scheme.Modules.pullback embedding).obj B.twistingLineBundle.carrier ≅
      chapter01SheafTensor
        ((Scheme.Modules.pullback (Limits.pullback.fst P.projection Q.projection)).obj
          P.twistingLineBundle.carrier)
        ((Scheme.Modules.pullback (Limits.pullback.snd P.projection Q.projection)).obj
          Q.twistingLineBundle.carrier)

/-- The Segre map is a closed immersion into the projective bundle of the tensor product. -/
theorem chapter03_segre_embedding (S : Scheme.{u}) (E F : S.Modules)
    (_hE : chapter03FiniteLocallyFree E) (_hF : chapter03FiniteLocallyFree F)
    (P : Chapter03RelativeProjectiveBundle S E)
    (Q : Chapter03RelativeProjectiveBundle S F) :
    ∃ (R : Chapter03TensorProductModule S E F)
      (B : Chapter03RelativeProjectiveBundle S R.module),
      Nonempty (Chapter03SegreData P Q R B) := by
  subst E
  subst F
  obtain ⟨R, B, hB⟩ :=
    chapter02_relative_segre_embedding P.canonical Q.canonical
  obtain ⟨D⟩ := hB
  let R₃ : Chapter03TensorProductModule S P.module.carrier Q.module.carrier :=
    { module := R.module
      finiteLocallyFree := R.finiteLocallyFree
      tensorProductIso := R.tensorProductIso }
  let B₃ : Chapter03RelativeProjectiveBundle S R₃.module :=
    { module := chapter02FiniteTensorProductQuasiCoherentModule R
      module_carrier := rfl
      finiteLocallyFree := R.finiteLocallyFree
      canonical := B }
  refine ⟨R₃, B₃, ⟨{
    embedding := D.embedding
    isClosedImmersion := D.isClosedImmersion
    overBase := D.overBase
    pullbackTwistingLineIso := D.pullbackTwistingLineIso }⟩⟩

/-- Composition of projective morphisms is projective. -/
theorem chapter03_projective_comp (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : chapter03Projective f) (hg : chapter03Projective g)
    [QuasiCompact (𝟙 S)] [QuasiSeparated (𝟙 S)] :
    chapter03Projective (f ≫ g) := by
  obtain ⟨P⟩ := hf
  obtain ⟨Q⟩ := hg
  exact chapter02_projective_presentation_comp f g P Q

/-- Composition of quasi-projective morphisms is quasi-projective. -/
theorem chapter03_quasiProjective_comp (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : chapter03QuasiProjective f) (hg : chapter03QuasiProjective g)
    (hfqc : QuasiCompact f) (hgqc : QuasiCompact g)
    [QuasiCompact (𝟙 S)] [QuasiSeparated (𝟙 S)] :
    chapter03QuasiProjective (f ≫ g) := by
  obtain ⟨P⟩ := hf
  obtain ⟨Q⟩ := hg
  exact chapter02_quasi_projective_presentation_comp f g P Q

/-- A projective morphism is locally projective on the target. -/
theorem chapter03_locallyProjective_of_projective (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03LocallyProjective f := by
  let 𝒰 : S.OpenCover :=
    S.openCoverOfIsOpenCover
      (fun i : S.affineCover.I₀ => (S.affineCover.f i).opensRange)
      S.affineCover.isOpenCover_opensRange
  refine ⟨𝒰, ?_⟩
  intro i
  have hp : chapter03Projective
      (Limits.pullback.snd f (𝒰.f i).opensRange.ι) :=
    chapter03_projective_baseChange f (𝒰.f i).opensRange.ι hf
  have hp' := chapter03_projective_precomp_iso
    (pullbackRestrictIsoRestrict f (𝒰.f i).opensRange).symm
    (Limits.pullback.snd f (𝒰.f i).opensRange.ι) hp
  simpa only [𝒰, ← pullbackRestrictIsoRestrict_hom_morphismRestrict,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hp'

/-- A quasi-projective morphism is locally quasi-projective on the target. -/
theorem chapter03_locallyQuasiProjective_of_quasiProjective (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) : chapter03LocallyQuasiProjective f := by
  let 𝒰 : S.OpenCover :=
    S.openCoverOfIsOpenCover
      (fun i : S.affineCover.I₀ => (S.affineCover.f i).opensRange)
      S.affineCover.isOpenCover_opensRange
  refine ⟨𝒰, ?_⟩
  intro i
  have hp : chapter03QuasiProjective
      (Limits.pullback.snd f (𝒰.f i).opensRange.ι) :=
    chapter03_quasiProjective_baseChange f (𝒰.f i).opensRange.ι hf
  have hp' := chapter03_quasiProjective_precomp_iso
    (pullbackRestrictIsoRestrict f (𝒰.f i).opensRange).symm
    (Limits.pullback.snd f (𝒰.f i).opensRange.ι) hp
  simpa only [𝒰, ← pullbackRestrictIsoRestrict_hom_morphismRestrict,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hp'

/-- Local projectivity globalizes only after a global polarization is supplied. -/
theorem chapter03_projective_iff_locallyProjective [CompactSpace S]
    (f : X ⟶ S) (P : Chapter03GlobalPolarization f) :
    chapter03Projective f ↔ chapter03LocallyProjective f := by
  constructor
  · exact chapter03_locallyProjective_of_projective f
  · rintro ⟨𝒰, h𝒰⟩
    exact chapter02_projective_presentation_of_compact_open_cover f 𝒰 h𝒰

/-- Local quasi-projectivity globalizes only after a global polarization and finite-type data are
supplied. -/
theorem chapter03_quasiProjective_iff_locallyQuasiProjective [CompactSpace S]
    (f : X ⟶ S)
    (hqc : QuasiCompact f) (hft : LocallyOfFiniteType f)
    (hqs : QuasiSeparated f) (P : Chapter03GlobalPolarization f) :
    chapter03QuasiProjective f ↔ chapter03LocallyQuasiProjective f := by
  constructor
  · exact chapter03_locallyQuasiProjective_of_quasiProjective f
  · rintro ⟨𝒰, h𝒰⟩
    exact chapter02_quasi_projective_presentation_of_compact_open_cover f 𝒰 h𝒰

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
    (f : X ⟶ S) (P : Chapter03GlobalPolarization f) :
    chapter03Projective f ↔ chapter03LocallyInStandardProjectiveSpace f := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
