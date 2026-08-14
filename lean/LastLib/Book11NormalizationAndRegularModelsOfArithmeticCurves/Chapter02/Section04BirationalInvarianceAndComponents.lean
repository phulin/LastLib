import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section03UniversalProperty
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.TensorProduct.Basic

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

noncomputable section

/-! ### 2.4 Birational invariance and components -/

theorem chapter02_normal_scheme_is_self_normalizing (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter02Normal X]
    [QuasiCompact (𝟙 X)] [QuasiSeparated (𝟙 X)] :
    IsIso ((𝟙 X).toNormalization) := by
  infer_instance

/-- The comparison from the normalization of a base change to the base change of a normalization. -/
noncomputable def chapter02NormalizationPullbackComparison
    {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (pullback.snd f g).normalization ⟶ pullback f.fromNormalization g :=
  f.normalizationPullback g

theorem chapter02_normalization_pullback_isIso
    {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Smooth g] :
    IsIso (chapter02NormalizationPullbackComparison f g) := by
  infer_instance

/-- Open immersions are smooth, so normalization restricts to the inverse image of an open. -/
theorem chapter02_normalization_of_open_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) :
    IsIso (chapter02NormalizationPullbackComparison f U.ι) := by
  infer_instance

/-- The dense-open specialization used in birational invariance. -/
theorem chapter02_normalization_of_dense_open_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (hU : Dense (U : Set S)) :
    IsIso (chapter02NormalizationPullbackComparison f U.ι) := by
  infer_instance

/-- The locus where the absolute normalization is not asserted to be locally an isomorphism. -/
def chapter02NonnormalLocus (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Set X :=
  {x | ¬ IsIntegrallyClosed (X.presheaf.stalk x)}

/-- Local triviality of a morphism at a point, expressed by an actual restriction map. -/
def Chapter02NormalizationTrivialAt {X' X : Scheme.{u}} (ν : X' ⟶ X) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ IsIso (Scheme.Hom.morphismRestrict ν U)

theorem chapter02_absolute_normalization_trivial_off_nonnormal_locus
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [QuasiCompact (𝟙 X)] [QuasiSeparated (𝟙 X)]
    (x : X) (hx : x ∉ chapter02NonnormalLocus X) :
    Chapter02NormalizationTrivialAt (chapter02AbsoluteNormalizationMap X) x := by
  sorry

theorem chapter02_normalization_trivial_when_normal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [Chapter02Normal X]
    [QuasiCompact (𝟙 X)] [QuasiSeparated (𝟙 X)] :
    ∀ x : X, Chapter02NormalizationTrivialAt (chapter02AbsoluteNormalizationMap X) x := by
  sorry

/-- The normalization of a finite coproduct is the coproduct of the component normalizations. -/
noncomputable def chapter02NormalizationCoproductIso
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X)
    (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact iU] [QuasiSeparated iU]
    [QuasiCompact iV] [QuasiSeparated iV] :
    (iU ≫ f).normalization ⨿ (iV ≫ f).normalization ≅ f.normalization :=
  f.normalizationCoprodIso e

theorem chapter02_normalization_coproduct_inl
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X)
    (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact iU] [QuasiSeparated iU]
    [QuasiCompact iV] [QuasiSeparated iV] :
    (iU ≫ f).toNormalization ≫ coprod.inl ≫
        (chapter02NormalizationCoproductIso f iU iV e).hom =
      iU ≫ f.toNormalization := by
  exact f.toNormalization_inl_normalizationCoprodIso_hom e

theorem chapter02_normalization_coproduct_inr
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X)
    (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact iU] [QuasiSeparated iU]
    [QuasiCompact iV] [QuasiSeparated iV] :
    (iV ≫ f).toNormalization ≫ coprod.inr ≫
        (chapter02NormalizationCoproductIso f iU iV e).hom =
      iV ≫ f.toNormalization := by
  exact f.toNormalization_inr_normalizationCoprodIso_hom e

theorem chapter02_normalization_coproduct_fromNormalization_inl
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X)
    (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact iU] [QuasiSeparated iU]
    [QuasiCompact iV] [QuasiSeparated iV] :
    coprod.inl ≫ (chapter02NormalizationCoproductIso f iU iV e).hom ≫ f.fromNormalization =
      (iU ≫ f).fromNormalization := by
  exact f.inl_normalizationCoprodIso_hom_fromNormalization e

theorem chapter02_normalization_coproduct_fromNormalization_inr
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (iU : U ⟶ X) (iV : V ⟶ X)
    (e : IsColimit (BinaryCofan.mk iU iV))
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact iU] [QuasiSeparated iU]
    [QuasiCompact iV] [QuasiSeparated iV] :
    coprod.inr ≫ (chapter02NormalizationCoproductIso f iU iV e).hom ≫ f.fromNormalization =
      (iV ≫ f).fromNormalization := by
  exact f.inr_normalizationCoprodIso_hom_fromNormalization e

/-- The finite-component form of the coproduct statement.  The binary comparison above is the
inductive step used to construct this finite coproduct comparison. -/
theorem chapter02_normalization_finite_coproduct
    {ι : Type u} [Finite ι] {Y : Scheme.{u}}
    (X : ι → Scheme.{u}) (f : (∐ i, X i) ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (∐ i, (Sigma.ι X i ≫ f).normalization) ≅ f.normalization := by
  sorry

theorem chapter02_node_is_reduced (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    IsReduced (Chapter02NodeRing k) := by
  sorry

theorem chapter02_node_connected_but_normalization_disconnected (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    ConnectedSpace (Spec (CommRingCat.of (Chapter02NodeRing k))) ∧
      ¬ ConnectedSpace (Spec (CommRingCat.of (Polynomial k × Polynomial k))) := by
  sorry

/-- The scheme-level meaning of a finite birational morphism: finite and birational over the
target, with the birationality witnessed on dense open subschemes. -/
def Chapter02FiniteBirationalMorphism {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsFinite f ∧ Scheme.BirationalOver f (𝟙 X)

theorem chapter02_finite_birational_normal_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [Chapter02Normal X] [Chapter02Normal Y]
    (hf : Chapter02FiniteBirationalMorphism f) :
    IsIso f := by
  sorry

/-! A ring-level affine interface for the finite-birational rigidity statement. -/

/-- A finite birational extension, with both normal domains embedded in one common field. -/
structure Chapter02AffineBirationalExtension
    (A B K : Type u) [CommRing A] [CommRing B] [Field K]
    [IsDomain A] [IsDomain B]
    [Algebra A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K] where
  map : A →+* B
  map_eq_algebraMap : map = algebraMap A B
  finite : Module.Finite A B
  injective_A : Function.Injective (algebraMap A K)
  injective_B : Function.Injective (algebraMap B K)
  A_integrallyClosed : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = x
  B_integrallyClosed : ∀ x : K, IsIntegral B x → ∃ b : B, algebraMap B K b = x

theorem chapter02_finite_birational_affine_is_bijective
    (A B K : Type u) [CommRing A] [CommRing B] [Field K]
    [IsDomain A] [IsDomain B]
    [Algebra A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K]
    (E : Chapter02AffineBirationalExtension A B K) :
    Function.Bijective E.map := by
  sorry

theorem chapter02_finite_morphisms_compose
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] :
    Module.Finite A C := by
  exact Module.Finite.trans A B C

theorem chapter02_birational_maps_compose
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g.comp f) := by
  exact hg.comp hf

theorem chapter02_finite_birational_maps_compose
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C]
    (f : A →+* B) (g : B →+* C)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g.comp f) ∧ Module.Finite A C := by
  exact ⟨hg.comp hf, Module.Finite.trans A B C⟩

/-! The base-change warning is recorded both as a reusable predicate and as an
existence statement for a ring-level counterexample. -/

def Chapter02NormalityFailureAfterFieldExtension
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] : Prop :=
  IsIntegrallyClosed A ∧ ¬ IsIntegrallyClosed (K ⊗[k] A)

theorem chapter02_normality_failure_after_field_extension_iff
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] :
    Chapter02NormalityFailureAfterFieldExtension k K A ↔
      IsIntegrallyClosed A ∧ ¬ IsIntegrallyClosed (K ⊗[k] A) :=
  Iff.rfl

structure Chapter02NormalityFieldExtensionCounterexample
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] : Prop where
  base_normal : IsIntegrallyClosed A
  scalar_extension_not_normal : ¬ IsIntegrallyClosed (K ⊗[k] A)

theorem chapter02_normality_not_stable_under_arbitrary_field_extension :
    ∃ (k K A : Type u) (hk : Field k) (hK : Field K) (hKAlg : Algebra k K)
      (hA : CommRing A) (hAAlg : Algebra k A),
      Nonempty (@Chapter02NormalityFieldExtensionCounterexample
        k K A hk hK hKAlg hA hAAlg) := by
  sorry

/-- The scheme-theoretic scalar extension whose normalization must be compared with base change. -/
def chapter02FieldBaseChange {X : Scheme.{u}} {k K : Type u} [Field k] [Field K]
    [Algebra k K] (f : X ⟶ Spec (CommRingCat.of k)) : Scheme :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- Normalize the scalar extension itself. -/
noncomputable def chapter02NormalizationAfterFieldBaseChange
    {X : Scheme.{u}} {k K : Type u} [Field k] [Field K] [Algebra k K]
    (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact (𝟙 (chapter02FieldBaseChange f))]
    [QuasiSeparated (𝟙 (chapter02FieldBaseChange f))] : Scheme :=
  (𝟙 (chapter02FieldBaseChange f)).normalization

/-- Base-change the absolute normalization of `X`.  This is a separate construction from the
normalization of `chapter02FieldBaseChange f`. -/
noncomputable def chapter02FieldBaseChangeOfNormalization
    {X : Scheme.{u}} {k K : Type u} [Field k] [Field K] [Algebra k K]
    (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact (𝟙 X)] [QuasiSeparated (𝟙 X)] : Scheme :=
  pullback (chapter02AbsoluteNormalizationMap X ≫ f)
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
