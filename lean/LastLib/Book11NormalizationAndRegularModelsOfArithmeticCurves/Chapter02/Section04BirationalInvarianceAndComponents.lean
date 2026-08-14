import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section01AffineConstruction
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section02LocalizationAndGluing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.ULift
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

noncomputable section

/-! ### 2.4 Birational invariance and components -/

private theorem chapter02_affine_sections_integrallyClosed
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [Chapter02Normal X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp hpm
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hpm.isPrime⟩
  let x : U := hU.isoSpec.inv y
  have hxy : hU.primeIdealOf x = y := by
    change hU.isoSpec.hom (hU.isoSpec.inv y) = y
    have h := congrArg (fun q => q y) hU.isoSpec.inv_hom_id
    change hU.isoSpec.hom (hU.isoSpec.inv y) = y at h
    simpa using h
  have hloc := hU.isLocalization_stalk x
  rw [hxy] at hloc
  exact (Chapter02Normal.integrallyClosed_stalk x.1).of_equiv
    (IsLocalization.algEquiv p.primeCompl
      (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv

theorem chapter02_normal_scheme_is_self_normalizing (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [Chapter02Normal X]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X X.functionField)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X X.functionField)] :
    IsIso (chapter02AbsoluteNormalizationMap X) := by
  let f := chapter02FunctionFieldExtensionMap X X.functionField
  have hpre (U : X.Opens) (hU : IsAffineOpen U) (hNU : Nonempty U) :
      f ⁻¹ᵁ U = ⊤ := by
    apply le_antisymm le_top
    intro z hz
    have hz' : z = genericPoint (Spec (CommRingCat.of X.functionField)) := Subsingleton.elim _ _
    subst z
    change f (genericPoint (Spec (CommRingCat.of X.functionField))) ∈ U
    rw [show f (genericPoint (Spec (CommRingCat.of X.functionField))) = genericPoint X by
      have hbot : (⊥ : PrimeSpectrum X.functionField) =
          IsLocalRing.closedPoint X.functionField := by
        apply PrimeSpectrum.ext
        change (⊥ : Ideal X.functionField) = IsLocalRing.maximalIdeal X.functionField
        rw [IsLocalRing.maximalIdeal_eq_bot]
      simp [f, chapter02FunctionFieldExtensionMap]
      rw [hbot]
      exact Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)]
    exact ((genericPoint_spec X).mem_open_set_iff U.2).mpr (by simpa using hNU)
  let : IsAffineHom f.fromNormalization := inferInstance
  change IsIso f.fromNormalization
  rw [← MorphismProperty.isomorphisms.iff]
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
    (iSup_affineOpens_eq_top X)]
  intro U
  change IsIso (f.fromNormalization ∣_ U.1)
  have hU : IsAffineOpen U.1 := by
    simpa only [Scheme.affineOpens, Set.mem_ofPred_eq] using U.2
  rw [isIso_morphismRestrict_iff_isIso_app f.fromNormalization hU]
  let := (f.app U.1).hom.toAlgebra
  cases isEmpty_or_nonempty U.1 with
  | inl hUempty =>
    have hUbot : (U : X.Opens) = (⊥ : X.Opens) :=
      (TopologicalSpace.Opens.not_nonempty_iff_eq_bot U.1).mp
        (by
          intro h
          rcases h with ⟨y, hy⟩
          exact hUempty.false ⟨y, hy⟩)
    rw [hUbot]
    have hpreempty : f.fromNormalization ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by
      ext z
      simp
    let : Subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ (⊥ : X.Opens)) := by
      rw [hpreempty]
      infer_instance
    apply (ConcreteCategory.isIso_iff_bijective (f.fromNormalization.app (⊥ : X.Opens))).mpr
    constructor
    · intro a b hab
      exact Subsingleton.elim _ _
    · intro b
      exact ⟨0, Subsingleton.elim _ _⟩
  | inr hUnonempty =>
    have hpreU := hpre U.1 hU hUnonempty
    rw [Scheme.Hom.fromNormalization_app f hU]
    let eB : Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1) ≃+*
        X.functionField :=
      ((Spec (CommRingCat.of X.functionField)).presheaf.mapIso
        (eqToIso hpreU.symm).op ≪≫ Scheme.ΓSpecIso (CommRingCat.of X.functionField)).commRingCatIsoToRingEquiv
    have heB : Function.Bijective eB := eB.bijective
    have hmem : f (IsLocalRing.closedPoint X.functionField) ∈ U.1 := by
      change IsLocalRing.closedPoint X.functionField ∈ f ⁻¹ᵁ U.1
      rw [hpreU]
      trivial
    have hmap : eB.toRingHom.comp (algebraMap Γ(X, U.1)
        (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1))) =
        algebraMap Γ(X, U.1) X.functionField := by
      ext r
      change eB ((f.app U.1).hom r) = X.germToFunctionField U.1 r
      have hg := Scheme.germ_stalkClosedPointTo (f := f) (U := U.1) hmem
      have hg' := congrArg CommRingCat.Hom.hom hg
      have hright : eB ((f.app U.1).hom r) =
          (X.presheaf.germ U.1 (f (IsLocalRing.closedPoint X.functionField)) hmem ≫
            Scheme.stalkClosedPointTo f).hom r := by
        change (CommRingCat.Hom.hom
          ((Spec (CommRingCat.of X.functionField)).presheaf.mapIso
            (eqToIso hpreU.symm).op ≪≫ Scheme.ΓSpecIso
              (CommRingCat.of X.functionField)).hom) ((f.app U.1).hom r) = _
        simpa using congrArg (fun q => q r) hg'.symm
      rw [hright]
      have hxU : genericPoint X ∈ U.1 := by
        exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by
          simpa using (inferInstance : Nonempty U.1))
      have hgl := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
        (X := X) (x := genericPoint X)
        (f := 𝟙 X.functionField) U.1 (by
          simpa only [Spec.map_id, Category.id_comp, Scheme.Hom.comp_apply,
            Scheme.fromSpecStalk_closedPoint] using hxU)
      have hgl' := congrArg CommRingCat.Hom.hom hgl
      simpa [f, chapter02FunctionFieldExtensionMap, Scheme.germToFunctionField,
        CommRingCat.of_carrier, CommRingCat.hom_comp] using
        congrArg (fun q => q r) hgl'
    have hR : IsIntegrallyClosed Γ(X, U.1) :=
      chapter02_affine_sections_integrallyClosed X U.1 hU
    let eAlg : Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1) ≃ₐ[Γ(X, U.1)]
        X.functionField :=
      { eB with
        commutes' := fun r => congrArg (fun q => q r) hmap }
    let : IsFractionRing Γ(X, U.1) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U.1 hU
    let : IsFractionRing Γ(X, U.1)
        (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1)) :=
      IsFractionRing.of_algEquiv eAlg.symm
    let : IsIntegrallyClosedIn Γ(X, U.1)
        (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1)) :=
      (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mp hR
    have hinj : Function.Injective (algebraMap Γ(X, U.1)
        (integralClosure Γ(X, U.1)
          (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1)))) := by
      intro a b hab
      apply IsFractionRing.injective Γ(X, U.1)
        (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1))
      exact congrArg Subtype.val hab
    have hsurj : Function.Surjective (algebraMap Γ(X, U.1)
        (integralClosure Γ(X, U.1)
          (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1)))) := by
      intro z
      obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral z.property
      refine ⟨r, ?_⟩
      apply Subtype.ext
      exact hr
    let eR := RingEquiv.ofBijective
      (algebraMap Γ(X, U.1)
        (integralClosure Γ(X, U.1)
          (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1)))) ⟨hinj, hsurj⟩
    change IsIso (CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (integralClosure Γ(X, U.1)
        (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1)))) ≫
      (Scheme.Hom.normalizationObjIso f hU).inv)
    have : IsIso (CommRingCat.ofHom (algebraMap Γ(X, U.1)
        (integralClosure Γ(X, U.1)
          (Γ(Spec (CommRingCat.of X.functionField), f ⁻¹ᵁ U.1))))) := by
      change IsIso eR.toCommRingCatIso.hom
      infer_instance
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
  change IsIso (f.normalizationPullback g)
  infer_instance

/-- Open immersions are smooth, so normalization restricts to the inverse image of an open. -/
theorem chapter02_normalization_of_open_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) :
    IsIso (chapter02NormalizationPullbackComparison f U.ι) := by
  change IsIso (f.normalizationPullback U.ι)
  infer_instance

/-- The dense-open specialization used in birational invariance. -/
theorem chapter02_normalization_of_dense_open_isIso
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X X.functionField)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X X.functionField)]
    (U : {U : X.Opens // Dense (U : Set X)}) :
    IsIso (chapter02NormalizationPullbackComparison
      (chapter02FunctionFieldExtensionMap X X.functionField) U.1.ι) := by
  exact chapter02_normalization_of_open_isIso
    (chapter02FunctionFieldExtensionMap X X.functionField) U.1

/-- The locus where the absolute normalization is not asserted to be locally an isomorphism. -/
def chapter02NonnormalLocus (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] : Set X :=
  {x | ¬ IsIntegrallyClosed (X.presheaf.stalk x)}

/-- Local triviality of a morphism at a point, expressed by an actual restriction map. -/
def Chapter02NormalizationTrivialAt {X' X : Scheme.{u}} (ν : X' ⟶ X) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ IsIso (ν ∣_ U)

theorem chapter02_absolute_normalization_trivial_off_nonnormal_locus
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X X.functionField)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X X.functionField)]
    [IsFinite (chapter02AbsoluteNormalizationMap X)]
    (x : X) (hx : x ∉ chapter02NonnormalLocus X) :
    Chapter02NormalizationTrivialAt (chapter02AbsoluteNormalizationMap X) x := by
  sorry

theorem chapter02_normalization_trivial_when_normal
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [Chapter02Normal X]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X X.functionField)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X X.functionField)] :
    ∀ x : X, Chapter02NormalizationTrivialAt (chapter02AbsoluteNormalizationMap X) x := by
  intro x
  refine ⟨⊤, by simp, ?_⟩
  let : IsIso (chapter02AbsoluteNormalizationMap X) :=
    chapter02_normal_scheme_is_self_normalizing X
  change IsIso (chapter02AbsoluteNormalizationMap X ∣_ (⊤ : X.Opens))
  infer_instance

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

private theorem chapter02_isIntegralHom_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIntegralHom f := by
  constructor
  intro U hU
  apply (RingHom.Finite.of_surjective _ ?_).to_isIntegral
  have hbij : Function.Bijective (f.app U).hom :=
    ConcreteCategory.bijective_of_isIso (f.app U)
  exact hbij.2

private theorem chapter02_isIntegralHom_sigmaDesc
    {ι : Type u} [Finite ι] {Y : Scheme.{u}}
    (Z : ι → Scheme.{u}) (g : ∀ i, Z i ⟶ Y)
    (hg : ∀ i, IsIntegralHom (g i)) :
    IsIntegralHom (Sigma.desc g) := by
  sorry

/-- The finite-component form of the coproduct statement.  The binary comparison above is the
inductive step used to construct this finite coproduct comparison. -/
noncomputable def chapter02_normalization_finite_coproduct
    {ι : Type u} [Finite ι] {Y : Scheme.{u}}
    (X : ι → Scheme.{u}) (f : (∐ X) ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [∀ i, QuasiCompact (Sigma.ι X i ≫ f)]
    [∀ i, QuasiSeparated (Sigma.ι X i ≫ f)] :
    (∐ fun i ↦ (Sigma.ι X i ≫ f).normalization) ≅ f.normalization := by
  classical
  let hom : (∐ fun i ↦ (Sigma.ι X i ≫ f).normalization) ⟶ f.normalization :=
    Sigma.desc fun i ↦
      (Sigma.ι X i ≫ f).normalizationDesc
        (Sigma.ι X i ≫ f.toNormalization) f.fromNormalization (by
          rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization])
  let f₂ : (∐ fun i ↦ (Sigma.ι X i ≫ f).normalization) ⟶ Y :=
    Sigma.desc fun i ↦ (Sigma.ι X i ≫ f).fromNormalization
  letI : IsIntegralHom f₂ := chapter02_isIntegralHom_sigmaDesc _ _
    (fun i ↦ inferInstance)
  let f₁ : (∐ fun i ↦ X i) ⟶ (∐ fun i ↦ (Sigma.ι X i ≫ f).normalization) :=
    Sigma.desc fun i ↦
      (Sigma.ι X i ≫ f).toNormalization ≫ Sigma.ι
        (fun i ↦ (Sigma.ι X i ≫ f).normalization) i
  have hf : f = f₁ ≫ f₂ := by
    apply Sigma.hom_ext
    intro i
    simp [f₁, f₂, Category.assoc]
  let inv : f.normalization ⟶ (∐ fun i ↦ (Sigma.ι X i ≫ f).normalization) :=
    f.normalizationDesc f₁ f₂ hf
  refine { hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro i
    apply Scheme.Hom.normalization.hom_ext
      (f := Sigma.ι X i ≫ f)
      (Sigma.ι (fun i ↦ (Sigma.ι X i ≫ f).normalization) i ≫ hom ≫ inv)
      (Sigma.ι (fun i ↦ (Sigma.ι X i ≫ f).normalization) i) f₂
    · simp [hom, inv, f₁, f₂, Category.assoc]
    · simp [hom, inv, f₁, f₂, Category.assoc]
    · simp [f₂]
  · have hhomf₂ : hom ≫ f.fromNormalization = f₂ := by
      apply Sigma.hom_ext
      intro i
      simp [hom, f₂]
    apply Scheme.Hom.normalization.hom_ext (f := f) (inv ≫ hom) (𝟙 _) f.fromNormalization
    · apply Sigma.hom_ext
      intro i
      simp [inv, hom, f₁, f₂, Category.assoc]
    · rw [Category.assoc, hhomf₂]
      exact Scheme.Hom.normalizationDesc_comp (f := f) (f₁ := f₁) (f₂ := f₂) hf
    · simp

theorem chapter02_node_is_reduced (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    IsReduced (Chapter02NodeRing k) := by
  exact isReduced_of_injective (chapter02NodeNormalizationMap k)
    (chapter02_node_normalization_injective k)

theorem chapter02_node_connected_but_normalization_disconnected (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    ConnectedSpace (Spec (CommRingCat.of (Chapter02NodeRing k))) ∧
      ¬ ConnectedSpace (Spec (CommRingCat.of (Polynomial k × Polynomial k))) := by
  have hpoly : ∀ p : Polynomial k, IsIdempotentElem p → p = 0 ∨ p = 1 := by
    intro p hp
    rcases mul_eq_zero.mp hp.mul_one_sub_self with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  have hconst : ∀ z : Chapter02NodeRing k,
      (chapter02NodeNormalizationMap k z).1.coeff 0 =
        (chapter02NodeNormalizationMap k z).2.coeff 0 := by
    intro z
    rcases z with ⟨p⟩
    change (chapter02NodeBranchMap k p).1.coeff 0 =
      (chapter02NodeBranchMap k p).2.coeff 0
    let e0 : Chapter02NodePolynomialRing k →+* Polynomial k :=
      MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
        (fun i => if i = (0 : Fin 2) then Polynomial.X else 0)
    let e1 : Chapter02NodePolynomialRing k →+* Polynomial k :=
      MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
        (fun i => if i = (1 : Fin 2) then Polynomial.X else 0)
    change (e0 p).coeff 0 = (e1 p).coeff 0
    induction p using MvPolynomial.induction_on with
    | C a => simp [e0, e1]
    | add p q hp hq =>
        simpa [e0, e1, Polynomial.coeff_add] using congrArg₂ (· + ·) hp hq
    | mul_X p i hp =>
        fin_cases i <;> simp [e0, e1]
  have hnode : ∀ z : Chapter02NodeRing k, IsIdempotentElem z → z = 0 ∨ z = 1 := by
    intro z hz
    have hz' : IsIdempotentElem (chapter02NodeNormalizationMap k z) :=
      hz.map (chapter02NodeNormalizationMap k)
    have hp : IsIdempotentElem (chapter02NodeNormalizationMap k z).1 := by
      rw [isIdempotentElem_iff]
      exact congrArg Prod.fst hz'.eq
    have hq : IsIdempotentElem (chapter02NodeNormalizationMap k z).2 := by
      rw [isIdempotentElem_iff]
      exact congrArg Prod.snd hz'.eq
    rcases hpoly _ hp with hp | hp <;> rcases hpoly _ hq with hq | hq
    · left
      apply chapter02_node_normalization_injective k
      ext <;> simp [hp, hq]
    · exfalso
      have h01 : (0 : k) = 1 := by
        simpa [hp, hq] using hconst z
      exact (zero_ne_one : (0 : k) ≠ 1) h01
    · exfalso
      have h10 : (1 : k) = 0 := by
        simpa [hp, hq] using hconst z
      exact (one_ne_zero : (1 : k) ≠ 0) h10
    · right
      apply chapter02_node_normalization_injective k
      ext <;> simp [hp, hq]
  have hconnected : ConnectedSpace (Spec (CommRingCat.of (Chapter02NodeRing k))) := by
    change ConnectedSpace (PrimeSpectrum (Chapter02NodeRing k))
    let : Nontrivial (Chapter02NodeRing k) := by
      refine ⟨0, 1, ?_⟩
      intro h
      have h' := congrArg (fun z => (chapter02NodeNormalizationMap k z).1) h
      simp at h'
    rw [connectedSpace_iff_clopen]
    refine ⟨inferInstance, ?_⟩
    intro s hs
    obtain ⟨z, hz, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases hnode z hz with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  have hdisconnected : ¬ ConnectedSpace
      (Spec (CommRingCat.of (Polynomial k × Polynomial k))) := by
    intro h
    change ConnectedSpace (PrimeSpectrum (Polynomial k × Polynomial k)) at h
    let A := PrimeSpectrum (Polynomial k)
    let B := PrimeSpectrum (Polynomial k)
    let s : Set (A ⊕ B) := Sum.inl '' (Set.univ : Set A)
    have hs : IsClopen s := by
      constructor
      · simpa [s] using isClosedMap_inl (X := A) (Y := B) Set.univ isClosed_univ
      · simpa [s] using isOpenMap_inl (X := A) (Y := B) Set.univ isOpen_univ
    have hsne : s ≠ ∅ := by
      intro he
      let a : A := Classical.choice (inferInstance : Nonempty A)
      have ha : Sum.inl a ∈ s := ⟨a, trivial, rfl⟩
      simp [he] at ha
    have hsuniv : s ≠ Set.univ := by
      intro he
      let b : B := Classical.choice (inferInstance : Nonempty B)
      have hb : Sum.inr b ∈ s := by rw [he]; trivial
      rcases hb with ⟨a, _, hab⟩
      exact Sum.inl_ne_inr hab
    have hsum : ConnectedSpace (A ⊕ B) := by
      exact (Homeomorph.connectedSpace_iff
        (PrimeSpectrum.primeSpectrumProdHomeo (R := Polynomial k) (S := Polynomial k))).mp h
    exact hsne ((connectedSpace_iff_clopen.mp hsum).2 s hs |>.resolve_right hsuniv)
  exact ⟨hconnected, hdisconnected⟩

/-- The scheme-level meaning of a finite birational morphism: finite and birational over the
target, with the birationality witnessed on dense open subschemes. -/
def Chapter02FiniteBirationalMorphism {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsFinite f ∧ Scheme.BirationalOver f (𝟙 X)

theorem chapter02_finite_birational_morphisms_compose
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (hf : Chapter02FiniteBirationalMorphism f)
    (hg : Chapter02FiniteBirationalMorphism g) :
    Chapter02FiniteBirationalMorphism (g ≫ f) := by
  rcases hf with ⟨hfFinite, hfBir⟩
  rcases hg with ⟨hgFinite, hgBir⟩
  let : IsFinite f := hfFinite
  let : IsFinite g := hgFinite
  refine ⟨?_, ?_⟩
  · infer_instance
  · apply Scheme.BirationalOver.trans (S := X) (sX := g ≫ f) (sY := f) (sZ := 𝟙 X)
    · refine ⟨hgBir.partialIso, ?_⟩
      simpa [Category.assoc] using congrArg (fun h => h ≫ f) hgBir.partialIso_isOver
    · exact hfBir

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
  let : Module.Finite A B := E.finite
  constructor
  · intro a b hab
    apply E.injective_A
    simpa [E.map_eq_algebraMap, IsScalarTower.algebraMap_apply A B K] using
      congrArg (algebraMap B K) hab
  · intro b
    have hb : IsIntegral A (algebraMap B K b) := by
      exact (IsIntegral.of_finite A b).map (IsScalarTower.toAlgHom A B K)
    obtain ⟨a, ha⟩ := E.A_integrallyClosed (algebraMap B K b) hb
    refine ⟨a, ?_⟩
    apply E.injective_B
    simpa [E.map_eq_algebraMap, IsScalarTower.algebraMap_apply A B K] using ha

theorem chapter02_finite_morphisms_compose
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] :
    Module.Finite A C := by
  exact Module.Finite.trans B C

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
  exact ⟨hg.comp hf, Module.Finite.trans B C⟩

/-! The base-change warning is recorded both as a reusable predicate and as an
existence statement for a ring-level counterexample. -/

def Chapter02NormalityFailureAfterFieldExtension
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] : Prop :=
  (IsReduced A ∧ IsIntegrallyClosed A) ∧
    ¬ (IsReduced (K ⊗[k] A) ∧ IsIntegrallyClosed (K ⊗[k] A))

theorem chapter02_normality_failure_after_field_extension_iff
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] :
    Chapter02NormalityFailureAfterFieldExtension k K A ↔
      (IsReduced A ∧ IsIntegrallyClosed A) ∧
        ¬ (IsReduced (K ⊗[k] A) ∧ IsIntegrallyClosed (K ⊗[k] A)) :=
  Iff.rfl

structure Chapter02NormalityFieldExtensionCounterexample
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] : Prop where
  base_normal : IsReduced A ∧ IsIntegrallyClosed A
  scalar_extension_not_normal :
    ¬ (IsReduced (K ⊗[k] A) ∧ IsIntegrallyClosed (K ⊗[k] A))

theorem chapter02_normality_not_stable_under_arbitrary_field_extension :
    ∃ (k K A : Type u) (hk : Field k) (hK : Field K) (hKAlg : Algebra k K)
      (hA : CommRing A) (hAAlg : Algebra k A),
      Nonempty (@Chapter02NormalityFieldExtensionCounterexample
        k K A hk hK hKAlg hA hAAlg) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let k : Type u := RatFunc (ULift.{u} (ZMod 2))
  let a : k := RatFunc.X
  let f : Polynomial k := Polynomial.X ^ 2 - Polynomial.C a
  have hroot : ∀ b : k, b ^ 2 ≠ a := by
    intro b hb
    by_cases hb0 : b = 0
    · simp [hb0] at hb
      exact (RatFunc.X_ne_zero : (RatFunc.X : k) ≠ 0) (by simpa [a] using hb.symm)
    have hdeg := congrArg (fun z : k => RatFunc.intDegree z) hb
    rw [pow_two, RatFunc.intDegree_mul hb0 hb0] at hdeg
    simp [a] at hdeg
    omega
  have hf : Irreducible f := by
    exact X_pow_sub_C_irreducible_of_prime (p := 2) (by decide) hroot
  let : Fact (Irreducible f) := ⟨hf⟩
  let K := AdjoinRoot f
  let : Field K := inferInstance
  let : Algebra k K := inferInstance
  let : CharP K 2 := charP_of_injective_algebraMap
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (Polynomial.degree_pos_of_irreducible hf).ne') 2
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hroot_sq : (AdjoinRoot.root f) ^ 2 = algebraMap k K a := by
    have h := AdjoinRoot.eval₂_root f
    have h' : (AdjoinRoot.root f) ^ 2 - AdjoinRoot.of f a = 0 := by
      simpa [f] using h
    rw [sub_eq_zero] at h'
    change (AdjoinRoot.root f) ^ 2 = AdjoinRoot.of f a
    exact h'
  let : IsPurelyInseparable k K := by
    rw [isPurelyInseparable_iff_pow_mem k 2]
    intro z
    induction z using AdjoinRoot.induction_on with
    | _ p =>
      refine ⟨1, ?_⟩
      change ∃ c : k, algebraMap k K c = (AdjoinRoot.mk f p) ^ 2
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
        obtain ⟨cp, hp⟩ := hp
        obtain ⟨cq, hq⟩ := hq
        refine ⟨cp + cq, ?_⟩
        simp [map_add, add_pow_two, htwo, hp, hq]
      | monomial n c =>
        refine ⟨c ^ 2 * a ^ n, ?_⟩
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        have hpow : (AdjoinRoot.root f ^ n) ^ 2 = (algebraMap k K a) ^ n := by
          rw [pow_two, ← mul_pow, ← pow_two, hroot_sq]
        rw [mul_pow, hpow]
        simp only [pow_two]
        have hc : (algebraMap k K) c = AdjoinRoot.of f c := by
          exact congrArg (fun g : k →+* K => g c)
            (AdjoinRoot.algebraMap_eq (f := f))
        rw [hc]
  refine ⟨k, K, K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨?_, ?_⟩⟩
  · exact ⟨(inferInstance : IsReduced K), (inferInstance : IsIntegrallyClosed K)⟩
  have hroot_not_range : AdjoinRoot.root f ∉ Set.range (algebraMap k K) := by
    rintro ⟨b, hb⟩
    change AdjoinRoot.mk f (Polynomial.C b) = AdjoinRoot.mk f Polynomial.X at hb
    have hdiv : f ∣ Polynomial.C b - Polynomial.X :=
      (AdjoinRoot.mk_eq_mk).mp hb
    have hsmall : (Polynomial.C b - Polynomial.X).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_sub]
      exact Polynomial.natDegree_X_sub_C_le b
    have hq0 : Polynomial.C b - Polynomial.X ≠ 0 := by
      intro hzero
      apply Polynomial.X_sub_C_ne_zero b
      simpa [neg_sub] using congrArg Neg.neg hzero
    have hnat := Polynomial.natDegree_le_of_dvd hdiv hq0
    have hbad : 2 ≤ 1 := by
      calc
        2 = f.natDegree := by simp [f]
        _ ≤ (Polynomial.C b - Polynomial.X).natDegree := hnat
        _ ≤ 1 := hsmall
    omega
  intro hnormal
  rcases hnormal with ⟨hred, _⟩
  let : IsReduced (K ⊗[k] K) := hred
  have hcomp :
      Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap k K) =
        (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K).toRingHom.comp
          (algebraMap k K) := by
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  have heq :
      (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] K) =
        (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K).toRingHom :=
    IsPurelyInseparable.injective_comp_algebraMap k K (K ⊗[k] K) hcomp
  have hmem : AdjoinRoot.root f ∈ Set.range (algebraMap k K) := by
    have hm : AdjoinRoot.root f ∈
        (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] K).eqLocus
          (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K).toRingHom :=
      congrArg (fun g : K →+* K ⊗[k] K => g (AdjoinRoot.root f)) heq
    exact Algebra.IsEffective.eqLocus_includeLeft_includeRight
      (Algebra.IsEffective.of_faithfullyFlat k K) ▸ hm
  exact hroot_not_range hmem

/-- The scheme-theoretic scalar extension whose normalization must be compared with base change. -/
def chapter02FieldBaseChange {X : Scheme.{u}} {k K : Type u} [Field k] [Field K]
    [Algebra k K] (f : X ⟶ Spec (CommRingCat.of k)) : Scheme :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- Normalize an integral component of the scalar extension in its function field.

The reduced/componentwise replacement from the base-change rule is represented by the
`IsIntegral` component hypothesis here; a nonintegral reduced base change must be split into
its integral components before applying this construction. -/
noncomputable def chapter02NormalizationAfterFieldBaseChange
    {X : Scheme.{u}} {k K : Type u} [Field k] [Field K] [Algebra k K]
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral (chapter02FieldBaseChange (K := K) f)]
    [QuasiCompact (chapter02FunctionFieldExtensionMap
      (chapter02FieldBaseChange (K := K) f)
      (chapter02FieldBaseChange (K := K) f).functionField)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap
      (chapter02FieldBaseChange (K := K) f)
      (chapter02FieldBaseChange (K := K) f).functionField)] : Scheme :=
  (chapter02FunctionFieldExtensionMap
    (chapter02FieldBaseChange (K := K) f)
    (chapter02FieldBaseChange (K := K) f).functionField).normalization

/-- Base-change the absolute normalization of `X`.  This is a separate construction from the
normalization of `chapter02FieldBaseChange f`. -/
noncomputable def chapter02FieldBaseChangeOfNormalization
    {X : Scheme.{u}} {k K : Type u} [Field k] [Field K] [Algebra k K]
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X X.functionField)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X X.functionField)] : Scheme :=
  pullback (chapter02AbsoluteNormalizationMap X ≫ f)
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
