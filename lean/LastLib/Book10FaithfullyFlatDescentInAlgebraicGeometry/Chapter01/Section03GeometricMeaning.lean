import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Dependencies
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# 1.3 The geometric meaning

The scheme-level predicates below keep flatness, surjectivity, quasi-compactness, and local finite
presentation separate.  The final family-refinement interface is intentionally small: the detailed
covering theory is developed in the next chapter, but the finite-control hypothesis is already
needed to state the warning in this chapter.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01

noncomputable section

/-- A faithfully flat morphism of schemes. -/
def Chapter01FaithfullyFlatMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ Surjective p

/-- An fpqc morphism, i.e. a faithfully flat quasi-compact morphism. -/
def Chapter01FpqcMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Chapter01FaithfullyFlatMorphism p ∧ QuasiCompact p

/-- An fppf morphism, i.e. a flat morphism locally of finite presentation. -/
def Chapter01FppfMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ LocallyOfFinitePresentation p

/-- A surjective fppf morphism. -/
def Chapter01FppfCover {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Chapter01FppfMorphism p ∧ Surjective p

theorem chapter01_flat_morphism_iff_stalk_maps {T S : Scheme.{u}} (p : T ⟶ S) :
    Flat p ↔ ∀ x, (p.stalkMap x).hom.Flat :=
  Flat.iff_flat_stalkMap p

theorem chapter01_fpqcMorphism_of_fppfCover_of_quasiCompact
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter01FppfCover p)
    (hpqc : QuasiCompact p) : Chapter01FpqcMorphism p := by
  exact ⟨⟨hp.1.1, hp.2⟩, hpqc⟩

theorem chapter01_specMap_faithfullyFlat_iff
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Chapter01FaithfullyFlatMorphism (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  simpa [Chapter01FaithfullyFlatMorphism] using
    (flat_and_surjective_SpecMap_iff f)

theorem chapter01_specMap_ringHom_faithfullyFlat_iff
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Chapter01FaithfullyFlatMorphism (chapter01SpecMap f) ↔ f.FaithfullyFlat := by
  simpa [chapter01SpecMap, Chapter01FaithfullyFlatMorphism] using
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f))

/- LOCAL_DEPENDENCY_GUESS: the detailed fpqc/fppf family refinement construction is supplied by
Chapter 2.  This chapter records the weakest witness needed for its forward reference. -/
theorem chapter01_surjective_fppf_morphism_has_fpqc_family_refinement
    {T S : Scheme.{u}} (p : T ⟶ S) (hp : Chapter01FppfMorphism p) (hs : Surjective p) :
    Nonempty (Chapter01FpqcFamilyRefinement p) := by
  let _ : Flat p := hp.1
  let _ : LocallyOfFinitePresentation p := hp.2
  refine ⟨{
    index := ULift Unit
    source := fun _ => T
    lift := fun _ => 𝟙 T
    map := fun _ => p
    factor := fun _ => by simp
    flat := fun _ => inferInstance
    finite_reduction := ?_ }⟩
  intro U hU
  obtain ⟨V, hV, hVimage⟩ :=
    p.isOpenMap.exists_opens_image_eq_of_prespectralSpace p.continuous
      (by
        intro x _
        exact hs.surj x)
      U.2 hU
  refine ⟨{ULift.up ()}, (fun _ => V), ?_, ?_, ?_⟩
  · intro i
    simpa using hV
  · intro i y
    have hy : p y ∈ p '' (V : Set T) := ⟨y, y.property, rfl⟩
    rw [hVimage] at hy
    exact hy
  · intro x
    have hx : x.1 ∈ p '' (V : Set T) := by
      rw [hVimage]
      exact x.property
    obtain ⟨y, hy, hpy⟩ := hx
    refine ⟨⟨ULift.up (), by simp⟩, ⟨y, hy⟩, ?_⟩
    exact hpy

/-- A finite locally free surjective morphism is the cover used in the examples. -/
def Chapter01FiniteLocallyFreeCover {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Nonempty T ∧ IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p

theorem chapter01_finiteLocallyFreeCover_isFaithfullyFlat
    {T S : Scheme.{u}} {p : T ⟶ S} (hp : Chapter01FiniteLocallyFreeCover p) :
    Chapter01FaithfullyFlatMorphism p := by
  exact ⟨hp.2.2.1, hp.2.2.2.2⟩

theorem chapter01_fieldExtension_faithfullyFlat
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    (algebraMap K L).FaithfullyFlat := by
  refine (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).2 ⟨
    RingHom.Flat.of_isField (Field.toIsField K) (algebraMap K L), ?_⟩
  intro p
  obtain rfl := Subsingleton.elim p (⊥ : PrimeSpectrum K)
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective K L)

theorem chapter01_fieldExtension_spec_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Chapter01FaithfullyFlatMorphism
      (chapter01SpecMap (algebraMap K L)) := by
  apply (chapter01_specMap_ringHom_faithfullyFlat_iff (algebraMap K L)).2
  exact chapter01_fieldExtension_faithfullyFlat K L

/-- The coproduct of the members of an open cover is the corresponding single algebraic map. -/
noncomputable def chapter01OpenCoverSigmaMap {S : Scheme.{u}} (𝒰 : S.OpenCover) :
    (∐ 𝒰.X) ⟶ S :=
  Sigma.desc 𝒰.f

theorem chapter01_openCover_component_flat {S : Scheme.{u}} (𝒰 : S.OpenCover)
    (i : 𝒰.I₀) : Flat (𝒰.f i) := by
  infer_instance

theorem chapter01_openCover_sigma_isFaithfullyFlat {S : Scheme.{u}} (𝒰 : S.OpenCover) :
    Chapter01FaithfullyFlatMorphism (chapter01OpenCoverSigmaMap 𝒰) := by
  change Flat (Sigma.desc 𝒰.f) ∧ Surjective (Sigma.desc 𝒰.f)
  constructor
  · let _ : ∀ i, Flat (𝒰.f i) := fun i => chapter01_openCover_component_flat 𝒰 i
    infer_instance
  · exact Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range

/-- The localization map is flat even before one asks whether it covers the target. -/
theorem chapter01_localization_flat
    (A : Type u) [CommRing A] (f : A) :
    RingHom.Flat (algebraMap A (Localization.Away f)) := by
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))

/-- The product of two localizations packages the cover `D(f) ∪ D(g)` into one ring map. -/
def chapter01LocalizationProductMap
    (A : Type u) [CommRing A] (f g : A) :
    A →+* Localization.Away f × Localization.Away g :=
  (algebraMap A (Localization.Away f)).prod (algebraMap A (Localization.Away g))

def Chapter01LocalizationProductCoverCondition
    (A : Type u) [CommRing A] (f g : A) : Prop :=
  Ideal.span ({f, g} : Set A) = ⊤

theorem chapter01_localization_product_faithfullyFlat
    (A : Type u) [CommRing A] (f g : A)
    (hfg : Chapter01LocalizationProductCoverCondition A f g) :
    RingHom.FaithfullyFlat (chapter01LocalizationProductMap A f g) := by
  unfold Chapter01LocalizationProductCoverCondition at hfg
  refine (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).2 ⟨?_, ?_⟩
  · have hmap : chapter01LocalizationProductMap A f g =
        algebraMap A (Localization.Away f × Localization.Away g) := by
      ext a <;> rfl
    rw [hmap, RingHom.flat_algebraMap_iff]
    have hf : Module.Flat A (Localization.Away f) :=
      RingHom.flat_algebraMap_iff.mp (chapter01_localization_flat A f)
    have hg : Module.Flat A (Localization.Away g) :=
      RingHom.flat_algebraMap_iff.mp (chapter01_localization_flat A g)
    rw [Module.Flat.iff_rTensor_injectiveₛ]
    intro P _ _ Q
    let eQ := TensorProduct.prodRight A A Q (Localization.Away f) (Localization.Away g)
    let eP := TensorProduct.prodRight A A P (Localization.Away f) (Localization.Away g)
    have hQf : Function.Injective
        (Q.subtype.rTensor (Localization.Away f)) :=
      (Module.Flat.iff_rTensor_injectiveₛ.mp hf Q)
    have hQg : Function.Injective
        (Q.subtype.rTensor (Localization.Away g)) :=
      (Module.Flat.iff_rTensor_injectiveₛ.mp hg Q)
    have hcomm :
        eP.toLinearMap.comp (Q.subtype.rTensor
          (Localization.Away f × Localization.Away g)) =
          ((Q.subtype.rTensor (Localization.Away f)).prodMap
            (Q.subtype.rTensor (Localization.Away g))).comp eQ.toLinearMap := by
      apply TensorProduct.ext'
      intro q m
      rfl
    intro x y hxy
    apply eQ.injective
    have hxy' := congrArg (fun z => eP z) hxy
    have hxcomm := congrArg (fun z => z x) hcomm
    have hycomm := congrArg (fun z => z y) hcomm
    simp only [LinearMap.comp_apply] at hxcomm hycomm
    change eP.toLinearMap ((Q.subtype.rTensor
      (Localization.Away f × Localization.Away g)) x) =
      eP.toLinearMap ((Q.subtype.rTensor
        (Localization.Away f × Localization.Away g)) y) at hxy'
    rw [hxcomm, hycomm] at hxy'
    apply Prod.ext
    · apply hQf
      simpa only [LinearMap.prodMap_apply, LinearEquiv.coe_coe] using congrArg Prod.fst hxy'
    · apply hQg
      simpa only [LinearMap.prodMap_apply, LinearEquiv.coe_coe] using congrArg Prod.snd hxy'
  · intro p
    by_cases hf : f ∈ p.asIdeal
    · by_cases hg : g ∈ p.asIdeal
      · have htop : (⊤ : Ideal A) ≤ p.asIdeal := by
          rw [← hfg]
          exact Ideal.span_le.2 (by
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl
            · exact hf
            · exact hg)
        exact False.elim (p.2.ne_top (top_le_iff.mp htop))
      · have hrange : p ∈ Set.range
            (PrimeSpectrum.comap (algebraMap A (Localization.Away g))) := by
          rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
          exact (PrimeSpectrum.mem_basicOpen g p).2 hg
        obtain ⟨q, hq⟩ := hrange
        refine ⟨(PrimeSpectrum.primeSpectrumProd (Localization.Away f)
          (Localization.Away g)).symm (Sum.inr q), ?_⟩
        apply PrimeSpectrum.ext
        rw [PrimeSpectrum.comap_asIdeal,
          PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal]
        ext a
        simp only [Ideal.mem_comap, Ideal.mem_prod]
        change (chapter01LocalizationProductMap A f g a).1 ∈ (⊤ : Ideal _) ∧
          (chapter01LocalizationProductMap A f g a).2 ∈ q.asIdeal ↔ a ∈ p.asIdeal
        have hq' : Ideal.comap (algebraMap A (Localization.Away g)) q.asIdeal = p.asIdeal := by
          simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
        rw [← hq']
        simp only [chapter01LocalizationProductMap, RingHom.prod_apply]
        constructor
        · rintro ⟨_, ha⟩
          exact ha
        · intro ha
          exact ⟨by simp, ha⟩
    · have hrange : p ∈ Set.range
          (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
        exact (PrimeSpectrum.mem_basicOpen f p).2 hf
      obtain ⟨q, hq⟩ := hrange
      refine ⟨(PrimeSpectrum.primeSpectrumProd (Localization.Away f)
        (Localization.Away g)).symm (Sum.inl q), ?_⟩
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal,
        PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_prod]
      change (chapter01LocalizationProductMap A f g a).1 ∈ q.asIdeal ∧
        (chapter01LocalizationProductMap A f g a).2 ∈ (⊤ : Ideal _) ↔ a ∈ p.asIdeal
      have hq' : Ideal.comap (algebraMap A (Localization.Away f)) q.asIdeal = p.asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
      rw [← hq']
      simp only [chapter01LocalizationProductMap, RingHom.prod_apply]
      constructor
      · rintro ⟨ha, _⟩
        exact ha
      · intro ha
        exact ⟨ha, by simp⟩

/- LOCAL_DEPENDENCY_GUESS: pinned Mathlib supplies adic-completion flatness but not the
faithfulness theorem in this generality; the displayed statement is the standard noetherian
Jacobson-radical bridge required by the source. -/
theorem chapter01_adicCompletion_faithfullyFlat_of_noetherian_of_le_jacobson
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) :
    RingHom.FaithfullyFlat (algebraMap A (AdicCompletion I A)) := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  refine (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A
    (AdicCompletion I A)).2 ⟨?_, ?_⟩
  · infer_instance
  · intro J hJ
    rw [Ideal.smul_top_eq_map] at hJ
    have hmap : Ideal.map (algebraMap A (AdicCompletion I A)) J = ⊤ :=
      (Submodule.restrictScalars_eq_top_iff A (AdicCompletion I A) (AdicCompletion I A)
        (p := Ideal.map (algebraMap A (AdicCompletion I A)) J)).mp hJ
    have hquot : Ideal.map (Ideal.Quotient.mk I) J = ⊤ := by
      rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk,
        ← Ideal.map_map, hmap, Ideal.map_top]
    have hsup : I ⊔ J = ⊤ := by
      rw [← Ideal.comap_map_quotientMk I J, hquot]
      simp
    apply Ideal.jacobson_eq_top_iff.mp
    apply top_unique
    rw [← hsup]
    exact sup_le (hI.trans (Ideal.jacobson_mono bot_le)) Ideal.le_jacobson

theorem chapter01_adicCompletion_flat_of_noetherian
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    Module.Flat A (AdicCompletion I A) := by
  infer_instance

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
