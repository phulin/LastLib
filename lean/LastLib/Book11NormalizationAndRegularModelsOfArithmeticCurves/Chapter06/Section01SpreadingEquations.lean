import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section04ClosedSubschemesFromHomogeneousIdeals
import Mathlib.RingTheory.MvPolynomial.Localization

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ### 6.1 Spreading equations -/

abbrev chapter06EquationIdeal
    {A : Type u} [CommRing A] {N : ℕ}
    (E : Chapter06HomogeneousEquations A N) : Ideal (MvPolynomial (Fin (N + 1)) A) :=
  Ideal.span (Set.range E.equation)

/-! The pinned relative-Proj API does not expose the scheme cutout attached to a
finite homogeneous list over an arbitrary base open.  The equation locus below
is therefore expressed as the base change of the canonical homogeneous-ideal
scheme `V_+` from Book 8, while the ambient closed immersion and its comparison
with the supplied cutout are carried as explicit data. -/
structure Chapter06EquationCutoutInterface
    {A : Type u} [CommRing A] {N : ℕ}
    (E : Chapter06HomogeneousEquations A N)
    {S X : Scheme.{u}} (f : X ⟶ S)
    (i : X ⟶ chapter02ProjectiveSpace S N) where
  equationIdealData : Chapter02PolynomialHomogeneousIdealData A N
  equationIdealData_eq :
    equationIdealData.ideal = chapter06EquationIdeal E
  baseMap : S ⟶ Spec (CommRingCat.of A)
  equationLocusEmbedding :
    pullback (chapter02PolynomialVPlusProjection A N equationIdealData) baseMap ⟶
      chapter02ProjectiveSpace S N
  equationLocus_closedImmersion : IsClosedImmersion equationLocusEmbedding
  equationLocus_over :
    equationLocusEmbedding ≫ chapter02ProjectiveSpaceProjection S N =
      pullback.snd (chapter02PolynomialVPlusProjection A N equationIdealData) baseMap
  cutout : Scheme.{u}
  cutoutMap : cutout ⟶ S
  cutoutEmbedding : cutout ⟶ chapter02ProjectiveSpace S N
  cutout_closedImmersion : IsClosedImmersion cutoutEmbedding
  cutout_over : cutoutEmbedding ≫ chapter02ProjectiveSpaceProjection S N = cutoutMap
  cutoutEquationLocusIso :
    cutout ≅ pullback (chapter02PolynomialVPlusProjection A N equationIdealData) baseMap
  cutoutEquationLocusIso_over :
    cutoutEquationLocusIso.hom ≫
        pullback.snd (chapter02PolynomialVPlusProjection A N equationIdealData) baseMap =
      cutoutMap
  cutoutEquationLocusIso_embedding :
    cutoutEquationLocusIso.hom ≫ equationLocusEmbedding = cutoutEmbedding
  carrierIso : cutout ≅ X
  carrierIso_over : carrierIso.hom ≫ f = cutoutMap
  carrierIso_embedding : carrierIso.hom ≫ i = cutoutEmbedding

structure Chapter06SpreadFamily
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C) where
  baseOpen : (Chapter06BaseScheme R).Opens
  open_nonempty : baseOpen ≠ ⊥
  complement_finite : Set.Finite ((baseOpen : Set (Chapter06BaseScheme R))ᶜ)
  baseEquations : Chapter06HomogeneousEquations R E.dimension
  genericEquations : Chapter06HomogeneousEquations (FractionRing R) E.dimension
  clearedEquations : Chapter06ClearedHomogeneousEquations R genericEquations
  baseEquations_eq_cleared : baseEquations = clearedEquations.base
  carrier : Scheme.{u}
  structureMap : carrier ⟶ baseOpen.toScheme
  ambientMap : chapter02ProjectiveSpace baseOpen.toScheme E.dimension ⟶ baseOpen.toScheme
  ambientMap_eq : ambientMap = chapter02ProjectiveSpaceProjection baseOpen.toScheme E.dimension
  embedding : carrier ⟶ chapter02ProjectiveSpace baseOpen.toScheme E.dimension
  closedImmersion : IsClosedImmersion embedding
  over : embedding ≫ ambientMap = structureMap
  projective : chapter04Projective structureMap
  genericMap : Spec (.of (FractionRing R)) ⟶ baseOpen.toScheme
  genericMap_over : genericMap ≫ baseOpen.ι = chapter06GenericBaseMap R
  genericFiber : Chapter06GenericFiberIdentification R C (structureMap ≫ baseOpen.ι)
  locallyOfFiniteType : LocallyOfFiniteType structureMap
  locallyOfFinitePresentation : LocallyOfFinitePresentation structureMap
  equationCutout :
    Chapter06EquationCutoutInterface baseEquations structureMap embedding
  equationCutout_baseMap :
    equationCutout.baseMap = baseOpen.ι
  genericEquationCutout :
    Chapter06EquationCutoutInterface genericEquations C.structureMap E.map
  genericEquationCutout_baseMap :
    genericEquationCutout.baseMap = 𝟙 _

structure Chapter06SpreadFamilyRestriction
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (F G : Chapter06SpreadFamily C E) where
  baseOpen_le : G.baseOpen ≤ F.baseOpen
  iso : ((F.structureMap ≫ F.baseOpen.ι) ⁻¹ᵁ G.baseOpen).toScheme ≅ G.carrier
  over : iso.hom ≫ G.structureMap =
    (F.structureMap ≫ F.baseOpen.ι) ∣_ G.baseOpen
  ambientIso :
    pullback F.ambientMap
        (Scheme.homOfLE (Chapter06BaseScheme R) baseOpen_le) ≅
      chapter02ProjectiveSpace G.baseOpen.toScheme E.dimension
  ambientIso_over :
    ambientIso.hom ≫ G.ambientMap =
      pullback.snd F.ambientMap
        (Scheme.homOfLE (Chapter06BaseScheme R) baseOpen_le)
  restrictedEmbedding :
    ((F.structureMap ≫ F.baseOpen.ι) ⁻¹ᵁ G.baseOpen).toScheme ⟶
      pullback F.ambientMap
        (Scheme.homOfLE (Chapter06BaseScheme R) baseOpen_le)
  restrictedEmbedding_fst :
    restrictedEmbedding ≫
        pullback.fst F.ambientMap
          (Scheme.homOfLE (Chapter06BaseScheme R) baseOpen_le) =
      ((F.structureMap ≫ F.baseOpen.ι) ⁻¹ᵁ G.baseOpen).ι ≫ F.embedding
  restrictedEmbedding_snd :
    restrictedEmbedding ≫
        pullback.snd F.ambientMap
          (Scheme.homOfLE (Chapter06BaseScheme R) baseOpen_le) =
      (F.structureMap ≫ F.baseOpen.ι) ∣_ G.baseOpen
  embedding_compatibility :
    iso.hom ≫ G.embedding = restrictedEmbedding ≫ ambientIso.hom
  baseEquations_eq : G.baseEquations = F.baseEquations
  genericEquations_eq : G.genericEquations = F.genericEquations
  equationIdeal_eq :
    G.equationCutout.equationIdealData.ideal =
      F.equationCutout.equationIdealData.ideal

structure Chapter06GoodSpreadFamily
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    extends Chapter06SpreadFamily C E where
  flat : Flat structureMap
  smooth : Smooth structureMap

noncomputable def chapter06_goodSpreadFamily_to_openModel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {C : Chapter06SmoothProjectiveCurve R}
    {E : Chapter06ProjectiveEmbedding C}
    (G : Chapter06GoodSpreadFamily C E) : Chapter06SmoothProjectiveOpenModel R C :=
  { baseOpen := G.baseOpen
    open_nonempty := G.open_nonempty
    complement_finite := G.complement_finite
    carrier := G.carrier
    structureMap := G.structureMap
    projective := G.projective
    smooth := G.smooth
    genericMap := G.genericMap
    genericMap_over := G.genericMap_over
    genericFiber := G.genericFiber }

theorem chapter06_clear_denominators
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    (G : Chapter06HomogeneousEquations (FractionRing R) E.dimension) :
    Nonempty (Chapter06ClearedHomogeneousEquations R G) := by
  classical
  let : Algebra
      (MvPolynomial (Fin (E.dimension + 1)) R)
      (MvPolynomial (Fin (E.dimension + 1)) (FractionRing R)) :=
    MvPolynomial.algebraMvPolynomial
  let : IsLocalization
      ((nonZeroDivisors R).map
        (MvPolynomial.C : R →+* MvPolynomial (Fin (E.dimension + 1)) R))
      (MvPolynomial (Fin (E.dimension + 1)) (FractionRing R)) :=
    MvPolynomial.isLocalization (nonZeroDivisors R) (FractionRing R)
  let M :=
    (nonZeroDivisors R).map
      (MvPolynomial.C : R →+* MvPolynomial (Fin (E.dimension + 1)) R)
  have hclear (i : G.index) :
      ∃ p : MvPolynomial (Fin (E.dimension + 1)) R, ∃ m : R,
        m ≠ 0 ∧ chapter06PolynomialGenericMap R E.dimension p =
          (algebraMap R (FractionRing R) m) • G.equation i := by
    obtain ⟨⟨p, d⟩, hd⟩ := IsLocalization.surj M (G.equation i)
    rcases d.property with ⟨m, hm, hdm⟩
    refine ⟨p, (m : R), ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero hm
    · rw [← hdm] at hd
      change (algebraMap
        (MvPolynomial (Fin (E.dimension + 1)) R)
        (MvPolynomial (Fin (E.dimension + 1)) (FractionRing R))) p =
          (algebraMap R (FractionRing R) m) • G.equation i
      rw [← hd]
      simp [Algebra.smul_def, mul_comm]
  choose p m hne hpm using hclear
  let base : Chapter06HomogeneousEquations R E.dimension :=
    { index := G.index
      finiteIndex := G.finiteIndex
      degree := G.degree
      equation := p
      homogeneous := by
        intro i
        have hscalar :
            ((algebraMap R (FractionRing R) (m i)) • G.equation i).IsHomogeneous
              (G.degree i) :=
          (MvPolynomial.homogeneousSubmodule (Fin (E.dimension + 1))
            (FractionRing R) (G.degree i)).smul_mem
              (algebraMap R (FractionRing R) (m i)) (G.homogeneous i)
        have hpmap :
            (chapter06PolynomialGenericMap R E.dimension (p i)).IsHomogeneous
              (G.degree i) := by
          rw [hpm i]
          exact hscalar
        exact MvPolynomial.IsHomogeneous.of_map
          (IsFractionRing.injective R (FractionRing R)) hpmap }
  let scalar : G.index → FractionRing R :=
    fun i => algebraMap R (FractionRing R) (m i)
  refine ⟨base, Equiv.refl _, scalar, ?_, ?_⟩
  · intro i h
    apply hne i
    have h' : algebraMap R (FractionRing R) (m i) = 0 := by
      simpa [scalar] using h
    exact (IsFractionRing.injective R (FractionRing R)) (by simpa using h')
  · intro i
    exact hpm i

theorem chapter06_spreading_out
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C) :
    Nonempty (Chapter06SpreadFamily C E) := by
  sorry

theorem chapter06_spread_can_be_made_flat_and_smooth
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    (F : Chapter06SpreadFamily C E) :
    ∃ G : Chapter06GoodSpreadFamily C E,
      Nonempty (Chapter06SpreadFamilyRestriction F G.toChapter06SpreadFamily) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
