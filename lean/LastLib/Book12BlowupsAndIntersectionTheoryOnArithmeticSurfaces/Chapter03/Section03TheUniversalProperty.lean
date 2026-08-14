import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Section01ConstructionAndProjectivity

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
open scoped AlgebraicGeometry

/-! ## 3.3. The universal property -/

/- The two predicates below retain the source's local-generator language while making the
regularity hypothesis explicit.  The second one is definitionally the earlier blowup API's
invertible-ideal predicate. -/
def Chapter03LocallyPrincipalIdeal
    {X : Scheme.{u}} (J : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    J.ideal U = Ideal.span {a}

def Chapter03LocallyPrincipalRegularIdeal
    {X : Scheme.{u}} (J : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    J.ideal U = Ideal.span {a} ∧ IsRegular a

theorem chapter03_locally_principal_regular_iff_invertible
    {X : Scheme.{u}} (J : X.IdealSheafData) :
    Chapter03LocallyPrincipalRegularIdeal J ↔ Chapter07IsInvertibleIdeal J :=
  Iff.rfl

/-- The source is contained in the center when every point maps into the ideal support. -/
def Chapter03SourceContainedInCenter
    {T X : Scheme.{u}} (I : Chapter03CoherentIdeal X) (g : T ⟶ X) : Prop :=
  (Set.univ : Set T) ⊆ I.ideal.support.preimage g.continuous

abbrev chapter03CenterComplement
    {X : Scheme.{u}} (I : X.IdealSheafData) : X.Opens :=
  I.support.compl

theorem chapter03_regular_pullback_not_source_contained_in_center
    {T X : Scheme.{u}} (I : Chapter03CoherentIdeal X) (g : T ⟶ X)
    (hT : Nonempty T)
    (hI : Chapter03LocallyPrincipalRegularIdeal (I.ideal.comap g)) :
    ¬ Chapter03SourceContainedInCenter I g := by
  sorry

abbrev Chapter03ChartRatio
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i j : ι) :=
  chapter02ChartRatio f i j

theorem chapter03_chart_ratio_mul_denominator
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i j : ι) :
    algebraMap R (Localization.Away (f i)) (f i) *
        Chapter03ChartRatio f i j =
      algebraMap R (Localization.Away (f i)) (f j) := by
  exact chapter02_chart_ratio_mul_denominator f i j

/- The regular local generator is precisely the input needed to use the canonical blowup
universal property.  The comparison in `Chapter03BlowupPresentation` transports that property
from the earlier book-facing carrier to the relative-Proj carrier. -/
theorem chapter03_theorem_3_1_universal_property
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) {T : Scheme.{u}} (g : T ⟶ X)
    (hI : Chapter03LocallyPrincipalRegularIdeal (I.ideal.comap g)) :
    ∃! u : T ⟶ B.carrier, u ≫ B.projection = g := by
  sorry

theorem chapter03_blowup_factor_exists
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) {T : Scheme.{u}} (g : T ⟶ X)
    (hI : Chapter03LocallyPrincipalRegularIdeal (I.ideal.comap g)) :
    ∃ u : T ⟶ B.carrier, u ≫ B.projection = g := by
  exact (chapter03_theorem_3_1_universal_property B g hI).exists

theorem chapter03_blowup_factor_unique
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) {T : Scheme.{u}} (g : T ⟶ X)
    (hI : Chapter03LocallyPrincipalRegularIdeal (I.ideal.comap g))
    {u v : T ⟶ B.carrier} (hu : u ≫ B.projection = g) (hv : v ≫ B.projection = g) :
    u = v := by
  sorry

theorem chapter03_blowup_of_invertible_ideal_isIso
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I)
    (hI : Chapter03LocallyPrincipalRegularIdeal I.ideal) :
    IsIso B.projection := by
  sorry

/-! ### The quotient formulation -/

/- A finitely generated quasi-coherent module is the module-facing input for the general relative
Proj universal property.  The ideal case is recovered by the earlier ideal-module presentation. -/
structure Chapter03FinitelyGeneratedModule (X : Scheme.{u}) where
  carrier : X.Modules
  isQuasicoherent : carrier.IsQuasicoherent
  finitelyGenerated : carrier.IsFiniteType

noncomputable def chapter03ModuleQuotientData
    {X : Scheme.{u}} (M : Chapter03FinitelyGeneratedModule X) :
    Chapter01ProjectiveBundleData X
      { carrier := M.carrier, isQuasicoherent := M.isQuasicoherent } :=
  chapter01ProjectiveBundleData X
    { carrier := M.carrier, isQuasicoherent := M.isQuasicoherent }

noncomputable def chapter03_relative_proj_represents_invertible_module_quotients
    {X : Scheme.{u}} (M : Chapter03FinitelyGeneratedModule X)
    {T : Scheme.{u}} (g : T ⟶ X) :
    {u : T ⟶ (chapter03ModuleQuotientData M).scheme //
        u ≫ (chapter03ModuleQuotientData M).projection = g} ≃
      Chapter01InvertibleQuotientClass M.carrier g := by
  exact (chapter03ModuleQuotientData M).universalProperty g

theorem chapter03_relative_proj_quotient_naturality
    {X : Scheme.{u}} (M : Chapter03FinitelyGeneratedModule X)
    {T U : Scheme.{u}} (g : T ⟶ X) (h : U ⟶ T)
    (u : {u : T ⟶ (chapter03ModuleQuotientData M).scheme //
      u ≫ (chapter03ModuleQuotientData M).projection = g}) :
    ∃ p : Chapter01InvertibleQuotient M.carrier g,
      (chapter03ModuleQuotientData M).universalProperty g u =
          chapter01InvertibleQuotientClassMk p ∧
        (chapter03ModuleQuotientData M).universalProperty (h ≫ g)
            ⟨h ≫ u.1, by simp only [Category.assoc, u.2]⟩ =
          chapter01InvertibleQuotientClassMk
            (chapter01PullbackInvertibleQuotientAlong g h p) := by
  sorry

/-! ### Consequences for maps -/

def Chapter03DominantMap {T X : Scheme.{u}} (g : T ⟶ X) : Prop :=
  Dense (Set.range g)

/- The target chart is part of the coordinate data.  Its section map is induced by the displayed
map into the target chart, while the ratio equations are equations in the source chart ring. -/
structure Chapter03GeneratorRatioCoordinateData
    {X Y : Scheme.{u}} (I : Chapter03CoherentIdeal X)
    (g : (chapter03CenterComplement I.ideal).toScheme ⟶ Y) where
  targetChart : Y.Opens
  targetChart_affine : IsAffineOpen targetChart
  targetChartMap :
    (chapter03CenterComplement I.ideal).toScheme ⟶ targetChart.toScheme
  targetChartMap_over : targetChartMap ≫ targetChart.ι = g
  generatorIndex : Type v
  denominator : generatorIndex
  targetGenerators : generatorIndex → Γ(targetChart.toScheme, ⊤)
  sourceGenerators : generatorIndex →
    Γ((chapter03CenterComplement I.ideal).toScheme, ⊤)
  sourceGenerators_are_pullbacks :
    ∀ i, sourceGenerators i =
      (targetChartMap.appLE (⊤ : targetChart.toScheme.Opens)
        (⊤ : (chapter03CenterComplement I.ideal).toScheme.Opens) (by simp)).hom
        (targetGenerators i)
  denominator_is_unit :
    IsUnit (sourceGenerators denominator)
  ratios : generatorIndex →
    Γ((chapter03CenterComplement I.ideal).toScheme, ⊤)
  ratio_equations :
    ∀ i, sourceGenerators denominator * ratios i = sourceGenerators i

structure Chapter03RationalMapByGeneratorRatios
    {X Y : Scheme.{u}} where
  centerIdeal : Chapter03CoherentIdeal X
  mapOnCenterComplement :
    (chapter03CenterComplement centerIdeal.ideal).toScheme ⟶ Y
  coordinates :
    Chapter03GeneratorRatioCoordinateData.{u, v} centerIdeal mapOnCenterComplement

/- The inverse of the restriction is available because the blowup is an isomorphism off the
center.  This is the canonical open part on which a resolved map must agree with the original
rational map. -/
noncomputable def chapter03BlowupComplementInclusion
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X} (B : Chapter03Blowup I) :
    (chapter03CenterComplement I.ideal).toScheme ⟶ B.carrier := by
  letI : IsIso (chapter03BlowupRestriction B I.ideal.support.compl) := B.off_center
  exact inv (chapter03BlowupRestriction B I.ideal.support.compl) ≫
    (B.projection ⁻¹ᵁ I.ideal.support.compl).ι

structure Chapter03RationalMapResolutionData
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
  (B : Chapter03Blowup I)
  (mapOnCenterComplement : (chapter03CenterComplement I.ideal).toScheme ⟶ Y) where
  resolvedMap : B.carrier ⟶ Y

  /-- The resolved morphism restricts to the original morphism on the complement of the center. -/
  agreesOnTheBlowupComplement :
    chapter03BlowupComplementInclusion B ≫ resolvedMap = mapOnCenterComplement

/- A ratio presentation for an arbitrary target is not by itself an extension theorem: one must
also specify a projective target presentation and the relations that make the ratios a quotient.
The universal property above is the precise extension statement retained here; a target-specific
ratio corollary can be added once those data are available. -/

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03
