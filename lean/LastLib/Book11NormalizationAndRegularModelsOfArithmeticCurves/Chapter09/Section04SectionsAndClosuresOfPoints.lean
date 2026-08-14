import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09.Section03DominatingFinitelyManyModels

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ## 9.4. Sections and closures of points -/

theorem chapter09_K_point_extends_to_section
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09KPoint C) :
    Nonempty (Chapter09SectionExtension X P) := by
  sorry

theorem chapter09_K_point_extends_to_section_over_normal_base
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    (hS : Chapter01NormalScheme S)
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09KPoint C) :
    Nonempty (Chapter09SectionExtension X P) := by
  sorry

theorem chapter09_section_extension_unique
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09KPoint C)
    (σ τ : Chapter09SectionExtension X P) :
    σ.section.map = τ.section.map := by
  sorry

theorem chapter09_section_extension_unique_as_data
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09KPoint C)
    (σ τ : Chapter09SectionExtension X P) :
    σ = τ := by
  apply chapter09_sectionExtension_ext
  exact chapter09_section_extension_unique X P σ τ

theorem chapter09_base_normalization_in_residue_field_exists
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    (B : Chapter09ExcellentDedekindBase S K)
    {C : Chapter09SmoothProjectiveCurve K}
    (P : Chapter09ClosedPointOverK C L) :
    Nonempty (Chapter09BaseNormalization (L := L) B) := by
  sorry

theorem chapter09_base_normalization_is_finite
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    (N : Chapter09BaseNormalization (L := L) B) :
    IsFinite N.map :=
  N.finite

theorem chapter09_residue_point_extends_over_base_normalization
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09ClosedPointOverK C L)
    (N : Chapter09BaseNormalization (L := L) B) :
    Nonempty (Chapter09ResidueSectionExtension X P N) := by
  sorry

theorem chapter09_horizontalClosure_normalization_is_baseNormalization
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) :
    Chapter09HorizontalClosureNormalizationStatement H := by
  sorry

theorem chapter09_section_is_effective_cartier
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : Chapter09RegularSurface X)
    (hf : Chapter01ArithmeticSurface f)
    (σ : Chapter09Section f) :
    Nonempty (Chapter09SectionCartierData σ) := by
  sorry

theorem chapter09_section_closed_point_has_dimension_two_and_local_parameter
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : Chapter09RegularSurface X)
    (hf : Chapter01ArithmeticSurface f)
    (σ : Chapter09Section f)
    (D : Chapter09SectionCartierData σ)
    {x : X} (hx : x ∈ Set.range σ.map)
    (hclosed : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = 2 ∧
      chapter09SectionLocalParameter D x := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09
