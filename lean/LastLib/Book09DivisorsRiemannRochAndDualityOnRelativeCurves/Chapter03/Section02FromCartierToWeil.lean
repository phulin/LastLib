import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section01CodimensionOneCycles

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ## 3.2. From Cartier to Weil -/

/-- Codimension-one points lying in an open. -/
abbrev Chapter03CodimensionOnePointInOpen {X : Scheme.{u}} (U : X.Opens) :=
  {x : X // x ∈ U ∧ Order.coheight x = 1}

/-- The image in the function field of regular functions on a nonempty open. -/
def chapter03SectionImage
    {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} [Nonempty U] :
    Set X.functionField :=
  Set.range (X.germToFunctionField U).hom

/-- The image of a stalk in the function field. -/
def chapter03StalkImage
    {X : Scheme.{u}} [IsIntegral X] (x : X) : Set X.functionField :=
  Set.range (algebraMap (X.presheaf.stalk x) X.functionField)

/--
The normal intersection description of the structure sheaf inside the
function field.  The index is restricted to codimension-one points of the
open, matching the textbook notation `U^(1)`.
-/
theorem chapter03_structureSheaf_intersection_codimension_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] (U : X.Opens) [Nonempty U] :
    chapter03SectionImage (U := U) =
      ⋂ x : Chapter03CodimensionOnePointInOpen U, chapter03StalkImage x.1 := by
  sorry

def chapter03NoCodimensionOnePoles
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (f : X.functionField) : Prop :=
  f ∈ ⋂ x : Chapter03CodimensionOnePointInOpen U, chapter03StalkImage x.1

theorem chapter03_no_codimension_one_poles_iff_section
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] (U : X.Opens) [Nonempty U] (f : X.functionField) :
    chapter03NoCodimensionOnePoles U f ↔
      ∃ g : Γ(X, U), X.germToFunctionField U g = f := by
  rw [chapter03NoCodimensionOnePoles]
  rw [← chapter03_structureSheaf_intersection_codimension_one U]
  rfl

/-- A rational function and its inverse with no codimension-one poles are units. -/
theorem chapter03_no_codimension_one_zero_or_pole_is_unit
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] (U : X.Opens) [Nonempty U] (f : X.functionField)
    (hf : f ≠ 0) (h₀ : chapter03NoCodimensionOnePoles U f)
    (h₁ : chapter03NoCodimensionOnePoles U f⁻¹) :
    ∃ g : Γ(X, U), IsUnit g ∧ X.germToFunctionField U g = f := by
  obtain ⟨g, hg⟩ := (chapter03_no_codimension_one_poles_iff_section U f).mp h₀
  obtain ⟨h, hh⟩ := (chapter03_no_codimension_one_poles_iff_section U f⁻¹).mp h₁
  refine ⟨g, ?_, hg⟩
  exact isUnit_iff_exists.mpr
    ⟨h,
      by
        apply Scheme.germToFunctionField_injective X U
        simp [map_mul, hg, hh, hf],
      by
        apply Scheme.germToFunctionField_injective X U
        simp [map_mul, hg, hh, hf]⟩

theorem chapter03_cartier_to_weil_map_zero
    {X : Scheme.{u}} [Chapter03CartierDivisorTheory X] :
    chapter03CartierDivisorToWeil X 0 = 0 := by
  exact map_zero _

theorem chapter03_cartier_to_weil_map_add
    {X : Scheme.{u}} [Chapter03CartierDivisorTheory X]
    (D E : Chapter03CartierDivisor X) :
    chapter03CartierDivisorToWeil X (D + E) =
      chapter03CartierDivisorToWeil X D + chapter03CartierDivisorToWeil X E := by
  exact map_add _ D E

theorem chapter03_cartier_to_weil_map_neg
    {X : Scheme.{u}} [Chapter03CartierDivisorTheory X]
    (D : Chapter03CartierDivisor X) :
    chapter03CartierDivisorToWeil X (-D) =
      -chapter03CartierDivisorToWeil X D := by
  exact map_neg _ D

/-- The Cartier divisor map is injective on locally noetherian normal integral schemes. -/
theorem chapter03_cartier_to_weil_injective
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] [T : Chapter03CartierDivisorTheory X] :
    Function.Injective (chapter03CartierDivisorToWeil X) := by
  intro D E h
  apply T.canonicalLocalPresentation.injective
  apply Subtype.ext
  calc
    (T.canonicalLocalPresentation D).1 = chapter03CartierDivisorToWeil X D :=
      (chapter03_cartierDivisorToWeil_eq_canonicalLocalPresentation D).symm
    _ = chapter03CartierDivisorToWeil X E := h
    _ = (T.canonicalLocalPresentation E).1 :=
      chapter03_cartierDivisorToWeil_eq_canonicalLocalPresentation E

/-- Surjectivity of the Cartier--Weil map is equivalent to local factoriality. -/
theorem chapter03_cartier_to_weil_surjective_iff_locallyFactorial
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] [Chapter03CartierDivisorTheory X] :
    Function.Surjective (chapter03CartierDivisorToWeil X) ↔
      Chapter03LocallyFactorial X := by
  sorry

/-- A prime divisor is Cartier exactly when its height-one ideal is locally principal. -/
theorem chapter03_primeDivisor_isCartier_iff_locallyPrincipal
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] [Chapter03CartierDivisorTheory X]
    (P : Chapter03PrimeDivisor X) :
    (∃ D : Chapter03CartierDivisor X,
      chapter03CartierDivisorToWeil X D = chapter03PrimeDivisorCycle P 1) ↔
      chapter03PrimeDivisorLocallyPrincipal P := by
  sorry

/-- The height-one ideal of a prime divisor is principal on a regular scheme. -/
theorem chapter03_regular_height_one_ideal_is_locallyPrincipal
    {X : Scheme.{u}} [IsNoetherian X] [Chapter03Regular X]
    (P : Chapter03PrimeDivisor X) :
    chapter03PrimeDivisorLocallyPrincipal P := by
  sorry

/-- Regular noetherian schemes are locally factorial. -/
theorem chapter03_regular_noetherian_is_locallyFactorial
    (X : Scheme.{u}) [IsNoetherian X] [Chapter03Regular X] :
    Chapter03LocallyFactorial X := by
  sorry

/-- Every Weil divisor on a regular noetherian integral scheme is Cartier. -/
theorem chapter03_regular_noetherian_integral_cartier_to_weil_surjective
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Regular X]
    [Chapter03Normal X] [Chapter03CartierDivisorTheory X] :
    Function.Surjective (chapter03CartierDivisorToWeil X) := by
  apply (chapter03_cartier_to_weil_surjective_iff_locallyFactorial (X := X)).2
  exact chapter03_regular_noetherian_is_locallyFactorial X

theorem chapter03_regular_noetherian_integral_cartier_to_weil_bijective
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] [Chapter03Regular X] [Chapter03CartierDivisorTheory X] :
    Function.Bijective (chapter03CartierDivisorToWeil X) := by
  exact ⟨chapter03_cartier_to_weil_injective (X := X),
    chapter03_regular_noetherian_integral_cartier_to_weil_surjective (X := X)⟩

/-- The divisor dictionary as a (noncomputable) equivalence of underlying types. -/
noncomputable def chapter03CartierWeilEquiv
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] [Chapter03Regular X] [Chapter03CartierDivisorTheory X] :
    Chapter03CartierDivisor X ≃ Chapter03WeilDivisor X :=
  Equiv.ofBijective (chapter03CartierDivisorToWeil X)
    (chapter03_regular_noetherian_integral_cartier_to_weil_bijective (X := X))

/-- A chosen Cartier representative, corresponding to local generators of height-one primes. -/
noncomputable def chapter03CartierRepresentative
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] [Chapter03Regular X] [Chapter03CartierDivisorTheory X]
    (D : Chapter03WeilDivisor X) : Chapter03CartierDivisor X :=
  Classical.choose
    (chapter03_regular_noetherian_integral_cartier_to_weil_surjective (X := X) D)

theorem chapter03CartierRepresentative_toWeil
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] [Chapter03Regular X] [Chapter03CartierDivisorTheory X]
    (D : Chapter03WeilDivisor X) :
    chapter03CartierDivisorToWeil X (chapter03CartierRepresentative D) = D := by
  exact Classical.choose_spec
    (chapter03_regular_noetherian_integral_cartier_to_weil_surjective (X := X) D)

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
