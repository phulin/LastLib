import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05.Section03HorizontalAndVerticalGeometry
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Section03NormalSurfacesNeedNotBeRegular
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Section04JacobianAndFiberwiseCriteria

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open scoped AlgebraicGeometry BigOperators TensorProduct

noncomputable section

universe u v

/-! ### 5.4 Local equations over a discrete valuation ring -/

abbrev chapter05DVRPolynomialRing
    (R : Type u) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin n) R

abbrev chapter05AffineLineRing (R : Type u) [CommRing R] :=
  chapter05DVRPolynomialRing R 1

def chapter05AffineLineStructureMap
    (R : Type u) [CommRing R] :
    Scheme.Spec (CommRingCat.of (chapter05AffineLineRing R)) ⟶
      Scheme.Spec (CommRingCat.of R) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (algebraMap R (chapter05AffineLineRing R)))

def chapter05AffineLineSpecialFiberRing
    (R : Type u) [CommRing R] [IsLocalRing R] : Type u :=
  chapter05AffineLineRing R ⊗[R] IsLocalRing.ResidueField R

def Chapter05AffineLineLocalEquationProfile
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] : Prop :=
  Smooth (chapter05AffineLineStructureMap R) ∧
    Chapter04RegularScheme
      (Scheme.Spec (CommRingCat.of (chapter05AffineLineRing R)))

theorem chapter05_affine_line_is_smooth_and_regular
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Chapter05AffineLineLocalEquationProfile R := by
  sorry

theorem chapter05_affine_line_special_fiber_is_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∀ s : Scheme.Spec (CommRingCat.of R),
      Smooth ((chapter05AffineLineStructureMap R).fiberToSpecResidueField s) := by
  sorry

/-! The basic semistable equation `xy - π`.  Chapter 4 already exposes the
canonical quotient, coordinates, node, and flatness predicates. -/

abbrev chapter05NodeRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter04DvrNodeRing R π

abbrev chapter05NodeStructureMap
    (R : Type u) [CommRing R] (π : R) :=
  chapter04DvrNodeStructureMap R π

abbrev chapter05NodeCoordinate
    (R : Type u) [CommRing R] (π : R) (i : Fin 2) :=
  chapter04DvrNodeCoordinate R π i

theorem chapter05_node_equation
    (R : Type u) [CommRing R] (π : R) :
    chapter05NodeCoordinate R π 0 * chapter05NodeCoordinate R π 1 =
      algebraMap R (chapter05NodeRing R π) π := by
  exact chapter04_dvr_node_equation R π

theorem chapter05_node_is_regular_flat_with_nodal_special_fiber
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (hprime : (chapter04DvrNodeMaximalIdeal R π).IsPrime) :
    Chapter04DvrNodeRegularAtNode R π hprime ∧
      Chapter04DvrNodeFlatOverBase R π ∧
      Chapter04DvrNodeMorphismFlat R π ∧
      Chapter04DvrNodeSpecialFiberNodal R ∧
      ¬ Chapter04DvrNodeSmoothAtNode R π hprime ∧
      ¬ Smooth (chapter05NodeStructureMap R π) := by
  exact chapter04_dvr_node_regular_flat_nodal_not_smooth R π hπ hprime

/-! The thickness equation `xy = π^n`, for `n > 1`. -/

def chapter05ThicknessEquation
    (R : Type u) [CommRing R] (π x y : R) (n : ℕ) : Prop :=
  x * y = π ^ n

def chapter05ThicknessRelationIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (chapter05DVRPolynomialRing R 2) :=
  Ideal.span ({
    MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (π ^ n)
  } : Set (chapter05DVRPolynomialRing R 2))

abbrev chapter05ThicknessRing
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  chapter05DVRPolynomialRing R 2 ⧸ chapter05ThicknessRelationIdeal R π n

def chapter05ThicknessStructureMap
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Scheme.Spec (CommRingCat.of (chapter05ThicknessRing R π n)) ⟶
      Scheme.Spec (CommRingCat.of R) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (algebraMap R (chapter05ThicknessRing R π n)))

def chapter05ThicknessCoordinate
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (i : Fin 2) :
    chapter05ThicknessRing R π n :=
  Ideal.Quotient.mk (chapter05ThicknessRelationIdeal R π n)
    (MvPolynomial.X i)

theorem chapter05_thickness_equation
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    chapter05ThicknessCoordinate R π n 0 *
        chapter05ThicknessCoordinate R π n 1 =
      algebraMap R (chapter05ThicknessRing R π n) (π ^ n) := by
  sorry

def chapter05ThicknessOriginIdeal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Ideal (chapter05ThicknessRing R π n) :=
  Ideal.span ({chapter05ThicknessCoordinate R π n 0,
    chapter05ThicknessCoordinate R π n 1} :
    Set (chapter05ThicknessRing R π n))

def Chapter05ThicknessNormal
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Prop :=
  IsDomain (chapter05ThicknessRing R π n) ∧
    IsIntegrallyClosed (chapter05ThicknessRing R π n)

def Chapter05ThicknessSingularAtOrigin
    (R : Type u) [CommRing R] (π : R) (n : ℕ) : Prop :=
  ∃ hp : (chapter05ThicknessOriginIdeal R π n).IsPrime,
    ¬ (letI := hp
      IsRegularLocalRing
        (Localization.AtPrime (chapter05ThicknessOriginIdeal R π n)))

def Chapter05ThicknessBlowupDecreasesExponent (n : ℕ) : Prop :=
  1 < n → n - 1 < n

/- LOCAL_DEPENDENCY_GUESS: The pinned project has no local resolution object
for the thickness singularity, so the finite exponent list and the incidence
of its exceptional chain are exposed as fields of a reusable profile. -/

structure Chapter05ThicknessResolutionData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (n : ℕ) where
  source : Scheme.{u}
  source_eq : source = Scheme.Spec
    (CommRingCat.of (chapter05ThicknessRing R π n))
  resolution : Scheme.{u}
  resolutionMap : resolution ⟶ source
  proper : IsProper resolutionMap
  exponents : List ℕ
  initial_exponent : exponents.head? = some n
  exponent_steps_decrease : Prop
  chain_between_branches : Prop

theorem chapter05_thickness_blowup_decreases_exponent
    (n : ℕ) (hn : 1 < n) :
    Chapter05ThicknessBlowupDecreasesExponent n := by
  sorry

theorem chapter05_thickness_is_normal_singular_and_resolves_to_a_chain
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 1 < n) :
    Chapter05ThicknessNormal R π n ∧
      Chapter05ThicknessSingularAtOrigin R π n ∧
      Nonempty (Chapter05ThicknessResolutionData R π n) := by
  sorry

/-! The cusp equation `y^2 - x^3 - π` separates regularity of the total
space from nodality of the special fiber. -/

def chapter05CuspEquation
    (R : Type u) [CommRing R] (π : R) :
    chapter05DVRPolynomialRing R 2 :=
  MvPolynomial.X 0 ^ 3 + MvPolynomial.C π - MvPolynomial.X 1 ^ 2

def chapter05CuspRelationIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter05DVRPolynomialRing R 2) :=
  Ideal.span ({chapter05CuspEquation R π} :
    Set (chapter05DVRPolynomialRing R 2))

abbrev chapter05CuspRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter05DVRPolynomialRing R 2 ⧸ chapter05CuspRelationIdeal R π

def chapter05CuspStructureMap
    (R : Type u) [CommRing R] (π : R) :
    Scheme.Spec (CommRingCat.of (chapter05CuspRing R π)) ⟶
      Scheme.Spec (CommRingCat.of R) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (algebraMap R (chapter05CuspRing R π)))

def chapter05CuspOriginIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter05CuspRing R π) :=
  Ideal.span ({
    Ideal.Quotient.mk (chapter05CuspRelationIdeal R π) (MvPolynomial.X 0),
    Ideal.Quotient.mk (chapter05CuspRelationIdeal R π) (MvPolynomial.X 1)
  } : Set (chapter05CuspRing R π))

def Chapter05CuspTotalSpaceRegularAtOrigin
    (R : Type u) [CommRing R] (π : R) : Prop :=
  ∃ hp : (chapter05CuspOriginIdeal R π).IsPrime,
    letI := hp
      IsRegularLocalRing (Localization.AtPrime (chapter05CuspOriginIdeal R π))

def chapter05CuspSpecialFiberEquation
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    MvPolynomial (Fin 2) (IsLocalRing.ResidueField R) :=
  MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C (algebraMap R (IsLocalRing.ResidueField R) π) -
    MvPolynomial.X 1 ^ 2

def chapter05CuspSpecialFiberRelationIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    Ideal (MvPolynomial (Fin 2) (IsLocalRing.ResidueField R)) :=
  Ideal.span ({chapter05CuspSpecialFiberEquation R π} :
    Set (MvPolynomial (Fin 2) (IsLocalRing.ResidueField R)))

abbrev chapter05CuspSpecialFiberRing
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :=
  MvPolynomial (Fin 2) (IsLocalRing.ResidueField R) ⧸
    chapter05CuspSpecialFiberRelationIdeal R π

def chapter05CuspSpecialFiberOriginIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    Ideal (chapter05CuspSpecialFiberRing R π) :=
  Ideal.span ({
    Ideal.Quotient.mk (chapter05CuspSpecialFiberRelationIdeal R π)
      (MvPolynomial.X 0),
    Ideal.Quotient.mk (chapter05CuspSpecialFiberRelationIdeal R π)
      (MvPolynomial.X 1)
  } : Set (chapter05CuspSpecialFiberRing R π))

def Chapter05CuspSpecialFiberCuspidal
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) : Prop :=
  ∃ hp : (chapter05CuspSpecialFiberOriginIdeal R π).IsPrime,
    (letI := hp
      ¬ IsRegularLocalRing
        (Localization.AtPrime (chapter05CuspSpecialFiberOriginIdeal R π)))

theorem chapter05_cusp_specialFiber_equation
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :
    chapter05CuspSpecialFiberEquation R π =
      MvPolynomial.X 0 ^ 3 +
          MvPolynomial.C (algebraMap R (IsLocalRing.ResidueField R) π) -
        MvPolynomial.X 1 ^ 2 := by
  rfl

theorem chapter05_cusp_specialFiber_uniformizer_equation
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    chapter05CuspSpecialFiberEquation R π =
      MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2 := by
  sorry

structure Chapter05CuspRegularTotalSpaceProfile
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) where
  totalSpaceRegularAtOrigin : Chapter05CuspTotalSpaceRegularAtOrigin R π
  specialFiberCuspidal : Chapter05CuspSpecialFiberCuspidal R π

theorem chapter05_cusp_can_have_regular_total_space_and_cuspidal_fiber
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    Nonempty (Chapter05CuspRegularTotalSpaceProfile R π) := by
  sorry

/-! Finally, `π x = 0` has vertical torsion and therefore is not flat. -/

def chapter05VerticalTorsionPolynomialRing
    (R : Type u) [CommRing R] :=
  chapter05DVRPolynomialRing R 1

def chapter05VerticalTorsionEquation
    (R : Type u) [CommRing R] (π : R) :
    chapter05VerticalTorsionPolynomialRing R :=
  MvPolynomial.C π * MvPolynomial.X 0

def chapter05VerticalTorsionRelationIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter05VerticalTorsionPolynomialRing R) :=
  Ideal.span ({chapter05VerticalTorsionEquation R π} :
    Set (chapter05VerticalTorsionPolynomialRing R))

abbrev chapter05VerticalTorsionRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter05VerticalTorsionPolynomialRing R ⧸
    chapter05VerticalTorsionRelationIdeal R π

def chapter05VerticalTorsionStructureMap
    (R : Type u) [CommRing R] (π : R) :
    Scheme.Spec (CommRingCat.of (chapter05VerticalTorsionRing R π)) ⟶
      Scheme.Spec (CommRingCat.of R) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (algebraMap R (chapter05VerticalTorsionRing R π)))

theorem chapter05_vertical_torsion_equation_is_not_flat
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) :
    Chapter05VerticalTorsion R (chapter05VerticalTorsionRing R π) ∧
      ¬ Module.Flat R (chapter05VerticalTorsionRing R π) := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05
