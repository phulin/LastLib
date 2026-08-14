import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators TensorProduct

noncomputable section

universe u v

/-! ### 5.2 Flatness from torsion-freeness -/

theorem chapter05_flat_iff_torsionFree
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [IsDedekindDomain R] :
    Module.Flat R M ↔ Module.IsTorsionFree R M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]

theorem chapter05_flat_implies_torsionFree
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [IsDomain R] (hflat : Module.Flat R M) :
    Module.IsTorsionFree R M := by
  sorry

theorem chapter05_torsionFree_implies_flat
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [IsDedekindDomain R]
    (htorsionFree : Module.IsTorsionFree R M) :
    Module.Flat R M := by
  sorry

theorem chapter05_flat_module_has_no_vertical_torsion
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R M) :
    Module.IsTorsionFree R M := by
  sorry

theorem chapter05_domain_algebra_is_torsionFree
    (R A : Type u) [CommRing R] [CommRing A]
    [IsDomain R] [IsDomain A] [Algebra R A]
    (hinjective : Function.Injective (algebraMap R A)) :
    Module.IsTorsionFree R A := by
  sorry

theorem chapter05_domain_algebra_over_Dedekind_is_flat
    (R A : Type u) [CommRing R] [CommRing A]
    [IsDomain A] [IsDedekindDomain R] [Algebra R A]
    (hinjective : Function.Injective (algebraMap R A)) :
    Module.Flat R A := by
  sorry

def Chapter05AffineDominatesBase
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Prop :=
  Function.Injective (algebraMap R A)

def Chapter05VerticalTorsion
    (R A : Type u) [CommRing R] [CommRing A]
    [Module R A] : Prop :=
  ¬ Module.IsTorsionFree R A

theorem chapter05_verticalTorsion_implies_not_flat
    (R A : Type u) [CommRing R] [CommRing A]
    [Module R A]
    (htorsion : Chapter05VerticalTorsion R A) :
    ¬ Module.Flat R A := by
  sorry

theorem chapter05_affine_dominance_is_torsionFree
    (R A : Type u) [CommRing R] [CommRing A]
    [IsDomain R] [IsDomain A] [Algebra R A]
    (hdom : Chapter05AffineDominatesBase R A) :
    Module.IsTorsionFree R A := by
  exact chapter05_domain_algebra_is_torsionFree R A hdom

theorem chapter05_affine_dominance_over_Dedekind_is_flat
    (R A : Type u) [CommRing R] [CommRing A]
    [IsDomain A] [IsDedekindDomain R] [Algebra R A]
    (hdom : Chapter05AffineDominatesBase R A) :
    Module.Flat R A := by
  exact chapter05_domain_algebra_over_Dedekind_is_flat R A hdom

/- The scheme-level statement is the affine-local form of the preceding
domain argument. -/

theorem chapter05_integral_dominant_morphism_is_flat
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05DedekindScheme S)
    (hX : IsIntegral X) (hdom : IsDominant f) :
    Flat f := by
  sorry

theorem chapter05_integral_surface_dominating_Dedekind_base_is_flat
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05DedekindScheme S)
    (hX : Chapter05ArithmeticSurface S X f)
    (hdom : IsDominant f) :
    Flat f := by
  exact chapter05_integral_dominant_morphism_is_flat f hS hX.integral hdom

theorem chapter05_flat_dominant_morphism_has_no_vertical_source_component
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : Chapter05DedekindScheme S)
    (hX : IsIntegral X) (hdom : IsDominant f) (hflat : Flat f) :
    ¬ Chapter05VerticalIrreducibleComponent f := by
  sorry

def Chapter05FlatFamilyWithNonreducedFiber
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ ∃ s : S, ¬ IsReduced (f.fiber s)

def Chapter05FlatFamilyWithReducibleFiber
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ ∃ s : S, ¬ IsIntegral (f.fiber s)

/-! The equation `x^2 - π` is the local warning that flatness does not mean
that the special fiber is reduced. -/

abbrev chapter05RamifiedPointPolynomialRing
    (R : Type u) [CommRing R] :=
  MvPolynomial (Fin 1) R

def chapter05RamifiedPointEquation
    (R : Type u) [CommRing R] (π : R) :
    chapter05RamifiedPointPolynomialRing R :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.C π

def chapter05RamifiedPointRelationIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (chapter05RamifiedPointPolynomialRing R) :=
  Ideal.span ({chapter05RamifiedPointEquation R π} :
    Set (chapter05RamifiedPointPolynomialRing R))

abbrev chapter05RamifiedPointRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter05RamifiedPointPolynomialRing R ⧸
    chapter05RamifiedPointRelationIdeal R π

def chapter05RamifiedPointStructureMap
    (R : Type u) [CommRing R] (π : R) :
    AlgebraicGeometry.Spec (CommRingCat.of (chapter05RamifiedPointRing R π)) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of R) :=
  Scheme.Spec.map (CommRingCat.ofHom
    (algebraMap R (chapter05RamifiedPointRing R π))).op

abbrev chapter05RamifiedPointSpecialFiberRing
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) :=
  chapter05RamifiedPointRing R π ⊗[R] IsLocalRing.ResidueField R

def Chapter05RamifiedPointSpecialFiberNonreduced
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) : Prop :=
  ¬ IsReduced (chapter05RamifiedPointSpecialFiberRing R π)

theorem chapter05_ramifiedPoint_equation_flat_and_specialFiber_nonreduced
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (hchar : ringChar (IsLocalRing.ResidueField R) ≠ 2) :
    Module.Flat R (chapter05RamifiedPointRing R π) ∧
      Chapter05RamifiedPointSpecialFiberNonreduced R π := by
  sorry

theorem chapter05_flatness_does_not_force_reduced_special_fibers
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (hchar : ringChar (IsLocalRing.ResidueField R) ≠ 2) :
    Module.Flat R (chapter05RamifiedPointRing R π) ∧
      ¬ IsReduced (chapter05RamifiedPointSpecialFiberRing R π) := by
  exact chapter05_ramifiedPoint_equation_flat_and_specialFiber_nonreduced
    R π hπ hchar

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter05
