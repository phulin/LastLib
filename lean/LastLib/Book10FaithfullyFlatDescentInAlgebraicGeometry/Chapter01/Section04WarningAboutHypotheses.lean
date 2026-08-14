import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Dependencies

/-!
# 1.4 A first warning about hypotheses

The failure predicates below make the two standard bad substitutes for a faithfully flat cover
explicit.  The quasi-compactness interface records finite control separately from tensor
faithfulness.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01

noncomputable section

/-- Modules on which an ideal acts trivially. -/
def Chapter01AnnihilatedByIdeal
    {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] : Prop :=
  I • (⊤ : Submodule A M) = ⊥

/-- The quotient map that is not a flat-cover substitute in general. -/
def chapter01QuotientMap {A : Type u} [CommRing A] (I : Ideal A) :
    A →+* A ⧸ I :=
  Ideal.Quotient.mk I

theorem chapter01_quotient_map_surjective
    {A : Type u} [CommRing A] (I : Ideal A) :
    Function.Surjective (chapter01QuotientMap I) :=
  Ideal.Quotient.mk_surjective

theorem chapter01_quotient_map_not_faithfullyFlat_of_nonzero_ideal
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≠ ⊥) :
    ¬ RingHom.FaithfullyFlat (chapter01QuotientMap I) := by
  sorry

theorem chapter01_quotient_map_kernel
    {A : Type u} [CommRing A] (I : Ideal A) :
    RingHom.ker (chapter01QuotientMap I) = I := by
  sorry

/-- Tensoring with an algebra reflects equality of all linear maps. -/
def Chapter01TensorReflectsMapEquality
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f g : M →ₗ[A] N), f.lTensor B = g.lTensor B → f = g

theorem chapter01_localization_not_faithfullyFlat_of_not_isUnit
    (A : Type u) [CommRing A] (f : A) (hf : ¬ IsUnit f) :
    ¬ RingHom.FaithfullyFlat (algebraMap A (Localization.Away f)) := by
  sorry

theorem chapter01_localization_specMap_not_surjective_of_not_isUnit
    (A : Type u) [CommRing A] (f : A) (hf : ¬ IsUnit f) :
    ¬ Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
  sorry

theorem chapter01_localization_does_not_reflect_maps_of_not_isUnit
    (A : Type u) [CommRing A] (f : A) (hf : ¬ IsUnit f) :
    ¬ Chapter01TensorReflectsMapEquality A (Localization.Away f) := by
  sorry

/-- Finite control over a quasi-compact open is a separate field of the fpqc-family interface. -/
theorem chapter01_fpqc_refinement_finite_reduction
    {T S : Scheme.{u}} {p : T ⟶ S} (𝒰 : Chapter01FpqcFamilyRefinement p)
    (U : S.Opens) (hU : IsQuasiCompact (U : Set S)) :
    ∃ (J : Finset 𝒰.index) (V : ∀ i : J, (𝒰.source i).Opens),
      (∀ i : J, IsQuasiCompact (V i : Set (𝒰.source i))) ∧
        (∀ x : U, ∃ i : J, ∃ y : V i, (𝒰.map i y : S) = x.1) :=
  𝒰.finite_reduction U hU

theorem chapter01_fpqc_refinement_finite_reduction_on_affines
    {T S : Scheme.{u}} {p : T ⟶ S} (𝒰 : Chapter01FpqcFamilyRefinement p)
    (U : S.Opens) (hU : IsAffineOpen U) (hq : IsQuasiCompact (U : Set S)) :
    ∃ (J : Finset 𝒰.index) (V : ∀ i : J, (𝒰.source i).Opens),
      (∀ i : J, IsQuasiCompact (V i : Set (𝒰.source i))) ∧
        (∀ x : U, ∃ i : J, ∃ y : V i, (𝒰.map i y : S) = x.1) := by
  exact chapter01_fpqc_refinement_finite_reduction 𝒰 U hq

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
