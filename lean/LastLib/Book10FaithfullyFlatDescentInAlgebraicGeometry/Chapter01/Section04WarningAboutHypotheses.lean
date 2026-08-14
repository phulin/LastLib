import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Dependencies
import Mathlib.RingTheory.Localization.BaseChange

/-!
# 1.4 A first warning about hypotheses

The failure predicates below make the two standard bad substitutes for a faithfully flat cover
explicit.  The quasi-compactness interface records finite control separately from tensor
faithfulness.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

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
  intro h
  have hinj : Function.Injective (chapter01QuotientMap I) :=
    RingHom.FaithfullyFlat.injective h
  apply hI
  apply le_antisymm
  · intro x hx
    have hxzero : chapter01QuotientMap I x = 0 := by
      rw [chapter01QuotientMap, Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    have hx0 : x = 0 := by
      apply hinj
      simpa using hxzero
    simpa using hx0
  · exact bot_le

theorem chapter01_quotient_map_kernel
    {A : Type u} [CommRing A] (I : Ideal A) :
    RingHom.ker (chapter01QuotientMap I) = I := by
  change RingHom.ker (Ideal.Quotient.mk I) = I
  exact Ideal.mk_ker

/-- Tensoring with an algebra reflects equality of all linear maps. -/
def Chapter01TensorReflectsMapEquality
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f g : M →ₗ[A] N), f.lTensor B = g.lTensor B → f = g

theorem chapter01_localization_not_faithfullyFlat_of_not_isUnit
    (A : Type u) [CommRing A] (f : A) (hf : ¬ IsUnit f) :
    ¬ RingHom.FaithfullyFlat (algebraMap A (Localization.Away f)) := by
  intro h
  have hff : Module.FaithfullyFlat A (Localization.Away f) :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp h
  have hcriterion :=
    (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A
      (Localization.Away f)).mp hff
  have htop : (Ideal.span ({f} : Set A)) •
      (⊤ : Submodule A (Localization.Away f)) = ⊤ := by
    rw [Ideal.smul_top_eq_map]
    apply (Submodule.restrictScalars_eq_top_iff A (Localization.Away f)
      (Localization.Away f)).2
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.span_singleton_eq_top.mpr (IsLocalization.Away.algebraMap_isUnit f)
  have hspan : Ideal.span ({f} : Set A) = ⊤ := hcriterion.2 _ htop
  exact hf (Ideal.span_singleton_eq_top.mp hspan)

theorem chapter01_localization_specMap_not_surjective_of_not_isUnit
    (A : Type u) [CommRing A] (f : A) (hf : ¬ IsUnit f) :
    ¬ Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
  intro hsurj
  have hspan : Ideal.span ({f} : Set A) ≠ ⊤ := by
    intro htop
    exact hf (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨m, hm, hfm⟩ := Ideal.exists_le_maximal (Ideal.span ({f} : Set A)) hspan
  let p : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hfp : f ∈ p.asIdeal := hfm (Ideal.subset_span (by simp))
  have hpnot : p ∉ PrimeSpectrum.basicOpen f := by
    intro hp
    exact (PrimeSpectrum.mem_basicOpen f p).mp hp hfp
  obtain ⟨q, hq⟩ := hsurj p
  have hp_range : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := ⟨q, hq⟩
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at hp_range
  exact hpnot hp_range

theorem chapter01_localization_does_not_reflect_maps_of_not_isUnit
    (A : Type u) [CommRing A] (f : A) (hf : ¬ IsUnit f) :
    ¬ Chapter01TensorReflectsMapEquality A (Localization.Away f) := by
  intro h
  unfold Chapter01TensorReflectsMapEquality at h
  let M := A ⧸ Ideal.span ({f} : Set A)
  have hzero : (0 : M) ∈ Algebra.algebraMapSubmonoid M (Submonoid.powers f) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    have hz : algebraMap A M f = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.subset_span (by simp)
    rw [hz]
    exact Submonoid.mem_powers _
  let _ : IsLocalization (Algebra.algebraMapSubmonoid M (Submonoid.powers f))
      (M ⊗[A] Localization.Away f) := by infer_instance
  let _ : Subsingleton (M ⊗[A] Localization.Away f) :=
    IsLocalization.subsingleton hzero
  let _ : Subsingleton (Localization.Away f ⊗[A] M) :=
    ⟨fun x y => (TensorProduct.comm A (Localization.Away f) M).injective
      (Subsingleton.elim _ _)⟩
  have hEq : ((LinearMap.id : M →ₗ[A] M).lTensor (Localization.Away f)) =
      (0 : M →ₗ[A] M).lTensor (Localization.Away f) := by
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  have hne : (LinearMap.id : M →ₗ[A] M) ≠ 0 := by
    intro hzeroMap
    have h1 := congrArg (fun k : M →ₗ[A] M => k 1) hzeroMap
    have hmem : (1 : A) ∈ Ideal.span ({f} : Set A) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa using h1
    apply hf
    exact Ideal.span_singleton_eq_top.mp ((Ideal.span ({f} : Set A)).eq_top_iff_one.mpr hmem)
  exact hne (h (LinearMap.id : M →ₗ[A] M) 0 hEq)

/-- Finite control over a quasi-compact open is a separate field of the fpqc-family interface. -/
theorem chapter01_fpqc_refinement_finite_reduction
    {T S : Scheme.{u}} {p : T ⟶ S} (𝒰 : Chapter01FpqcFamilyRefinement p)
    (U : S.Opens) (hU : IsCompact (U : Set S)) :
    ∃ (J : Finset 𝒰.index) (V : ∀ i : J, (𝒰.source i).Opens),
      (∀ i : J, IsCompact (V i : Set (𝒰.source i))) ∧
        (∀ i : J, ∀ y : V i, (𝒰.map i y : S) ∈ U) ∧
        (∀ x : U, ∃ i : J, ∃ y : V i, (𝒰.map i y : S) = x.1) :=
  𝒰.finite_reduction U hU

theorem chapter01_fpqc_refinement_finite_reduction_on_affines
    {T S : Scheme.{u}} {p : T ⟶ S} (𝒰 : Chapter01FpqcFamilyRefinement p)
    (U : S.Opens) (_hU : IsAffineOpen U) (hq : IsCompact (U : Set S)) :
    ∃ (J : Finset 𝒰.index) (V : ∀ i : J, (𝒰.source i).Opens),
      (∀ i : J, IsCompact (V i : Set (𝒰.source i))) ∧
        (∀ i : J, ∀ y : V i, (𝒰.map i y : S) ∈ U) ∧
        (∀ x : U, ∃ i : J, ∃ y : V i, (𝒰.map i y : S) = x.1) := by
  exact chapter01_fpqc_refinement_finite_reduction 𝒰 U hq

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
