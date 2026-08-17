import LastLib.Book06GlobalClassFieldTheory.Chapter12.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter12

noncomputable section

open LastLib.Book06GlobalClassFieldTheory.Chapter07
open LastLib.Book06GlobalClassFieldTheory.Chapter08
open NumberField
open scoped nonZeroDivisors

universe u

/-! ## 12.3. Moduli, ramification, and splitting -/

def chapter12ModulusFiniteDepth
    {K : Type*} [Field K] [NumberField K] (m : Modulus K)
    (v : NumberField.FinitePlace K) : ℕ :=
  m.finiteExponent v

def chapter12ModulusRealSignPlaces
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) :
    Finset (RealPlace K) :=
  m.infinitePart

theorem chapter12_modulus_records_principal_unit_depth
    {K : Type*} [Field K] [NumberField K] (m : Modulus K)
    (v : NumberField.FinitePlace K) :
    chapter12ModulusFiniteDepth m v = m.finiteExponent v :=
  rfl

theorem chapter12_modulus_records_only_real_infinite_places
    {K : Type*} [Field K] [NumberField K] (m : Modulus K)
    (v : RealPlace K) (_hv : v ∈ chapter12ModulusRealSignPlaces m) :
    v.1.IsReal := by
  exact v.2

theorem chapter12_ray_class_field_is_maximal_for_a_modulus
    {K I : Type*} [Field K] [NumberField K]
    [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]
    (D : IdeleContext K I) (m : Modulus K) (R : RayClassField D m)
    {G : Type*} [CommGroup G] [Fintype G]
    (A : AbelianArtinData (K := K) (I := I) D G)
    (h : ExtensionConductorBound A m) :
    ArtinPresentationIsSubextension R A := by
  exact ray_class_field_contains_every_bounded_artin_presentation R A h

theorem chapter12_ray_class_field_kernel_is_the_ray_subgroup
    {K I : Type*} [Field K] [NumberField K]
    [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I]
    (D : IdeleContext K I) (m : Modulus K) (R : RayClassField D m) :
    rayClassFieldKernel R = rayClassSubgroup D m := by
  exact ray_class_field_kernel_eq_ray_class_subgroup R

theorem chapter12_prime_away_from_conductor_maps_to_arithmetic_frobenius
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus)
    {p : Ideal (𝓞 K)} (hp : p ∈ A.primeAway) :
    chapter08ArtinMap R E A hcond (R.idealClass p) = A.frobenius hp := by
  exact chapter08_ideal_group_artin_prime_eq_arithmetic_frobenius R E A hcond hp

theorem chapter12_subfield_splitting_iff_ray_class_membership
    {K L I C : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (S : Chapter08RaySubfieldData K L I C R)
    [Algebra (𝓞 K) (𝓞 L)]
    {p : Ideal (𝓞 K)} [p.IsPrime]
    (hp : chapter08PrimeAwayFromModulus R.modulus p) :
    chapter08SplitsCompletely K L p ↔
      chapter08RayClassOfIdeal R p ∈ S.correspondingSubgroup := by
  exact chapter08_subfield_splitting_iff_ray_class_mem R S hp

noncomputable def chapter12_hilbert_class_field_galois_group_is_class_group
    {K : Type*} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    Gal(chapter08HilbertClassField H / K) ≃*
      chapter08OrdinaryClassGroup K := by
  exact chapter08_hilbert_galois_group_equiv_class_group H

theorem chapter12_hilbert_prime_splits_iff_principal_class
    {K : Type*} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K)
    {p : Ideal (𝓞 K)} [p.IsPrime] :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    letI : Algebra (𝓞 K) (𝓞 H.carrier) := inferInstance
    chapter08SplitsCompletely K (chapter08HilbertClassField H) p ↔
      ∃ a : 𝓞 K, p = Ideal.span {a} := by
  sorry

theorem chapter12_ordinary_hilbert_field_preserves_real_places
    {K : Type*} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08RealPlacesStayReal K (chapter08HilbertClassField H) := by
  exact chapter08_hilbert_real_places_stay_real H

theorem chapter12_ordinary_hilbert_maximality_requires_real_preservation
    {K L : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K)
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hunram : chapter08UnramifiedAtFinitePlaces K L)
    (hreal : chapter08RealPlacesStayReal K L) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    chapter08ExtensionContained K L (chapter08HilbertClassField H) := by
  exact chapter08_hilbert_is_maximal_finite_unramified_real_preserving H hunram hreal

theorem chapter12_narrow_hilbert_field_has_no_infinite_unramified_requirement
    {K : Type*} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K)
    (HN : Chapter08NarrowHilbertClassFieldData K N) :
    letI : Field HN.carrier := HN.carrierField
    letI : Algebra K HN.carrier := HN.carrierAlgebra
    letI : NumberField HN.carrier := HN.carrierNumberField
    letI : FiniteDimensional K HN.carrier := HN.carrierFinite
    letI : IsAbelianGalois K HN.carrier := HN.carrierAbelianGalois
    letI : Algebra (𝓞 K) (𝓞 HN.carrier) := inferInstance
    chapter08UnramifiedAtFinitePlaces K
      (chapter08NarrowHilbertClassField HN) := by
  exact chapter08_narrow_hilbert_forgets_infinite_unramified_condition N HN

theorem chapter12_narrow_hilbert_maximality_has_no_real_place_hypothesis
    {K L : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K)
    (HN : Chapter08NarrowHilbertClassFieldData K N)
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hunram : chapter08UnramifiedAtFinitePlaces K L) :
    letI : Field HN.carrier := HN.carrierField
    letI : Algebra K HN.carrier := HN.carrierAlgebra
    letI : NumberField HN.carrier := HN.carrierNumberField
    letI : FiniteDimensional K HN.carrier := HN.carrierFinite
    letI : IsAbelianGalois K HN.carrier := HN.carrierAbelianGalois
    chapter08ExtensionContained K L (chapter08NarrowHilbertClassField HN) := by
  exact chapter08_narrow_hilbert_is_maximal_finite_unramified N HN hunram

def chapter12OrdinaryAndNarrowHilbertFieldsAgree
    {K : Type*} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K)
    (N : Chapter08NarrowClassGroupData K)
    (HN : Chapter08NarrowHilbertClassFieldData K N) : Prop :=
  letI : Field H.carrier := H.carrierField
  letI : Algebra K H.carrier := H.carrierAlgebra
  letI : NumberField H.carrier := H.carrierNumberField
  letI : FiniteDimensional K H.carrier := H.carrierFinite
  letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
  letI : Field HN.carrier := HN.carrierField
  letI : Algebra K HN.carrier := HN.carrierAlgebra
  letI : NumberField HN.carrier := HN.carrierNumberField
  letI : FiniteDimensional K HN.carrier := HN.carrierFinite
  letI : IsAbelianGalois K HN.carrier := HN.carrierAbelianGalois
  Nonempty (chapter08HilbertClassField H ≃ₐ[K]
    chapter08NarrowHilbertClassField HN)

def chapter12GlobalUnitsSupplyAllRealSignPatterns
    (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter08RealQuadraticSignMapSurjective K

theorem chapter12_ordinary_narrow_agreement_requires_unit_signs
    {K : Type*} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K)
    (N : Chapter08NarrowClassGroupData K)
    (HN : Chapter08NarrowHilbertClassFieldData K N)
    (hagree : chapter12OrdinaryAndNarrowHilbertFieldsAgree H N HN) :
    chapter12GlobalUnitsSupplyAllRealSignPatterns K := by
  sorry

structure Chapter12PrincipalRootOfUnityRelation
    (V A : Type*) [Fintype V] [CommGroup A] where
  localValue : V → A → ℂˣ
  rootsOfUnity : Set A
  principal_relation : ∀ ζ, ζ ∈ rootsOfUnity →
    ∏ v, localValue v ζ = 1

theorem chapter12_roots_of_unity_impose_principal_relations
    {V A : Type*} [Fintype V] [CommGroup A]
    (D : Chapter12PrincipalRootOfUnityRelation V A)
    {ζ : A} (hζ : ζ ∈ D.rootsOfUnity) :
    ∏ v, D.localValue v ζ = 1 := by
  exact D.principal_relation ζ hζ

theorem chapter12_cyclotomic_complete_splitting_is_congruence_one
    {m p : ℕ} {F : Type u} [Field F] [Algebra ℚ F]
    [NumberField F] [IsCyclotomicExtension {m} ℚ F]
    [IsAbelianGalois ℚ F] [Fact p.Prime] (hm : 2 < m)
    (hpm : ¬p ∣ m) :
    chapter08SplitsCompletely ℚ F (Ideal.span {(p : 𝓞 ℚ)}) ↔
      p ≡ 1 [MOD m] := by
  exact chapter08_cyclotomic_prime_splits_completely_iff_congruent_one hm hpm

theorem chapter12_complex_places_add_no_modulus_condition
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) :
    ∀ v, v ∈ m.infinitePart → v.1.IsReal := by
  intro v hv
  exact v.2

end

end LastLib.Book06GlobalClassFieldTheory.Chapter12
