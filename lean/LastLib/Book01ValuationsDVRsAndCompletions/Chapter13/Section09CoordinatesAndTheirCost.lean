import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section08WorkedExamplesAndCounterexamples

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Ideal IsLocalRing

noncomputable section

/-! # Book 1, Chapter 13, Section 13.9: Coordinates, and what they cost -/

universe u

/-- An equal-characteristic coordinate presentation of a complete local ring. -/
structure Chapter13EqualCharacteristicCoordinateData
    (A k : Type u) [CommRing A] [IsLocalRing A] [Field k] where
  variableCount : ℕ
  coefficient_map : k →+* A
  coefficient_local : IsLocalHom coefficient_map
  map : MvPowerSeries (Fin variableCount) k →+* A
  map_local : IsLocalHom map
  map_extends :
    map.comp (MvPowerSeries.C : k →+* MvPowerSeries (Fin variableCount) k) =
      coefficient_map
  surjective : Function.Surjective map
  kernel_presentation : Nonempty
    ((MvPowerSeries (Fin variableCount) k ⧸ RingHom.ker map) ≃+* A)

/-- A mixed-characteristic coordinate presentation over a Cohen ring. -/
structure Chapter13MixedCharacteristicCoordinateData
    (A C k : Type u) [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p : ℕ) where
  variableCount : ℕ
  coefficient_map : C →+* A
  coefficient_local : IsLocalHom coefficient_map
  map : MvPowerSeries (Fin variableCount) C →+* A
  map_local : IsLocalHom map
  map_extends :
    map.comp (MvPowerSeries.C : C →+* MvPowerSeries (Fin variableCount) C) =
      coefficient_map
  surjective : Function.Surjective map
  kernel_presentation : Nonempty
    ((MvPowerSeries (Fin variableCount) C ⧸ RingHom.ker map) ≃+* A)

/-- The coordinate presentations supplied by the two coefficient theories. -/
theorem chapter13_coordinate_synthesis_equal_characteristic
    {A k : Type u} [CommRing A] [IsLocalRing A] [Field k]
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hcontains : Chapter13ContainsField A)
    (σ : k →+* A) (hσ : IsLocalHom σ)
    (hres : Function.Bijective ((Chapter13ResidueMap A).comp σ)) :
    ∃ data : Chapter13EqualCharacteristicCoordinateData A k,
      data.coefficient_map = σ := by
  have _ := hcontains
  let instNoetherian : IsNoetherianRing A := hA.1
  let instFinite : Module.Finite A (IsLocalRing.maximalIdeal A) :=
    Module.Finite.of_fg (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (IsLocalRing.maximalIdeal A)
  let x : Fin n → A := fun i => (f (Pi.basisFun A (Fin n) i) : A)
  have hx : ∀ i : Fin n, x i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    simp [x]
  have hgen : Chapter13MaximalIdealGenerators x := by
    apply le_antisymm
    · exact Ideal.span_le.2 (fun _ h => by
        obtain ⟨i, rfl⟩ := h
        exact (f (Pi.basisFun A (Fin n) i)).property)
    · intro a ha
      have htop : Submodule.span A (Set.range (fun i : Fin n =>
          f (Pi.basisFun A (Fin n) i))) = ⊤ := by
        apply top_unique
        intro y hy
        obtain ⟨i, hi⟩ := hf y
        have hmap : f i ∈ Submodule.map f
            (Submodule.span A (Set.range (Pi.basisFun A (Fin n)))) := by
          exact ⟨i, (Pi.basisFun A (Fin n)).mem_span i, rfl⟩
        have hle : Submodule.map f
            (Submodule.span A (Set.range (Pi.basisFun A (Fin n)))) ≤
            Submodule.span A (Set.range (fun i : Fin n =>
              f (Pi.basisFun A (Fin n) i))) := by
          apply Submodule.map_le_iff_le_comap.mpr
          apply Submodule.span_le.2
          intro z hz
          obtain ⟨i, rfl⟩ := hz
          exact Submodule.subset_span (Set.mem_range_self i)
        rw [← hi]
        exact hle hmap
      have hspan : Submodule.span A (Set.range x) =
          (IsLocalRing.maximalIdeal A : Submodule A A) :=
        (Submodule.span_range_subtype_eq_top_iff
          (IsLocalRing.maximalIdeal A : Submodule A A) hx).mp (by
            simp [x] at htop ⊢
            exact htop)
      change a ∈ Submodule.span A (Set.range x)
      rw [hspan]
      exact ha
  obtain ⟨F, hF, hFsurj⟩ := chapter13_cohen_structure_equal_characteristic
    hA σ hσ hres n x hx hgen
  refine ⟨{
    variableCount := n
    coefficient_map := σ
    coefficient_local := hσ
    map := F
    map_local := IsLocalHom.of_surjective F hFsurj
    map_extends := hF.1
    surjective := hFsurj
    kernel_presentation := ⟨RingHom.quotientKerEquivOfSurjective hFsurj⟩
  }, rfl⟩

theorem chapter13_coordinate_synthesis_mixed_characteristic
    {A C k : Type u} [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hmixed : Chapter13MixedCharacteristic A p)
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* k)
    (u : C →+* A) (hu : IsLocalHom u)
    (hres : Chapter13ResidueMapCompatibility eC eA (RingHom.id k) u) :
    ∃ data : Chapter13MixedCharacteristicCoordinateData A C k p,
      data.coefficient_map = u := by
  let instNoetherian : IsNoetherianRing A := hA.1
  let instFinite : Module.Finite A (IsLocalRing.maximalIdeal A) :=
    Module.Finite.of_fg (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (IsLocalRing.maximalIdeal A)
  let x : Fin n → A := fun i => (f (Pi.basisFun A (Fin n) i) : A)
  have hx : ∀ i : Fin n, x i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    simp [x]
  have hgen : Chapter13MaximalIdealGenerators x := by
    apply le_antisymm
    · exact Ideal.span_le.2 (fun _ h => by
        obtain ⟨i, rfl⟩ := h
        exact (f (Pi.basisFun A (Fin n) i)).property)
    · intro a ha
      have htop : Submodule.span A (Set.range (fun i : Fin n =>
          f (Pi.basisFun A (Fin n) i))) = ⊤ := by
        apply top_unique
        intro y hy
        obtain ⟨i, hi⟩ := hf y
        have hmap : f i ∈ Submodule.map f
            (Submodule.span A (Set.range (Pi.basisFun A (Fin n)))) := by
          exact ⟨i, (Pi.basisFun A (Fin n)).mem_span i, rfl⟩
        have hle : Submodule.map f
            (Submodule.span A (Set.range (Pi.basisFun A (Fin n)))) ≤
            Submodule.span A (Set.range (fun i : Fin n =>
              f (Pi.basisFun A (Fin n) i))) := by
          apply Submodule.map_le_iff_le_comap.mpr
          apply Submodule.span_le.2
          intro z hz
          obtain ⟨i, rfl⟩ := hz
          exact Submodule.subset_span (Set.mem_range_self i)
        rw [← hi]
        exact hle hmap
      have hspan : Submodule.span A (Set.range x) =
          (IsLocalRing.maximalIdeal A : Submodule A A) :=
        (Submodule.span_range_subtype_eq_top_iff
          (IsLocalRing.maximalIdeal A : Submodule A A) hx).mp (by
            simp [x] at htop ⊢
            exact htop)
      change a ∈ Submodule.span A (Set.range x)
      rw [hspan]
      exact ha
  obtain ⟨F, hF, hFsurj⟩ := chapter13_cohen_structure_mixed_characteristic
    p n hA hmixed hC eC eA u hu hres x hx hgen
  refine ⟨{
    variableCount := n
    coefficient_map := u
    coefficient_local := hu
    map := F
    map_local := IsLocalHom.of_surjective F hFsurj
    map_extends := hF.1
    surjective := hFsurj
    kernel_presentation := ⟨RingHom.quotientKerEquivOfSurjective hFsurj⟩
  }, rfl⟩

/-! ### Finite extensions of the regular coordinate models -/

theorem chapter13_coordinate_synthesis_equal_domain_finite_extension
    {A k : Type u} [CommRing A] [IsLocalRing A] [Field k] (d : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hdomain : IsDomain A)
    (σ : k →+* A) (hσ : IsLocalHom σ)
    (hres : Function.Bijective ((Chapter13ResidueMap A).comp σ))
    (x : Fin d → A)
    (hx : ∀ i : Fin d, x i ∈ IsLocalRing.maximalIdeal A)
    (hfinite : Chapter13FiniteLengthParameterFamily
      (Ideal.span (Set.range x)))
    (hdim : ringKrullDim A = d) :
    ∃ F : MvPowerSeries (Fin d) k →+* A,
      Chapter13PowerSeriesEvaluationData d σ x F ∧
        Chapter13FinitePowerSeriesModule F ∧ Function.Injective F := by
  obtain ⟨F, hF, hfiniteF⟩ := chapter13_finite_over_equal_power_series
    hA σ hσ hres d x hx hfinite
  have hmodel := chapter13_power_series_over_field_is_regular k d
  have hdimQ : ringKrullDim (MvPowerSeries (Fin d) k) = ringKrullDim A :=
    hmodel.2.2.2.trans hdim.symm
  have hinj := chapter13_finite_power_series_map_injective
    (I := Chapter13PowerSeriesMaximalIdeal k d) d
    hmodel F hfiniteF hdomain hdimQ
  exact ⟨F, hF, hfiniteF, hinj⟩

theorem chapter13_coordinate_synthesis_mixed_domain_finite_extension
    {A C k : Type u} [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p d : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hdomain : IsDomain A)
    (hmixed : Chapter13MixedCharacteristic A p)
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* k)
    (u : C →+* A) (hu : IsLocalHom u)
    (hres : Chapter13ResidueMapCompatibility eC eA (RingHom.id k) u)
    (x : Fin d → A)
    (hx : ∀ i : Fin d, x i ∈ IsLocalRing.maximalIdeal A)
    (hfinite : Chapter13FiniteLengthParameterFamily
      (Ideal.span ({(p : A)} ∪ Set.range x)))
    (hdim : ringKrullDim A = d + 1) :
    ∃ F : MvPowerSeries (Fin d) C →+* A,
      Chapter13PowerSeriesEvaluationData d u x F ∧
        Chapter13FinitePowerSeriesModule F ∧ Function.Injective F := by
  obtain ⟨F, hF, hfiniteF⟩ := chapter13_finite_over_mixed_power_series
    p hA hmixed hC eC eA u hu hres d x hx hfinite
  have hmodel := chapter13_power_series_over_cohen_ring_is_regular C k p d hC
  have hdimQ : ringKrullDim (MvPowerSeries (Fin d) C) = ringKrullDim A :=
    hmodel.2.2.2.trans hdim.symm
  have hinj := chapter13_finite_power_series_map_injective
    (I := Chapter13PowerSeriesMaximalIdeal C d) (d + 1)
    hmodel F hfiniteF hdomain hdimQ
  exact ⟨F, hF, hfiniteF, hinj⟩

/-! ### What is and is not canonical -/

theorem chapter13_imperfect_coordinates_are_not_canonical
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (B : Set (Chapter13ResidueRing A))
    (hB : Chapter13PBasis
      (Chapter13PthPowerSubfield (Chapter13ResidueRing A) p) B p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A) :
    Nonempty
      (Chapter13CoefficientFields A ≃
        {a : B → A // Chapter13AdmissiblePBaseLiftFamily B a}) := by
  exact chapter13_equal_characteristic_p_coefficient_fields_bijection p B hB hA

theorem chapter13_perfect_coordinates_are_canonical
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hperfect : Chapter13PerfectAtPrime (Chapter13ResidueRing A) p) :
    ∃! K : Chapter13Subfield A,
      Chapter13IsCoefficientField K ∧
        (K.carrier : Set A) =
          ⋂ n : ℕ, Set.range (fun x : A => x ^ (p ^ n)) := by
  exact chapter13_perfect_residue_unique_coefficient_field p hA hperfect

theorem chapter13_perfect_cohen_coordinates_are_functorial
    {C A : Type u} [CommRing C] [IsLocalRing C]
    [CommRing A] [IsLocalRing A] {k ℓ : Type u}
    [Field k] [Field ℓ] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] [CharP ℓ p]
    (hC : Chapter13IsCohenRing C k p)
    (hperfect : Chapter13PerfectAtPrime k p)
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* ℓ) (φ : k →+* ℓ) :
    ∃! u : C →+* A,
      IsLocalHom u ∧ Chapter13ResidueMapCompatibility eC eA φ u := by
  exact chapter13_perfect_cohen_mapping_unique p hC hperfect hA eC eA φ

/-! ### Completeness as the common approximation mechanism -/

def Chapter13SuccessiveApproximationPrinciple
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal A) A

theorem chapter13_complete_local_ring_is_its_adic_limit
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : Chapter13SuccessiveApproximationPrinciple A) :
    Nonempty
      (A ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  unfold Chapter13SuccessiveApproximationPrinciple at hA
  let : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hA
  exact ⟨(AdicCompletion.ofAlgEquiv
    (IsLocalRing.maximalIdeal A)).toRingEquiv⟩

theorem chapter13_complete_local_ring_sums_adic_approximations
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (z : ℕ → A)
    (hz : Chapter13AdicTermsVanish (IsLocalRing.maximalIdeal A) z) :
    ∃ x : A,
      Chapter13AdicConvergesSeries (IsLocalRing.maximalIdeal A) z x ∧
        ∀ e : Equiv.Perm ℕ,
          Chapter13AdicConvergesSeries
            (IsLocalRing.maximalIdeal A) (z ∘ e) x := by
  exact chapter13_finite_module_adic_series hA z hz

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
