import LastLib.Book04AdelesAndIdeles.Chapter10.Section05ExamplesOfNormBehavior

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators Topology

/-! ## 10.6. Norms and congruence depth -/

/-- The valuation neighborhood of `1` at depth `n`. -/
def chapter10ValuationNeighborhood {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) (n : ℕ) : Set F :=
  {x | v (x - 1) ≥ (n : WithTop ℤ)}

theorem chapter10_mem_valuation_neighborhood_iff
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (n : ℕ) (x : F) :
    x ∈ chapter10ValuationNeighborhood v n ↔
      v (x - 1) ≥ (n : WithTop ℤ) := Iff.rfl

/-- A chosen valuation is compatible with the topology at the identity when
its depth neighborhoods form a basis there. -/
def chapter10ValuationNeighborhoodBasis {F : Type*} [Field F]
    [TopologicalSpace F] (v : AddValuation F (WithTop ℤ)) : Prop :=
  (∀ n, chapter10ValuationNeighborhood v n ∈ 𝓝 (1 : F)) ∧
    ∀ s ∈ 𝓝 (1 : F), ∃ n,
      chapter10ValuationNeighborhood v n ⊆ s

theorem chapter10_valuation_neighborhood_basis_mem
    {F : Type*} [Field F] [TopologicalSpace F]
    (v : AddValuation F (WithTop ℤ))
    (h : chapter10ValuationNeighborhoodBasis v) (n : ℕ) :
    chapter10ValuationNeighborhood v n ∈ 𝓝 (1 : F) :=
  h.1 n

/-- Continuity at `1` gives the asymmetric depth estimate needed for norms. -/
theorem chapter10_local_norm_maps_deep_principal_units
    (F E : Type*) [NontriviallyNormedField F] [CompleteSpace F] [NormedField E]
    [NormedAlgebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (hF : chapter10ValuationNeighborhoodBasis vF)
    (hE : chapter10ValuationNeighborhoodBasis vE)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ Set.MapsTo (chapter10LocalNorm F E)
      (chapter10ValuationNeighborhood vE m)
      (chapter10ValuationNeighborhood vF n) := by
  sorry

theorem chapter10_local_norm_maps_deep_principal_unit_sets
    (F E : Type*) [NontriviallyNormedField F] [CompleteSpace F] [NormedField E]
    [NormedAlgebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (hF : chapter10ValuationNeighborhoodBasis vF)
    (hE : chapter10ValuationNeighborhoodBasis vE)
    (hprincipalF : ∀ n,
      chapter10ValuationNeighborhood vF n ⊆ chapter10LocalPrincipalUnitSet vF n)
    (hprincipalE : ∀ n,
      chapter10LocalPrincipalUnitSet vE n ⊆ chapter10ValuationNeighborhood vE n)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ Set.MapsTo (chapter10LocalNorm F E)
      (chapter10LocalPrincipalUnitSet vE m)
      (chapter10LocalPrincipalUnitSet vF n) := by
  sorry

theorem chapter10_local_norm_tendsto_one
    (F E : Type*) [NontriviallyNormedField F] [CompleteSpace F] [NormedField E]
    [NormedAlgebra F E]
    [FiniteDimensional F E] :
    Filter.Tendsto (chapter10LocalNorm F E)
      (𝓝 (1 : E)) (𝓝 (1 : F)) := by
  sorry

theorem chapter10_norm_first_order_expansion
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (z : E) :
    chapter10LocalNorm F E (1 + z) =
      1 + Algebra.trace F E z +
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder F E z := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_norm_one_add_linearizes_to_trace
    F E z

/- The different governs the sharp relation between source and target depth;
the chapter only needs the existence statement, so no universal sharp formula
is built into this API. -/

def chapter10NormDepthControl
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ)) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ Set.MapsTo (chapter10LocalNorm F E)
    (chapter10ValuationNeighborhood vE m)
    (chapter10ValuationNeighborhood vF n)

theorem chapter10_norm_depth_control_iff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ)) :
    chapter10NormDepthControl F E vF vE ↔
      ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ Set.MapsTo (chapter10LocalNorm F E)
        (chapter10ValuationNeighborhood vE m)
        (chapter10ValuationNeighborhood vF n) := Iff.rfl

/-! ### Global ray levels -/

/-- A finite modulus with an optional positivity predicate for real places. -/
structure Chapter10Modulus (Places : Type*) where
  finitePart : Finset Places
  exponent : Places → ℕ
  exponent_support : ∀ v, exponent v ≠ 0 → v ∈ finitePart
  positiveAt : Places → Prop
  positive_support : {v | positiveAt v}.Finite

theorem chapter10_modulus_support_finite
    {Places : Type*} (m : Chapter10Modulus Places) :
    (Function.support m.exponent).Finite := by
  sorry

theorem chapter10_modulus_positive_support_finite
    {Places : Type*} (m : Chapter10Modulus Places) :
    {v | m.positiveAt v}.Finite :=
  m.positive_support

/-- A level system of ray-unit subgroups. -/
structure Chapter10RayUnitSystem
    (I Places : Type*) [CommGroup I] where
  unit : Chapter10Modulus Places → Subgroup I

abbrev chapter10RayQuotient
    {I Places : Type*} [CommGroup I]
    (U : Chapter10RayUnitSystem I Places) (m : Chapter10Modulus Places) : Type _ :=
  I ⧸ U.unit m

/- LOCAL_DEPENDENCY_GUESS: the preceding global chapter is expected to supply
the theorem that local norm continuity, finite support of a modulus, and the
real-place sign condition assemble into the following global level statement.
It is recorded as a proposition here rather than asserted without those
missing Chapter 9 hypotheses. -/
def chapter10NormMapsSufficientlyDeepRayUnits
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K)
    (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK) :
    Prop :=
    ∃ n : Chapter10Modulus PlacesL,
      Subgroup.map N (U_L.unit n) ≤ U_K.unit m

theorem chapter10_norm_maps_sufficiently_deep_ray_units_iff
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K)
    (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK) :
    chapter10NormMapsSufficientlyDeepRayUnits N U_K U_L m ↔
      ∃ n : Chapter10Modulus PlacesL,
        Subgroup.map N (U_L.unit n) ≤ U_K.unit m := Iff.rfl

def chapter10RayNormCompatibility
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K) (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK) (n : Chapter10Modulus PlacesL) : Prop :=
  Subgroup.map N (U_L.unit n) ≤ U_K.unit m

theorem chapter10_ray_norm_compatibility_iff
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K) (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK) (n : Chapter10Modulus PlacesL) :
    chapter10RayNormCompatibility N U_K U_L m n ↔
      Subgroup.map N (U_L.unit n) ≤ U_K.unit m := Iff.rfl

/-- The quotient map induced by a norm-compatible pair of ray levels. -/
def chapter10RayQuotientNorm
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K) (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK) (n : Chapter10Modulus PlacesL)
    (hcompat : chapter10RayNormCompatibility N U_K U_L m n) :
    chapter10RayQuotient U_L n →* chapter10RayQuotient U_K m := by
  classical
  refine QuotientGroup.lift (U_L.unit n)
    ((QuotientGroup.mk' (U_K.unit m)).comp N) ?_
  intro x hx
  sorry

theorem chapter10_ray_quotient_norm_mk
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K) (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK) (n : Chapter10Modulus PlacesL)
    (hcompat : chapter10RayNormCompatibility N U_K U_L m n) (x : I_L) :
    chapter10RayQuotientNorm N U_K U_L m n hcompat
        (QuotientGroup.mk' (U_L.unit n) x) =
      QuotientGroup.mk' (U_K.unit m) (N x) := by
  rfl

theorem chapter10_norm_induces_ray_quotient_map
    {I_K I_L PlacesK PlacesL : Type*}
    [CommGroup I_K] [CommGroup I_L]
    (N : I_L →* I_K) (U_K : Chapter10RayUnitSystem I_K PlacesK)
    (U_L : Chapter10RayUnitSystem I_L PlacesL)
    (m : Chapter10Modulus PlacesK)
    (n : Chapter10Modulus PlacesL)
    (hcompat : chapter10RayNormCompatibility N U_K U_L m n) :
    ∃ f : chapter10RayQuotient U_L n →* chapter10RayQuotient U_K m,
      ∀ x, f (QuotientGroup.mk' (U_L.unit n) x) =
        QuotientGroup.mk' (U_K.unit m) (N x) :=
  ⟨chapter10RayQuotientNorm N U_K U_L m n hcompat,
    fun _ => chapter10_ray_quotient_norm_mk N U_K U_L m n hcompat _⟩

/- The positivity part of a ray modulus is handled by the local complex/real
norm theorem above; no surjectivity of the resulting ray map is asserted. -/

end
end LastLib.Book04AdelesAndIdeles.Chapter10
