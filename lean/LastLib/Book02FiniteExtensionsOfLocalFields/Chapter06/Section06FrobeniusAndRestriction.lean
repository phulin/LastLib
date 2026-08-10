import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section05TraceAndNormUnderFiniteFieldFrobenius

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Set

/-! ## 6.6. Frobenius and restriction -/

/- The unique intermediate finite field of each allowed degree. -/
theorem chapter06_unique_intermediate_field_of_degree
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (f d : ℕ) (hdegree : Module.finrank k Kf = f) (hdvd : d ∣ f) :
    ∃! E : IntermediateField k Kf, Module.finrank k E = d := by
  sorry

/- The residue cardinality of the degree-`d` intermediate field is `q^d`. -/
theorem chapter06_intermediate_field_cardinality
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) (d : ℕ)
    (hdegree : Module.finrank k E = d) :
    Nat.card E = Nat.card k ^ d := by
  sorry

/- Arithmetic Frobenius restricts to arithmetic Frobenius on every intermediate field. -/
theorem chapter06_restriction_arithmetic_frobenius
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Normal k E] :
    AlgEquiv.restrictNormal (chapter06ArithmeticFrobenius k Kf) E =
      chapter06ArithmeticFrobenius k E := by
  sorry

/- In the tower `Kf / E / k`, relative arithmetic Frobenius is the `k`-Frobenius power
    determined by the intermediate residue degree. -/
theorem chapter06_relative_arithmetic_frobenius_is_degree_power
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Fintype E]
    (d : ℕ) (hdegree : Module.finrank k E = d) :
    chapter06ArithmeticFrobeniusRingEquiv E Kf =
      (chapter06ArithmeticFrobeniusRingEquiv k Kf) ^ d := by
  sorry

/- The corresponding geometric Frobenius identity is obtained by inversion. -/
theorem chapter06_relative_geometric_frobenius_is_degree_power
    (k Kf : Type*) [Field k] [Fintype k] [Field Kf] [Finite Kf]
    [Algebra k Kf] [FiniteDimensional k Kf]
    (E : IntermediateField k Kf) [Fintype E]
    (d : ℕ) (hdegree : Module.finrank k E = d) :
    chapter06GeometricFrobeniusRingEquiv E Kf =
      (chapter06GeometricFrobeniusRingEquiv k Kf) ^ d := by
  sorry

/- A compatible map of Galois quotients carries the Frobenius coset to the
    corresponding Frobenius coset.  This models restriction to a subextension
    and passage to a ramified quotient without choosing compatible lifts. -/
theorem chapter06_quotient_map_carries_frobenius_coset
    {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']
    (I : Subgroup G) (I' : Subgroup G') [I.Normal] [I'.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I)
    (D' : Chapter06RamifiedGaloisReduction G' H' I')
    (φ : G →* G') (ψ : H →* H') (α : H) (α' : H')
    (hcompat : ∀ g : G,
      D'.quotientEquiv (QuotientGroup.mk' I' (φ g)) =
        ψ (D.quotientEquiv (QuotientGroup.mk' I g)))
    (hfrob : ψ α = α') (g : G) :
    g ∈ chapter06ArithmeticFrobeniusCoset I D α ↔
      φ g ∈ chapter06ArithmeticFrobeniusCoset I' D' α' := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
