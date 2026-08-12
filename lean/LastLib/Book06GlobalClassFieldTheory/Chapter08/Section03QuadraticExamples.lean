import LastLib.Book06GlobalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter08

noncomputable section

open NumberField
open scoped nonZeroDivisors

universe u

/-! ## 8.3. Imaginary and real quadratic examples -/

def chapter08ImaginaryQuadratic
    (K : Type u) [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K] : Prop :=
  ∀ _v : Chapter08RealPlace K, False

theorem chapter08_imaginary_quadratic_has_no_real_places
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (hK : chapter08ImaginaryQuadratic K) :
    ∀ _v : Chapter08RealPlace K, False := by
  exact hK

theorem chapter08_imaginary_and_narrow_class_groups_coincide
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (hK : chapter08ImaginaryQuadratic K)
    (N : Chapter08NarrowClassGroupData K) :
    Nonempty (chapter08NarrowClassGroup N ≃*
      chapter08OrdinaryClassGroup K) := by
  sorry

theorem chapter08_imaginary_hilbert_degree_of_cyclic_class_group
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (H : Chapter08HilbertClassFieldData K)
    (hcyclic : IsCyclic (chapter08OrdinaryClassGroup K))
    {h : ℕ}
    (hcard : Fintype.card (chapter08OrdinaryClassGroup K) = h) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    IsCyclic (Gal(chapter08HilbertClassField H / K)) ∧
      Nat.card (Gal(chapter08HilbertClassField H / K)) = h ∧
        Module.finrank K (chapter08HilbertClassField H) = h := by
  sorry

theorem chapter08_imaginary_hilbert_splitting_iff_principal
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (hK : chapter08ImaginaryQuadratic K)
    (H : Chapter08HilbertClassFieldData K)
    {p : Ideal (𝓞 K)} [p.IsPrime]
    (hp : chapter08PrimeAwayFromModulus (chapter08TrivialModulus K) p) :
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    letI : Algebra (𝓞 K) (𝓞 H.carrier) := inferInstance
    chapter08SplitsCompletely K (chapter08HilbertClassField H) p ↔
      ∃ a : 𝓞 K, p = Ideal.span {a} := by
  sorry

theorem chapter08_imaginary_ordinary_and_narrow_hilbert_fields_coincide
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (hK : chapter08ImaginaryQuadratic K)
    (H : Chapter08HilbertClassFieldData K)
    (N : Chapter08NarrowClassGroupData K)
    (HN : Chapter08NarrowHilbertClassFieldData K N) :
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
      chapter08NarrowHilbertClassField HN) := by
  sorry

/-! The `ℚ(√-5)` calculation. -/

theorem chapter08_minusFive_minkowski_bound_value
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (_D : Chapter08MinusFiveData K) :
    chapter08MinusFiveMinkowskiBound = (2 / Real.pi) * Real.sqrt 20 := by
  rfl

theorem chapter08_minusFive_minkowski_bound_lt_three
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (_D : Chapter08MinusFiveData K) :
    chapter08MinusFiveMinkowskiBound < 3 := by
  sorry

theorem chapter08_minusFive_minkowski_representative
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) :
    ∀ C : chapter08OrdinaryClassGroup K,
      ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = C ∧
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ chapter08MinusFiveMinkowskiBound := by
  sorry

theorem chapter08_minusFive_only_prime_above_two_can_be_nontrivial
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    {I : (Ideal (𝓞 K))⁰}
    (hI : Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 2)
    (hnontrivial : ClassGroup.mk0 I ≠ 1) :
    (I : Ideal (𝓞 K)) = chapter08MinusFivePrime D := by
  sorry

theorem chapter08_minusFive_prime_is_prime
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) :
    (chapter08MinusFivePrime D).IsPrime := by
  sorry

theorem chapter08_minusFive_prime_square
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) :
    chapter08MinusFivePrime D ^ 2 = Ideal.span {(2 : 𝓞 K)} := by
  sorry

theorem chapter08_minusFive_norm_equation_has_no_solution :
    chapter08MinusFiveNormEquationNoSolution := by
  sorry

theorem chapter08_minusFive_prime_is_not_principal
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) :
    ¬∃ a : 𝓞 K, chapter08MinusFivePrime D = Ideal.span {a} := by
  sorry

theorem chapter08_minusFive_class_group_is_order_two
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) :
    Nonempty (chapter08OrdinaryClassGroup K ≃*
      Multiplicative (ZMod 2)) := by
  sorry

/-! The biquadratic Hilbert class field `K(√5) = ℚ(i,√5)`. -/

theorem chapter08_minusFive_quadratic_discriminants
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    chapter08QuadraticDiscriminants = {-4, 5, -20} := by
  exact W.quadraticDiscriminants

theorem chapter08_minusFive_discriminant_product :
    chapter08DiscriminantProduct (-4) 5 (-20) = 400 := by
  norm_num [chapter08DiscriminantProduct]

theorem chapter08_minusFive_absolute_discriminant
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    letI : Field W.H := W.fieldH
    letI : Algebra K W.H := W.algebraKH
    letI : NumberField W.H := W.numberFieldH
    letI : FiniteDimensional K W.H := W.finiteKH
    letI : IsAbelianGalois K W.H := W.abelianGaloisKH
    NumberField.discr W.H = (400 : ℤ) := by
  exact W.absoluteDiscriminant

theorem chapter08_minusFive_relative_discriminant_norm_one
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    Ideal.absNorm W.relativeDiscriminant = 1 := by
  exact W.relativeDiscriminantNorm

theorem chapter08_minusFive_discriminant_tower_formula
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    letI : Field W.H := W.fieldH
    letI : Algebra K W.H := W.algebraKH
    letI : NumberField W.H := W.numberFieldH
    letI : FiniteDimensional K W.H := W.finiteKH
    letI : IsAbelianGalois K W.H := W.abelianGaloisKH
    Int.natAbs (NumberField.discr W.H) =
      Int.natAbs (NumberField.discr K) ^ 2 * Ideal.absNorm W.relativeDiscriminant := by
  sorry

theorem chapter08_minusFive_hilbert_generators
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    letI : Field W.H := W.fieldH
    letI : Algebra K W.H := W.algebraKH
    letI : NumberField W.H := W.numberFieldH
    letI : FiniteDimensional K W.H := W.finiteKH
    letI : IsAbelianGalois K W.H := W.abelianGaloisKH
    W.i ^ 2 = (-1 : W.H) ∧
      W.sqrtFive ^ 2 = (5 : W.H) ∧
        algebraMap K W.H (algebraMap (𝓞 K) K D.omega) = W.i * W.sqrtFive := by
  exact ⟨W.i_square, W.sqrtFive_square, W.omega_image⟩

theorem chapter08_minusFive_relative_discriminant_is_unit
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    W.relativeDiscriminant = ⊤ := by
  sorry

theorem chapter08_minusFive_hilbert_field_is_finite_unramified
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    letI : Field W.H := W.fieldH
    letI : Algebra K W.H := W.algebraKH
    letI : NumberField W.H := W.numberFieldH
    letI : FiniteDimensional K W.H := W.finiteKH
    letI : IsAbelianGalois K W.H := W.abelianGaloisKH
    letI : Algebra (𝓞 K) (𝓞 W.H) := inferInstance
    chapter08UnramifiedAtFinitePlaces K W.H := by
  sorry

theorem chapter08_minusFive_hilbert_field_identification
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D) :
    letI : Field W.H := W.fieldH
    letI : Algebra K W.H := W.algebraKH
    letI : NumberField W.H := W.numberFieldH
    letI : FiniteDimensional K W.H := W.finiteKH
    letI : IsAbelianGalois K W.H := W.abelianGaloisKH
    Algebra.adjoin K ({W.sqrtFive} : Set W.H) = ⊤ ∧
      Algebra.adjoin ℚ ({W.i, W.sqrtFive} : Set W.H) = ⊤ := by
  exact ⟨W.relativeAdjoin, W.absoluteAdjoin⟩

theorem chapter08_minusFive_hilbert_field_is_the_hilbert_class_field
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K)
    (W : Chapter08MinusFiveHilbertWitness D)
    (H : Chapter08HilbertClassFieldData K) :
    letI : Field W.H := W.fieldH
    letI : Algebra K W.H := W.algebraKH
    letI : NumberField W.H := W.numberFieldH
    letI : FiniteDimensional K W.H := W.finiteKH
    letI : IsAbelianGalois K W.H := W.abelianGaloisKH
    letI : Field H.carrier := H.carrierField
    letI : Algebra K H.carrier := H.carrierAlgebra
    letI : NumberField H.carrier := H.carrierNumberField
    letI : FiniteDimensional K H.carrier := H.carrierFinite
    letI : IsAbelianGalois K H.carrier := H.carrierAbelianGalois
    Nonempty (W.H ≃ₐ[K] chapter08HilbertClassField H) := by
  sorry

/-! Real quadratic fields and the ordinary/narrow distinction. -/

theorem chapter08_real_quadratic_norm_minus_one_gives_all_sign_patterns
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (hnorm : chapter08HasUnitNormMinusOne K) :
    chapter08RealQuadraticSignMapSurjective K := by
  sorry

theorem chapter08_real_quadratic_narrow_equals_ordinary_if_norm_minus_one
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (N : Chapter08NarrowClassGroupData K)
    (hnorm : chapter08HasUnitNormMinusOne K) :
    Nonempty (chapter08NarrowClassGroup N ≃*
      chapter08OrdinaryClassGroup K) := by
  sorry

theorem chapter08_real_quadratic_narrow_class_number_twice_if_no_norm_minus_one
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (N : Chapter08NarrowClassGroupData K)
    (hnorm : ¬chapter08HasUnitNormMinusOne K) :
    chapter08NarrowClassNumber N = 2 * chapter08ClassNumber K := by
  sorry

theorem chapter08_real_quadratic_narrow_class_number_eq_ordinary_if_norm_minus_one
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (N : Chapter08NarrowClassGroupData K)
    (hnorm : chapter08HasUnitNormMinusOne K) :
    chapter08NarrowClassNumber N = chapter08ClassNumber K := by
  sorry

theorem chapter08_real_quadratic_extra_finite_unramified_extension
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K]
    (hnoNormMinusOne : ¬chapter08HasUnitNormMinusOne K) :
    Nonempty (Chapter08RealQuadraticExtraExtensionData K) := by
  sorry

/-- “Everywhere unramified” is the conjunction that remembers the infinite places. -/
def chapter08EverywhereUnramified
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] : Prop :=
  chapter08UnramifiedAtFinitePlaces K L ∧ chapter08RealPlacesStayReal K L

theorem chapter08_everywhere_unramified_requires_an_infinite_place_convention
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] :
    chapter08EverywhereUnramified K L ↔
      chapter08UnramifiedAtFinitePlaces K L ∧ chapter08RealPlacesStayReal K L := by
  rfl

end
end LastLib.Book06GlobalClassFieldTheory.Chapter08
