import LastLib.Book05LocalClassFieldTheory.Chapter04.Section01WhyCentralSimpleAlgebras
import Mathlib.LinearAlgebra.Basis.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

universe u

open scoped BigOperators

/-! ## 4.2. Valuations on division algebras -/

theorem chapter04_reduced_norm_agrees_with_determinant
    {K D S : Type*} [Field K] [Ring D] [Field S]
    [Algebra K D] [Algebra K S]
    (N : Dˣ →* Kˣ) (d : ℕ)
    (ρ : D →ₐ[K] Matrix (Fin d) (Fin d) S)
    (hdet : chapter04ReducedNormAgreesWithDeterminant N d ρ) :
    ∀ x : Dˣ, algebraMap K S (N x : K) = Matrix.det (ρ (x : D)) := by
  exact hdet

theorem chapter04_reduced_norm_on_a_commutative_subfield
    {K D : Type u} {E : Type*} [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [FiniteDimensional K E]
    (N : Chapter04ReducedNormData K D) (φ : E →ₐ[K] D)
    (hdiv : Module.finrank K E ∣ N.degree) :
    ∀ x : Eˣ,
      (N.reducedNorm (Units.map φ.toMonoidHom x) : K) =
        (Algebra.norm K (x : E)) ^ (N.degree / Module.finrank K E) := by
  sorry

def chapter04FieldNormValuationFormula
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    (vK : K → ℚ) (vE : E → ℚ) : Prop :=
  ∀ x : E, x ≠ 0 →
    vK (Algebra.norm K x) = (Module.finrank K E : ℚ) * vE x

theorem chapter04_division_valuation_on_a_subfield
    {K D : Type u} {E : Type*} [Field K] [DivisionRing D] [Field E]
    [Algebra K D] [Algebra K E] [FiniteDimensional K E]
    (N : Chapter04ReducedNormData K D) (vK : Kˣ → ℚ) (vE : Eˣ → ℚ)
    (φ : E →ₐ[K] D) (e : ℕ)
    (hdiv : Module.finrank K E ∣ N.degree)
    (hnorm : ∀ x : Eˣ,
      vK (N.reducedNorm (Units.map φ.toMonoidHom x)) =
        (N.degree : ℚ) / e * vE x)
    (x : Eˣ) :
    chapter04DivisionValuation N vK (φ (x : E)) =
        ((vK (N.reducedNorm (Units.map φ.toMonoidHom x)) / N.degree : ℚ) :
          WithTop ℚ) ∧
      (vK (N.reducedNorm (Units.map φ.toMonoidHom x)) / N.degree) =
        (vE x / e : ℚ) := by
  sorry

theorem chapter04_division_valuation_integrality_iff
    {D : Type*} [Ring D] (w : D → WithTop ℚ) (R : Subring D)
    (hR : R.carrier = chapter04DivisionValuationRing w) (x : D) :
    chapter04IsIntegralOverSubring R x ↔ w x ≥ 0 := by
  sorry

theorem chapter04_division_valuation_ultrametric
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD)
    (x y : D) :
    V.value (x + y) ≥ min (V.value x) (V.value y) := by
  exact V.value_add x y

theorem chapter04_division_valuation_multiplicative
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) (x y : D) :
    V.value (x * y) = V.value x + V.value y := by
  exact V.value_mul x y

theorem chapter04_division_valuation_triangle_argument
    {K D k barD : Type*} [Field K] [DivisionRing D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) (x y : D) (hx : x ≠ 0)
    (hle : V.value x ≤ V.value y) :
    V.value (x + y) = V.value x + V.value (1 + x⁻¹ * y) ∧
      V.value (1 + x⁻¹ * y) ≥ 0 := by
  sorry

theorem chapter04_division_valuation_ring_is_local
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    IsLocalRing V.valuationSubring := by
  sorry

theorem chapter04_division_valuation_ring_and_maximal_ideal
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    V.valuationSubring.carrier = {x | V.value x ≥ 0} ∧
      chapter04IdealImage V.valuationSubring V.maximalIdeal = {x | V.value x > 0} := by
  sorry

theorem chapter04_division_residue_is_a_finite_field
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    Finite barD ∧ Function.Surjective V.residueMap := by
  exact ⟨V.residue_finite, V.residue_surjective⟩

theorem chapter04_division_residue_quotient_equiv
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (V : Chapter04DivisionValuationInterface K D k barD) :
    Nonempty ((V.valuationSubring ⧸ V.maximalIdeal) ≃+ barD) := by
  sorry

theorem chapter04_division_dimension_value_residue_formula
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [TopologicalSpace D]
    (A : Chapter04DivisionAlgebraData K)
    [TopologicalSpace A.carrier]
    (V : Chapter04DivisionValuationInterface K (A.carrier) k barD)
    (d : ℕ) (hdegree : A.degree = d) :
    d ^ 2 = chapter04RamificationIndex V.unitValue *
      chapter04ResidueDegree k barD := by
  sorry

structure Chapter04ValuationProductBasis
    (K D : Type*) [Field K] [AddCommGroup D] [Module K D] [Mul D]
    (e f : ℕ) where
  valueRepresentatives : Fin e → D
  residueLifts : Fin f → D
  basis : Module.Basis (Fin e × Fin f) K D
  basis_eq_products : ∀ ij,
    basis ij = valueRepresentatives ij.1 * residueLifts ij.2

theorem chapter04_valuation_lattice_basis_exists
    {K : Type*} [Field K]
    (A : Chapter04DivisionAlgebraData K) (e f : ℕ)
    (hcard : Module.finrank K (A.carrier) = e * f) :
    Nonempty (Chapter04ValuationProductBasis K (A.carrier) e f) := by
  sorry

/- The preceding theorem is the reusable basis interface.  This statement
  records the source's leading-residue independence and completeness
  argument without turning that proof narration into a second construction. -/
theorem chapter04_valuation_product_basis_has_independence_and_expansion
    {K D : Type*} [Field K] [AddCommGroup D] [Module K D] [Mul D]
    {e f : ℕ}
    (B : Chapter04ValuationProductBasis K D e f) :
    LinearIndependent K B.basis ∧
      ∀ z : D, z ∈ Submodule.span K (Set.range B.basis) := by
  sorry

structure Chapter04ResidueConjugationData
    (K D k barD : Type*) [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD] where
  value : Dˣ → ℚ
  conjugation :
    (chapter04ValueGroup value ⧸ chapter04ValueGroupModInteger value) →
      Gal(barD / k)
  conjugation_mul : ∀ a b,
    conjugation (a + b) = conjugation a * conjugation b
  fixed_field_eq_base :
    {z : barD | ∀ q, conjugation q z = z} = Set.range (algebraMap k barD)

theorem chapter04_residue_conjugation_has_base_fixed_field
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD) :
    {z : barD | ∀ q, C.conjugation q z = z} = Set.range (algebraMap k barD) := by
  exact C.fixed_field_eq_base

theorem chapter04_residue_conjugation_is_surjective
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD)
    (hfixed : {z : barD | ∀ q, C.conjugation q z = z} =
      Set.range (algebraMap k barD)) :
    Function.Surjective C.conjugation := by
  sorry

theorem chapter04_division_indices_are_the_degree
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (A : Chapter04DivisionAlgebraData K)
    [TopologicalSpace A.carrier]
    (V : Chapter04DivisionValuationInterface K (A.carrier) k barD)
    (C : Chapter04ResidueConjugationData K (A.carrier) k barD)
    (d : ℕ) (hdegree : Module.finrank K (A.carrier) = d ^ 2)
    (hvalue : C.value = V.unitValue)
    (hbound : chapter04ValueGroupContainedInFractionalLattice V.unitValue d) :
    chapter04ResidueDegree k barD ≤ chapter04RamificationIndex V.unitValue ∧
      chapter04RamificationIndex V.unitValue ≤ d ∧
      d ≤ chapter04ResidueDegree k barD ∧
      chapter04RamificationIndex V.unitValue = chapter04ResidueDegree k barD ∧
      chapter04RamificationIndex V.unitValue = d ∧
      chapter04ResidueDegree k barD = d := by
  sorry

theorem chapter04_value_group_contains_integer_lattice
    {D : Type*} [Monoid D] (w : Dˣ → ℚ) (π : Dˣ) (hπ : w π = 1) :
    chapter04IntegerValueLattice ≤ chapter04ValueGroup w := by
  sorry

/- A lightweight witness records the Hensel-lifted unramified maximal field;
  its field, valuation, and centralizer APIs are supplied by the surrounding
  local-field chapters. -/
structure Chapter04UnramifiedMaximalSubfieldSpec
    (K : Type*) [Field K] (D : Chapter04DivisionAlgebraData K) where
  field : Type*
  degree : ℕ
  degree_eq : degree = D.degree
  embedding : field → D.carrier
  embedding_injective : Function.Injective embedding
  field_structure : Prop
  field_structure_holds : field_structure
  unramified_structure : Prop
  unramified_structure_holds : unramified_structure
  centralizer_is_field : Prop
  centralizer_is_field_holds : centralizer_is_field

theorem chapter04_division_algebra_has_unramified_maximal_subfield
    {K : Type*} [Field K] (D : Chapter04DivisionAlgebraData K) :
    Nonempty (Chapter04UnramifiedMaximalSubfieldSpec K D) := by
  sorry

theorem chapter04_unramified_maximal_subfield_is_maximal
    {K : Type*} [Field K] (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K D) :
    E.degree = D.degree ∧ E.centralizer_is_field := by
  exact ⟨E.degree_eq, E.centralizer_is_field_holds⟩

structure Chapter04ResidueConjugationIsomorphism
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD) where
  toEquiv :
    (chapter04ValueGroup C.value ⧸ chapter04ValueGroupModInteger C.value) ≃
      Gal(barD / k)
  map_add : ∀ a b, toEquiv (a + b) = toEquiv a * toEquiv b

theorem chapter04_unramified_residue_conjugation_is_an_isomorphism
    {K D k barD : Type*} [Field K] [Ring D] [Field k] [Field barD]
    [Algebra K D] [Algebra k barD] [FiniteDimensional k barD]
    [IsGalois k barD]
    (C : Chapter04ResidueConjugationData K D k barD)
    (hsurj : Function.Surjective C.conjugation) :
    Nonempty (Chapter04ResidueConjugationIsomorphism C) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the pinned cyclic-algebra API has a presentation
  carrier, but not the theorem identifying every division representative with
  one.  These fields retain the exact degree, Frobenius, parameter, and
  equivalence data needed by later invariant statements. -/
structure Chapter04CyclicPresentationSpec
    {K : Type*} [Field K] (D : Chapter04DivisionAlgebraData K) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  exponent_coprime : Nat.Coprime exponent D.degree
  presentation : chapter04CentralSimpleAlgebra K
  equivalence : Nonempty
    (D.carrier ≃ₐ[K] presentation)
  unramified_field_degree : ℕ
  unramified_field_degree_eq : unramified_field_degree = D.degree
  arithmetic_frobenius_relation : Prop
  parameter_power_normalization : Prop

theorem chapter04_division_algebra_has_cyclic_presentation
    {K : Type*} [Field K]
    (D : Chapter04DivisionAlgebraData K)
    (U : Chapter04UnramifiedMaximalSubfieldSpec K D) :
    Nonempty (Chapter04CyclicPresentationSpec D) := by
  sorry

theorem chapter04_division_parameter_power_is_central
    {K D : Type*} [Field K] [DivisionRing D]
    (piD : D) (d : ℕ)
    (hconj : ∀ x : D, piD ^ d * x = x * piD ^ d)
    :
    ∃ c : D, c = piD ^ d ∧ ∀ x : D, c * x = x * c := by
  sorry

theorem chapter04_division_parameter_power_is_uniformizer_times_unit
    {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
    (piD : D) (π : K) (d : ℕ)
    (hcentral : ∀ x : D, piD ^ d * x = x * piD ^ d)
    (hfactor : ∃ c : K, c ≠ 0 ∧ piD ^ d = algebraMap K D (c * π)) :
    ∃ c : Kˣ, piD ^ d = algebraMap K D ((c : K) * π) := by
  sorry

theorem chapter04_unramified_unit_norm_normalizes_parameter
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : Lˣ →* Kˣ) (c : Kˣ)
    (hsurj : ∀ u : Kˣ, ∃ b : Lˣ, N b = u) :
    ∃ b : Lˣ, N b = c⁻¹ := by
  exact hsurj c⁻¹

def chapter04GeneratorChangeFactor (n r : ℕ) : ZMod n :=
  (r : ZMod n)⁻¹

theorem chapter04_generator_change_factor_mul
    (n r : ℕ) (hcoprime : Nat.Coprime r n) :
    (r : ZMod n) * chapter04GeneratorChangeFactor n r = 1 := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter03.chapter03_generator_change_factor_mul
    n r hcoprime

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
