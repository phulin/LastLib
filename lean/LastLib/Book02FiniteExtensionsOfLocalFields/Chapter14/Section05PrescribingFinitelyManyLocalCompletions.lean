import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14.Section04WeakApproximationForCoefficients

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open Polynomial
open IntermediateField
open scoped BigOperators TensorProduct

universe u v w

/-! ## 14.5. Prescribing finitely many local completions -/

theorem chapter14_finite_local_extensions_over_characteristic_zero_are_separable
    {K L : Type*} [Field K] [Field L] [CharZero K]
    [Algebra K L] [FiniteDimensional K L] :
    Algebra.IsSeparable K L := by
  sorry

theorem chapter14_local_extension_has_a_primitive_polynomial
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ α : L, Nonempty (L ≃ₐ[K] K⟮α⟯) ∧
      (minpoly K α).Monic ∧
      Irreducible (minpoly K α) ∧
      (minpoly K α).natDegree = Module.finrank K L := by
  sorry

/- If a local minimal polynomial has degree smaller than `n`, its unused
   degree can be filled by distinct linear factors avoiding its roots. -/
theorem chapter14_fill_unused_degree_with_distinct_linear_factors
    {K : Type*} [Field K] [Infinite K]
    (f : K[X]) (hfmonic : f.Monic) (hfsep : f.Separable)
    (d n : ℕ) (hdegree : f.natDegree = d) (hle : d ≤ n) :
    ∃ q : K[X], q.Monic ∧ q.natDegree = n - d ∧
      (f * q).Separable ∧
      ∀ x : K, q.eval x = 0 → f.eval x ≠ 0 := by
  sorry

def chapter14FilledLocalPolynomial
    {K : Type*} [Semiring K] (f q : K[X]) : K[X] :=
  f * q

theorem chapter14_filled_local_polynomial_is_monic_separable
    {K : Type*} [Field K] (f q : K[X])
    (hf : f.Monic) (hq : q.Monic) (hsep : (f * q).Separable) :
    (chapter14FilledLocalPolynomial f q).Monic ∧
      (chapter14FilledLocalPolynomial f q).Separable := by
  exact ⟨hf.mul hq, by simpa [chapter14FilledLocalPolynomial] using hsep⟩

def chapter14EisensteinAtPlace
    {F : Type u} [Field F] [NumberField F]
    (v : Chapter14Prime F) (g : (chapter14BaseCompletion F v)[X]) : Prop :=
  ∃ h : (v.adicCompletionIntegers F)[X],
    h.map (algebraMap (v.adicCompletionIntegers F)
      (chapter14BaseCompletion F v)) = g ∧
      h.IsEisensteinAt (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))

structure Chapter14AuxiliaryEisensteinData
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ) where
  place : Chapter14Prime F
  outside : place ∉ S
  polynomial : (chapter14BaseCompletion F place)[X]
  monic : polynomial.Monic
  degree : polynomial.natDegree = n
  eisenstein : chapter14EisensteinAtPlace place polynomial

theorem chapter14_exists_auxiliary_eisenstein_place
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ) (hn : 0 < n) :
    Nonempty (Chapter14AuxiliaryEisensteinData S n) := by
  sorry

theorem chapter14_eisenstein_at_place_is_open
    {F : Type u} [Field F] [NumberField F]
    (v : Chapter14Prime F) (n : ℕ)
    [TopologicalSpace ((chapter14BaseCompletion F v)[X])] :
    IsOpen {g : (chapter14BaseCompletion F v)[X] |
      chapter14EisensteinAtPlace v g ∧ g.natDegree = n} := by
  sorry

theorem chapter14_eisenstein_at_place_implies_irreducible
    {F : Type u} [Field F] [NumberField F]
    (v : Chapter14Prime F) (g : (chapter14BaseCompletion F v)[X])
    (hg : chapter14EisensteinAtPlace v g) :
    Irreducible g := by
  sorry

theorem chapter14_global_polynomial_irreducible_from_auxiliary_place
    {F : Type u} [Field F] [NumberField F]
    (v : Chapter14Prime F) (g : F[X])
    (hg : chapter14EisensteinAtPlace v (chapter14PolynomialMapAt v g)) :
    Irreducible g := by
  sorry

/- The quotient `F[T]/(g)` is the global field produced by the polynomial. -/
def chapter14GlobalPolynomialQuotient
    {F : Type*} [Field F] (g : F[X]) : Type _ :=
  AdjoinRoot g

theorem chapter14_global_quotient_tensor_product_is_local_polynomial_quotient
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (g : F[X]) :
    Nonempty
      (AdjoinRoot g ⊗[F] K ≃+*
        AdjoinRoot (g.map (algebraMap F K))) := by
  sorry

def chapter14BaseNumberFieldModel
    {F : Type u} [Field F] [NumberField F] :
    Chapter14NumberFieldModel F :=
  { carrier := F
    field_carrier := inferInstance
    number_field_carrier := inferInstance
    algebra := Algebra.id F
    finite_dimensional := inferInstance }

theorem chapter14_global_polynomial_quotient_is_a_number_field
    {F : Type u} [Field F] [NumberField F]
    (g : F[X]) (hgmonic : g.Monic) (hgirreducible : Irreducible g) :
    ∃ M : Chapter14NumberFieldModel F,
      M.carrier = chapter14GlobalPolynomialQuotient g ∧
        chapter14ModelDegree M = g.natDegree := by
  sorry

/- The local coefficient conditions are open and can therefore be imposed at
   the auxiliary place and at each prescribed place simultaneously. -/
structure Chapter14LocalPolynomialFactorCondition
    {F : Type u} [Field F] [NumberField F]
    (p : Chapter14Prime F) (L : Type v) [Field L]
    [Algebra (chapter14BaseCompletion F p) L]
    [TopologicalSpace ((chapter14BaseCompletion F p)[X])] where
  polynomial : (chapter14BaseCompletion F p)[X]
  monic : polynomial.Monic
  separable : polynomial.Separable
  neighborhood : Set ((chapter14BaseCompletion F p)[X])
  neighborhood_open : IsOpen neighborhood
  neighborhood_contains : polynomial ∈ neighborhood
  factor : (chapter14BaseCompletion F p)[X]
  factor_monic : factor.Monic
  factor_divides : factor ∣ polynomial
  factor_generates : Nonempty (AdjoinRoot factor ≃+* L)

theorem chapter14_theorem_14_1_prescribed_nonarchimedean_completions
    {F : Type u} [Field F] [NumberField F]
    (r : ℕ) (p : Fin r → Chapter14Prime F)
    (hp : Function.Injective p)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (hr : 0 < r) :
    Nonempty (Chapter14ApproximationScope F p L) := by
  sorry

theorem chapter14_theorem_14_1_degree_one_case
    {F : Type u} [Field F] [NumberField F]
    (r : ℕ) (p : Fin r → Chapter14Prime F)
    (hp : Function.Injective p)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (hr : 0 < r)
    (hn : chapter14MaximumLocalDegree p L = 1) :
    ∃ S : Chapter14ApproximationScope F p L,
      chapter14ModelDegree S.model = 1 := by
  sorry

theorem chapter14_theorem_14_1_degree_one_can_take_the_base_field
    {F : Type u} [Field F] [NumberField F]
    (r : ℕ) (p : Fin r → Chapter14Prime F)
    (hp : Function.Injective p)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (hr : 0 < r)
    (hn : chapter14MaximumLocalDegree p L = 1) :
    ∃ S : Chapter14ApproximationScope F p L,
      S.model.carrier = F ∧ chapter14ModelDegree S.model = 1 := by
  sorry

theorem chapter14_theorem_14_1_degree_greater_than_one_case
    {F : Type u} [Field F] [NumberField F]
    (r : ℕ) (p : Fin r → Chapter14Prime F)
    (hp : Function.Injective p)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (hr : 0 < r)
    (hn : 1 < chapter14MaximumLocalDegree p L) :
    ∃ S : Chapter14ApproximationScope F p L,
      1 < chapter14ModelDegree S.model ∧
        chapter14ModelDegree S.model = chapter14MaximumLocalDegree p L := by
  sorry

theorem chapter14_theorem_14_1_selected_factor_is_a_completed_branch
    {F : Type u} [Field F] [NumberField F]
    (r : ℕ) (p : Fin r → Chapter14Prime F)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (S : Chapter14ApproximationScope F p L) (i : Fin r) :
    letI : Field (L i).carrier := (L i).field_carrier
    Nonempty (Chapter14CompletionChoice S.model (p i) (L i).carrier) := by
  sorry

/- A finite separable local algebra is the natural product-valued extension
   of the field-valued theorem. -/
structure Chapter14FiniteSeparableLocalAlgebra
    {F : Type u} [Field F] [NumberField F]
    (p : Chapter14Prime F) (n : ℕ) where
  carrier : Type v
  [comm_ring : CommRing carrier]
  [algebra : Algebra (chapter14BaseCompletion F p) carrier]
  [finite_dimensional : FiniteDimensional (chapter14BaseCompletion F p) carrier]
  dimension :
    letI : CommRing carrier := comm_ring
    letI : Algebra (chapter14BaseCompletion F p) carrier := algebra
    letI : FiniteDimensional (chapter14BaseCompletion F p) carrier := finite_dimensional
    Module.finrank (chapter14BaseCompletion F p) carrier = n
  separable :
    letI : CommRing carrier := comm_ring
    letI : Algebra (chapter14BaseCompletion F p) carrier := algebra
    Algebra.Etale (chapter14BaseCompletion F p) carrier

structure Chapter14AlgebraCompletionChoice
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F)
    [Algebra F (chapter14BaseCompletion F p)]
    (A : Type v) where
  [comm_ring : CommRing A]
  targetBaseMap : chapter14BaseCompletion F p →+* A
  equivalence : chapter14ModelScalarExtension M p ≃+* A
  commutes : ∀ x,
    equivalence (chapter14ModelTensorRightBaseMap M p x) = targetBaseMap x

theorem chapter14_prescribe_finite_separable_local_algebras
    {F : Type u} [Field F] [NumberField F]
    (r n : ℕ) (p : Fin r → Chapter14Prime F)
    (hp : Function.Injective p)
    (A : ∀ i, Chapter14FiniteSeparableLocalAlgebra (p i) n)
    [∀ i, Algebra F (chapter14BaseCompletion F (p i))]
    (hr : 0 < r) :
    ∃ M : Chapter14NumberFieldModel F,
      chapter14ModelDegree M = n ∧
        ∀ i,
          letI : CommRing (A i).carrier := (A i).comm_ring
          Nonempty
            (Chapter14AlgebraCompletionChoice M (p i) (A i).carrier) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
