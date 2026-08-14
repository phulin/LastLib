import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02.Section01RecordingAllPowersOfAnIdeal
import Mathlib.RingTheory.MvPolynomial.Ideal

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators DirectSum
open Polynomial

/-! ## 2.2. Generators, relations, and the symmetric algebra -/

/-- The degree-one linear map from an ideal to its Rees algebra. -/
def chapter02ReesDegreeOneMap
    {R : Type u} [CommRing R] (I : Ideal R) :
    I →ₗ[R] Chapter02ReesAlgebra R I where
  toFun r :=
    ⟨Polynomial.monomial 1 (r : R), by
      rw [reesAlgebra.monomial_mem, pow_one]
      exact r.2⟩
  map_add' := by
    intro r s
    ext
    simp
  map_smul' := by
    intro r s
    ext n
    by_cases h : 1 = n <;> simp [smul_eq_mul, Polynomial.coeff_monomial, h]

/-- The canonical map `Sym_R(I) → R_A(I)`. -/
def chapter02SymmetricToRees
    {R : Type u} [CommRing R] (I : Ideal R) :
    SymmetricAlgebra R I →ₐ[R] Chapter02ReesAlgebra R I :=
  SymmetricAlgebra.lift (chapter02ReesDegreeOneMap I)

@[simp] theorem chapter02_symmetric_to_rees_on_generator
    {R : Type u} [CommRing R] (I : Ideal R) (r : I) :
    chapter02SymmetricToRees I (SymmetricAlgebra.ι R I r) =
      chapter02ReesDegreeOneMap I r := by
  simp [chapter02SymmetricToRees]

theorem chapter02_symmetric_algebra_universal_property
    {R A M : Type u} [CommRing R] [CommRing A] [AddCommGroup M]
    [Module R M] [Algebra R A] (f : M →ₗ[R] A)
    (g : SymmetricAlgebra R M →ₐ[R] A)
    (h : g ∘ₗ SymmetricAlgebra.ι R M = f) :
    g = SymmetricAlgebra.lift f := by
  apply SymmetricAlgebra.algHom_ext
  calc
    g ∘ₗ SymmetricAlgebra.ι R M = f := h
    _ = SymmetricAlgebra.lift f ∘ₗ SymmetricAlgebra.ι R M :=
      (SymmetricAlgebra.lift_comp_ι f).symm

/- LOCAL_DEPENDENCY_GUESS: the symmetric algebra has its standard total-degree internal grading,
which is not packaged by the pinned SymmetricAlgebra API. -/
structure Chapter02SymmetricGradingData
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] where
  component : ℕ → Submodule R (SymmetricAlgebra R M)
  graded : GradedAlgebra component
  generator_mem_degree_one :
    ∀ m : M, SymmetricAlgebra.ι R M m ∈ component 1

theorem chapter02_symmetric_grading_exists
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Nonempty (Chapter02SymmetricGradingData (R := R) (M := M)) := by
  sorry

theorem chapter02_symmetric_algebra_is_free
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    IsSymmetricAlgebra (SymmetricAlgebra.ι R M) := by
  exact SymmetricAlgebra.isSymmetricAlgebra_ι

/- LOCAL_DEPENDENCY_GUESS: the degree-one generators generate all of the Rees algebra, so the
symmetric-algebra map is the source's natural surjection. -/
theorem chapter02_symmetric_to_rees_surjective
    {R : Type u} [CommRing R] (I : Ideal R) :
    Function.Surjective (chapter02SymmetricToRees I) := by
  have hset :
      Set.range (fun r : I => Polynomial.monomial 1 (r : R)) =
        (Submodule.map (monomial 1 : R →ₗ[R] Polynomial R) I :
          Set (Polynomial R)) := by
    ext p
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have hgen :
      Algebra.adjoin R (Set.range (chapter02ReesDegreeOneMap I)) = ⊤ := by
    rw [← (Subalgebra.map_injective (f := (Chapter02ReesAlgebra R I).val)
      Subtype.val_injective).eq_iff]
    rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp]
    have hfun :
        (⇑(Chapter02ReesAlgebra R I).val ∘ chapter02ReesDegreeOneMap I) =
          (fun r : I => Polynomial.monomial 1 (r : R)) := by
      funext r
      rfl
    rw [hfun, Subalgebra.range_val, hset,
        chapter02_rees_generated_by_degree_one I]
  rw [← AlgHom.range_eq_top]
  apply le_antisymm le_top
  rw [← hgen]
  apply Algebra.adjoin_le
  rintro _ ⟨r, rfl⟩
  exact ⟨SymmetricAlgebra.ι R I r, by
    simp [chapter02SymmetricToRees]⟩

def Chapter02SymmetricToReesIsomorphism
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  Function.Bijective (chapter02SymmetricToRees I)

def Chapter02SymmetricToReesMayHaveKernel
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  ¬ Function.Injective (chapter02SymmetricToRees I)

theorem chapter02_symmetric_to_rees_may_have_kernel_iff_not_isomorphism
    {R : Type u} [CommRing R] (I : Ideal R) :
    Chapter02SymmetricToReesMayHaveKernel I ↔
      ¬ Chapter02SymmetricToReesIsomorphism I := by
  simp only [Chapter02SymmetricToReesMayHaveKernel,
    Chapter02SymmetricToReesIsomorphism]
  constructor
  · intro h hIso
    exact h hIso.1
  · intro h hInjective
    exact h ⟨hInjective, chapter02_symmetric_to_rees_surjective I⟩

/-- The Rees element attached to one chosen generator of an ideal. -/
def chapter02ReesGenerator
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) (i : ι) :
    Chapter02ReesAlgebra R I :=
  ⟨Polynomial.monomial 1 (f i), by
    rw [reesAlgebra.monomial_mem, pow_one, hI]
    exact Ideal.subset_span ⟨i, rfl⟩⟩

/-- The presentation map `R[U_i] → R_A(I)` for a chosen generating family. -/
def chapter02FiniteGeneratorMap
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) :
    MvPolynomial ι R →ₐ[R] Chapter02ReesAlgebra R I :=
  MvPolynomial.eval₂AlgHom R (fun i => chapter02ReesGenerator f hI i)

theorem chapter02_finite_generator_map_surjective
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) :
    Function.Surjective (chapter02FiniteGeneratorMap f hI) := by
  rw [← AlgHom.range_eq_top]
  change (MvPolynomial.aeval
      (fun i => chapter02ReesGenerator f hI i)).range = ⊤
  rw [← Algebra.adjoin_range_eq_range_aeval]
  rw [← (Subalgebra.map_injective (f := (Chapter02ReesAlgebra R I).val)
    Subtype.val_injective).eq_iff]
  rw [AlgHom.map_adjoin, Algebra.map_top]
  rw [← Set.range_comp]
  have hfun :
      (⇑(Chapter02ReesAlgebra R I).val ∘
          (fun i => chapter02ReesGenerator f hI i)) =
        (fun i => Polynomial.monomial 1 (f i)) := by
    funext i
    rfl
  rw [hfun]
  rw [Subalgebra.range_val]
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change Polynomial.monomial 1 (f i) ∈ reesAlgebra I
    rw [reesAlgebra.monomial_mem, pow_one, hI]
    exact Ideal.subset_span ⟨i, rfl⟩
  · change reesAlgebra I ≤
      Algebra.adjoin R (Set.range (fun i => Polynomial.monomial 1 (f i)))
    rw [← adjoin_monomial_eq_reesAlgebra]
    apply Algebra.adjoin_le
    rintro _ ⟨r, hr, rfl⟩
    rw [hI] at hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
        rcases hr with ⟨i, rfl⟩
        exact Algebra.subset_adjoin ⟨i, rfl⟩
    | zero =>
        simp
    | add r s hr hs hr' hs' =>
        simpa using (Algebra.adjoin R
          (Set.range (fun i => Polynomial.monomial 1 (f i)))).add_mem hr' hs'
    | smul a r hr hr' =>
        simpa [Polynomial.smul_monomial] using
          (Algebra.adjoin R
            (Set.range (fun i => Polynomial.monomial 1 (f i)))).smul_mem hr' a

/-- The evident Koszul-type relation `f_i U_j - f_j U_i`. -/
def chapter02EvidentGeneratorRelation
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i j : ι) :
    MvPolynomial ι R :=
  MvPolynomial.C (f i) * MvPolynomial.X j -
    MvPolynomial.C (f j) * MvPolynomial.X i

def chapter02GeneratorKernel
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) : Ideal (MvPolynomial ι R) :=
  RingHom.ker (chapter02FiniteGeneratorMap f hI).toRingHom

/-- The ideal generated by the evident pairwise relations. -/
def chapter02EvidentRelationIdeal
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (_hI : I = Ideal.span (Set.range f)) : Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (fun ij : ι × ι =>
    chapter02EvidentGeneratorRelation f ij.1 ij.2))

theorem chapter02_evident_relation_mem_generator_kernel
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) (i j : ι) :
    chapter02EvidentGeneratorRelation f i j ∈ chapter02GeneratorKernel f hI := by
  change chapter02FiniteGeneratorMap f hI
      (chapter02EvidentGeneratorRelation f i j) = 0
  apply Subtype.ext
  ext n
  simp [chapter02FiniteGeneratorMap, chapter02EvidentGeneratorRelation,
    chapter02ReesGenerator, Polynomial.coeff_monomial]
  by_cases h : 1 = n <;> simp [h, mul_comm]

theorem chapter02_evident_relations_le_generator_kernel
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) :
    chapter02EvidentRelationIdeal f hI ≤ chapter02GeneratorKernel f hI := by
  rw [chapter02EvidentRelationIdeal]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact chapter02_evident_relation_mem_generator_kernel f hI i j

def Chapter02RelationsAreComplete
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) : Prop :=
  chapter02EvidentRelationIdeal f hI = chapter02GeneratorKernel f hI

/-- A witness that higher or torsion relations remain after the evident equations. -/
def Chapter02AdditionalReesRelationWitness
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f)) : Prop :=
  ∃ p, p ∈ chapter02GeneratorKernel f hI ∧
    p ∉ chapter02EvidentRelationIdeal f hI

theorem chapter02_additional_relation_witness_excludes_completeness
    {R : Type u} [CommRing R] {I : Ideal R} {ι : Type v}
    (f : ι → R) (hI : I = Ideal.span (Set.range f))
    (h : Chapter02AdditionalReesRelationWitness f hI) :
    ¬ Chapter02RelationsAreComplete f hI := by
  rcases h with ⟨p, hp, hp'⟩
  intro hcomplete
  change chapter02EvidentRelationIdeal f hI = chapter02GeneratorKernel f hI at hcomplete
  apply hp'
  rw [hcomplete]
  exact hp

/-!
On the chart obtained by inverting `f_i`, the ratio of the `j`th coordinate to the `i`th one is
the corresponding fraction `f_j/f_i`.  The statement is made in `Localization.Away (f_i)` so the
denominator hypothesis is explicit.
-/

def chapter02ChartRatio
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i j : ι) :
    Localization.Away (f i) :=
  algebraMap R (Localization.Away (f i)) (f j) *
    IsLocalization.Away.invSelf (f i)

theorem chapter02_chart_ratio_mul_denominator
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i j : ι) :
    algebraMap R (Localization.Away (f i)) (f i) * chapter02ChartRatio f i j =
      algebraMap R (Localization.Away (f i)) (f j) := by
  unfold chapter02ChartRatio
  calc
    algebraMap R (Localization.Away (f i)) (f i) *
        (algebraMap R (Localization.Away (f i)) (f j) *
          IsLocalization.Away.invSelf (f i)) =
      (algebraMap R (Localization.Away (f i)) (f i) *
        IsLocalization.Away.invSelf (f i)) *
        algebraMap R (Localization.Away (f i)) (f j) := by ac_rfl
    _ = 1 * algebraMap R (Localization.Away (f i)) (f j) := by
      rw [IsLocalization.Away.mul_invSelf]
    _ = algebraMap R (Localization.Away (f i)) (f j) := by simp

def Chapter02ChartCoordinateRelation
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i : ι)
    (u : ι → Localization.Away (f i)) : Prop :=
  ∀ j, u j = chapter02ChartRatio f i j

theorem chapter02_chart_coordinates_are_ratios
    {R : Type u} [CommRing R] {ι : Type v} (f : ι → R) (i : ι)
    (u : ι → Localization.Away (f i))
    (hu : ∀ j,
      algebraMap R (Localization.Away (f i)) (f i) * u j =
        algebraMap R (Localization.Away (f i)) (f j)) :
    Chapter02ChartCoordinateRelation f i u := by
  intro j
  calc
    u j = 1 * u j := by simp
    _ = (algebraMap R (Localization.Away (f i)) (f i) *
        IsLocalization.Away.invSelf (f i)) * u j := by
      rw [IsLocalization.Away.mul_invSelf]
    _ = IsLocalization.Away.invSelf (f i) *
        (algebraMap R (Localization.Away (f i)) (f i) * u j) := by
      ac_rfl
    _ = IsLocalization.Away.invSelf (f i) *
        algebraMap R (Localization.Away (f i)) (f j) :=
      congrArg (fun z => IsLocalization.Away.invSelf (f i) * z) (hu j)
    _ = algebraMap R (Localization.Away (f i)) (f j) *
        IsLocalization.Away.invSelf (f i) := by ac_rfl
    _ = chapter02ChartRatio f i j := rfl

/-- The bivariate polynomial ring used for the incidence example. -/
abbrev Chapter02BivariatePolynomial (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

def chapter02BivariateX {k : Type u} [CommRing k] : Chapter02BivariatePolynomial k :=
  MvPolynomial.X 0

def chapter02BivariateY {k : Type u} [CommRing k] : Chapter02BivariatePolynomial k :=
  MvPolynomial.X 1

def chapter02BivariateGenerators {k : Type u} [CommRing k] :
    Fin 2 → Chapter02BivariatePolynomial k :=
  Fin.cases (chapter02BivariateX) (fun j => MvPolynomial.X (Fin.succ j))

def chapter02BivariateIdeal {k : Type u} [CommRing k] :
    Ideal (Chapter02BivariatePolynomial k) :=
  Ideal.span (Set.range (chapter02BivariateGenerators : Fin 2 → Chapter02BivariatePolynomial k))

def chapter02BivariateSquareGenerators {k : Type u} [CommRing k] :
    Fin 3 → Chapter02BivariatePolynomial k :=
  Fin.cases (chapter02BivariateX ^ 2) (fun i =>
    Fin.cases (chapter02BivariateX * chapter02BivariateY) (fun _ => chapter02BivariateY ^ 2) i)

def chapter02BivariateSquareIdeal {k : Type u} [CommRing k] :
    Ideal (Chapter02BivariatePolynomial k) :=
  Ideal.span
    (Set.range (chapter02BivariateSquareGenerators : Fin 3 → Chapter02BivariatePolynomial k))

theorem chapter02_bivariate_square_ideal_eq_power
    {k : Type u} [CommRing k] :
    chapter02BivariateSquareIdeal (k := k) = chapter02BivariateIdeal (k := k) ^ 2 := by
  rw [chapter02BivariateSquareIdeal, chapter02BivariateIdeal, pow_two,
    Ideal.span_mul_span']
  congr 1
  ext z
  simp only [Set.mem_mul]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · refine ⟨chapter02BivariateX, ⟨0, rfl⟩, chapter02BivariateX, ⟨0, rfl⟩, ?_⟩
      change chapter02BivariateX * chapter02BivariateX = chapter02BivariateX ^ 2
      rw [pow_two]
    · refine ⟨chapter02BivariateX, ⟨0, rfl⟩, chapter02BivariateY, ⟨1, rfl⟩, ?_⟩
      change chapter02BivariateX * chapter02BivariateY =
        chapter02BivariateX * chapter02BivariateY
      rfl
    · refine ⟨chapter02BivariateY, ⟨1, rfl⟩, chapter02BivariateY, ⟨1, rfl⟩, ?_⟩
      change chapter02BivariateY * chapter02BivariateY = chapter02BivariateY ^ 2
      rw [pow_two]
  · rintro ⟨x, hx, y, hy, rfl⟩
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    fin_cases i <;> fin_cases j
    · refine ⟨0, ?_⟩
      change chapter02BivariateX ^ 2 =
        chapter02BivariateX * chapter02BivariateX
      rw [pow_two]
    · refine ⟨1, ?_⟩
      change chapter02BivariateX * chapter02BivariateY =
        chapter02BivariateX * chapter02BivariateY
      rfl
    · refine ⟨1, ?_⟩
      change chapter02BivariateX * chapter02BivariateY =
        chapter02BivariateY * chapter02BivariateX
      rw [mul_comm]
    · refine ⟨2, ?_⟩
      change chapter02BivariateY ^ 2 =
        chapter02BivariateY * chapter02BivariateY
      rw [pow_two]

theorem chapter02_bivariate_square_has_additional_rees_relation
    {k : Type u} [Field k] :
    Chapter02AdditionalReesRelationWitness
      (I := chapter02BivariateSquareIdeal (k := k))
      chapter02BivariateSquareGenerators rfl := by
  let p : MvPolynomial (Fin 3) (Chapter02BivariatePolynomial k) :=
    MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 2
  refine ⟨p, ?_, ?_⟩
  · change chapter02FiniteGeneratorMap chapter02BivariateSquareGenerators rfl p = 0
    change
      MvPolynomial.eval₂AlgHom (Chapter02BivariatePolynomial k)
        (fun i : Fin 3 =>
          chapter02ReesGenerator (I := chapter02BivariateSquareIdeal (k := k))
            chapter02BivariateSquareGenerators rfl i) p = 0
    rw [map_sub, map_pow, map_mul]
    simp only [MvPolynomial.eval₂AlgHom_X]
    change
      (⟨Polynomial.monomial 1
          (chapter02BivariateX * chapter02BivariateY), _⟩ :
        Chapter02ReesAlgebra (Chapter02BivariatePolynomial k)
          (chapter02BivariateSquareIdeal (k := k))) ^ 2 -
        ⟨Polynomial.monomial 1 (chapter02BivariateX ^ 2), _⟩ *
          ⟨Polynomial.monomial 1 (chapter02BivariateY ^ 2), _⟩ = 0
    apply Subtype.ext
    change
      Polynomial.monomial 1 (chapter02BivariateX * chapter02BivariateY) ^ 2 -
          Polynomial.monomial 1 (chapter02BivariateX ^ 2) *
            Polynomial.monomial 1 (chapter02BivariateY ^ 2) = 0
    rw [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
    rw [show (chapter02BivariateX * chapter02BivariateY) ^ 2 =
        chapter02BivariateX ^ 2 * chapter02BivariateY ^ 2 by ring]
    norm_num
  · let coefficientEvaluation : Chapter02BivariatePolynomial k →+* k :=
      MvPolynomial.eval (fun _ : Fin 2 => 0)
    let relationEvaluation :
        MvPolynomial (Fin 3) (Chapter02BivariatePolynomial k) →+* k :=
      MvPolynomial.eval₂Hom coefficientEvaluation
        (fun i => if i = (1 : Fin 3) then 1 else 0)
    have hgenerator : ∀ i : Fin 3,
        coefficientEvaluation (chapter02BivariateSquareGenerators i) = 0 := by
      intro i
      fin_cases i
      · change coefficientEvaluation (chapter02BivariateX ^ 2) = 0
        simp [coefficientEvaluation, chapter02BivariateX]
      · change coefficientEvaluation
          (chapter02BivariateX * chapter02BivariateY) = 0
        simp [coefficientEvaluation, chapter02BivariateX, chapter02BivariateY]
      · change coefficientEvaluation (chapter02BivariateY ^ 2) = 0
        simp [coefficientEvaluation, chapter02BivariateY]
    have hrelations :
        chapter02EvidentRelationIdeal
            (I := chapter02BivariateSquareIdeal (k := k))
            chapter02BivariateSquareGenerators rfl ≤
          RingHom.ker relationEvaluation := by
      unfold chapter02EvidentRelationIdeal
      refine Ideal.span_le.2 ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      change relationEvaluation
          (chapter02EvidentGeneratorRelation
            chapter02BivariateSquareGenerators i j) = 0
      simp [relationEvaluation, chapter02EvidentGeneratorRelation]
      rw [hgenerator i, hgenerator j]
      simp
    intro hp
    have hpzero : relationEvaluation p = 0 := by
      exact hrelations hp
    have hpone : relationEvaluation p = 1 := by
      norm_num [p, relationEvaluation]
    exact one_ne_zero (hpone.symm.trans hpzero)

/- LOCAL_DEPENDENCY_GUESS: the additional relation for the square ideal is also nontrivial in
the canonical symmetric-algebra map. -/
theorem chapter02_bivariate_square_symmetric_to_rees_has_kernel
    {k : Type u} [Field k] :
    ¬ Chapter02SymmetricToReesIsomorphism (chapter02BivariateSquareIdeal (k := k)) := by
  sorry

def chapter02IncidenceEquation {k : Type u} [CommRing k] :
    MvPolynomial (Fin 2) (Chapter02BivariatePolynomial k) :=
  MvPolynomial.C chapter02BivariateX * MvPolynomial.X 1 -
    MvPolynomial.C chapter02BivariateY * MvPolynomial.X 0

def chapter02IncidenceIdeal {k : Type u} [CommRing k] :
    Ideal (MvPolynomial (Fin 2) (Chapter02BivariatePolynomial k)) :=
  Ideal.span ({chapter02IncidenceEquation (k := k)} :
    Set (MvPolynomial (Fin 2) (Chapter02BivariatePolynomial k)))

theorem chapter02_bivariate_incidence_relation
    {k : Type u} [CommRing k] :
    chapter02EvidentGeneratorRelation chapter02BivariateGenerators 0 1 =
      chapter02IncidenceEquation (k := k) := by
  simp [chapter02EvidentGeneratorRelation, chapter02BivariateGenerators,
    chapter02IncidenceEquation, chapter02BivariateX, chapter02BivariateY]
  rfl

theorem chapter02_bivariate_rees_kernel_is_incidence_ideal
    {k : Type u} [Field k] :
    chapter02GeneratorKernel (I := chapter02BivariateIdeal (k := k))
        chapter02BivariateGenerators rfl =
      chapter02EvidentRelationIdeal (I := chapter02BivariateIdeal (k := k))
        chapter02BivariateGenerators rfl := by
  sorry

theorem chapter02_bivariate_square_rees_proj_iso
    {k : Type u} [Field k] :
    Nonempty (chapter02ReesProj (chapter02BivariateIdeal (k := k)) ≅
      chapter02ReesProj (chapter02BivariateSquareIdeal (k := k))) := by
  sorry

theorem chapter02_bivariate_square_rees_algebras_differ
  {k : Type u} [Field k] :
    Chapter02ReesAlgebra (R := Chapter02BivariatePolynomial k)
        (chapter02BivariateIdeal (k := k)) ≠
      Chapter02ReesAlgebra (R := Chapter02BivariatePolynomial k)
        (chapter02BivariateSquareIdeal (k := k)) := by
  intro hEq
  let p : Polynomial (Chapter02BivariatePolynomial k) :=
    Polynomial.monomial 1 chapter02BivariateX
  have hp : p ∈ Chapter02ReesAlgebra (Chapter02BivariatePolynomial k)
      (chapter02BivariateIdeal (k := k)) := by
    change Polynomial.monomial 1 chapter02BivariateX ∈
      Chapter02ReesAlgebra (Chapter02BivariatePolynomial k)
        (chapter02BivariateIdeal (k := k))
    rw [chapter02_rees_monomial_mem_iff, pow_one]
    exact Ideal.subset_span (show chapter02BivariateX ∈
      Set.range (chapter02BivariateGenerators : Fin 2 → Chapter02BivariatePolynomial k) by
        exact ⟨0, rfl⟩)
  have hp' : p ∈ Chapter02ReesAlgebra (Chapter02BivariatePolynomial k)
      (chapter02BivariateSquareIdeal (k := k)) := by
    rw [← hEq]
    exact hp
  have hcoeff : chapter02BivariateX ∈ chapter02BivariateIdeal (k := k) ^ 2 := by
    have hsquarePow : chapter02BivariateX ∈
        chapter02BivariateSquareIdeal (k := k) ^ 1 :=
      (chapter02_rees_monomial_mem_iff
        (chapter02BivariateSquareIdeal (k := k)) 1 chapter02BivariateX).1 (by
          change Polynomial.monomial 1 chapter02BivariateX ∈
            Chapter02ReesAlgebra (Chapter02BivariatePolynomial k)
              (chapter02BivariateSquareIdeal (k := k))
          exact hp')
    have hsquare : chapter02BivariateX ∈ chapter02BivariateSquareIdeal (k := k) := by
      simpa only [pow_one] using hsquarePow
    rw [chapter02_bivariate_square_ideal_eq_power] at hsquare
    exact hsquare
  rw [show chapter02BivariateIdeal (k := k) =
      MvPolynomial.idealOfVars (Fin 2) k by
        ext z
        constructor
        · intro hz
          apply (Ideal.span_le.2 ?_) hz
          rintro _ ⟨i, rfl⟩
          fin_cases i
          · exact Ideal.subset_span ⟨0, rfl⟩
          · change MvPolynomial.X 1 ∈ MvPolynomial.idealOfVars (Fin 2) k
            exact Ideal.subset_span ⟨1, rfl⟩
        · intro hz
          apply (Ideal.span_le.2 ?_) hz
          rintro _ ⟨i, rfl⟩
          fin_cases i
          · exact Ideal.subset_span ⟨0, rfl⟩
          · exact Ideal.subset_span ⟨1, rfl⟩] at hcoeff
  have hzero := (MvPolynomial.mem_pow_idealOfVars_iff' 2 chapter02BivariateX).1 hcoeff
  exact (by simpa [chapter02BivariateX] using hzero (Finsupp.single 0 1) (by simp))

def chapter02IncidenceEquationAt {k : Type u} [Field k]
    (a b : k) (u : Fin 2 → k) : Prop :=
  a * u 1 = b * u 0

theorem chapter02_incidence_over_origin
    {k : Type u} [Field k] (u : Fin 2 → k) :
    chapter02IncidenceEquationAt 0 0 u := by
  simp [chapter02IncidenceEquationAt]

def chapter02SameProjectiveDirection {k : Type u} [Field k]
    (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ ∀ i, u i = c * v i

def chapter02Direction {k : Type u} [Field k] (a b : k) : Fin 2 → k :=
  Fin.cases a (fun _ => b)

theorem chapter02_incidence_direction_forced_away_from_origin
    {k : Type u} [Field k] {a b : k} (hab : a ≠ 0 ∨ b ≠ 0)
    {u : Fin 2 → k} (hu : u 0 ≠ 0 ∨ u 1 ≠ 0)
    (hinc : chapter02IncidenceEquationAt a b u) :
    chapter02SameProjectiveDirection u (chapter02Direction a b) := by
  change a * u 1 = b * u 0 at hinc
  rcases hab with ha | hb
  · have hu0 : u 0 ≠ 0 := by
      intro hu0
      have hu1 : u 1 = 0 := by
        have hzero : a * u 1 = 0 := by simpa [hu0] using hinc
        exact (mul_eq_zero.mp hzero).resolve_left ha
      rcases hu with hu' | hu'
      · exact hu' hu0
      · exact hu' hu1
    refine ⟨u 0 / a, div_ne_zero hu0 ha, ?_⟩
    intro i
    fin_cases i
    · change u 0 = u 0 / a * a
      field_simp [ha]
    · change u 1 = u 0 / a * b
      field_simp [ha]
      simpa [mul_comm] using hinc
  · have hu1 : u 1 ≠ 0 := by
      intro hu1
      have hu0 : u 0 = 0 := by
        have hzero : b * u 0 = 0 := by simpa [hu1] using hinc.symm
        exact (mul_eq_zero.mp hzero).resolve_left hb
      rcases hu with hu' | hu'
      · exact (hu' hu0).elim
      · exact hu' hu1
    refine ⟨u 1 / b, div_ne_zero hu1 hb, ?_⟩
    intro i
    fin_cases i
    · change u 0 = u 1 / b * a
      field_simp [hb]
      simpa [mul_comm] using hinc.symm
    · change u 1 = u 1 / b * b
      field_simp [hb]

theorem chapter02_incidence_has_all_directions_over_origin
    {k : Type u} [Field k] :
    ∀ u : Fin 2 → k, (u 0 ≠ 0 ∨ u 1 ≠ 0) →
      chapter02IncidenceEquationAt 0 0 u := by
  intro u _
  exact chapter02_incidence_over_origin u

/- LOCAL_DEPENDENCY_GUESS: an invertible ideal has a Rees Proj canonically isomorphic to the
base affine scheme; the module-invertibility predicate is the strongest pinned ring interface. -/
theorem chapter02_rees_proj_of_invertible_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : Chapter02InvertibleIdeal I) :
    Nonempty (chapter02ReesProj I ≅ AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  sorry

/-! ### Veronese subalgebras and unchanged projective spectrum -/

abbrev chapter02ReesVeroneseCarrier
    {R : Type u} [CommRing R] (I : Ideal R) (q : ℕ) :=
  ⨁ n : ℕ, (chapter02ReesGradingData I).component (q * n)

structure Chapter02ReesVeroneseData
    {R : Type u} [CommRing R] (I : Ideal R) (q : ℕ) where
  [commRing : CommRing (chapter02ReesVeroneseCarrier I q)]
  [algebra : Algebra R (chapter02ReesVeroneseCarrier I q)]
  component : ℕ →
    @Submodule R (chapter02ReesVeroneseCarrier I q)
      (@CommRing.toCommSemiring R inferInstance).toSemiring
      (@CommRing.toCommSemiring (chapter02ReesVeroneseCarrier I q) commRing).toAddCommMonoid
      (@Algebra.toModule R (chapter02ReesVeroneseCarrier I q)
        (@CommRing.toCommSemiring R inferInstance)
        (@CommRing.toCommSemiring (chapter02ReesVeroneseCarrier I q) commRing).toSemiring algebra)
  graded : GradedAlgebra component
  component_spec :
    ∀ n (x : chapter02ReesVeroneseCarrier I q),
      x ∈ component n ↔
        ∃ y : (chapter02ReesGradingData I).component (q * n),
          DirectSum.of (fun n : ℕ => (chapter02ReesGradingData I).component (q * n)) n y = x
  reesEquiv :
    letI : CommRing (chapter02ReesVeroneseCarrier I q) := commRing
    Chapter02ReesAlgebra R (I ^ q) ≃+* chapter02ReesVeroneseCarrier I q
  reesEquiv_component :
    letI : CommRing (chapter02ReesVeroneseCarrier I q) := commRing
    ∀ n (x : Chapter02ReesAlgebra R (I ^ q)),
      x ∈ (chapter02ReesGradingData (I ^ q)).component n ↔
        reesEquiv x ∈ component n

/- LOCAL_DEPENDENCY_GUESS: the direct sum of the `I^(qn)T^(qn)` pieces carries the canonical
Veronese graded algebra structure. -/
theorem chapter02_rees_veronese_exists
    {R : Type u} [CommRing R] (I : Ideal R) {q : ℕ} (hq : 0 < q) :
    Nonempty (Chapter02ReesVeroneseData I q) := by
  sorry

noncomputable def chapter02ReesVeroneseData
    {R : Type u} [CommRing R] (I : Ideal R) {q : ℕ} (hq : 0 < q) :
    Chapter02ReesVeroneseData I q :=
  Classical.choice (chapter02_rees_veronese_exists I hq)

noncomputable def chapter02ReesVeroneseProj
    {R : Type u} [CommRing R] {I : Ideal R} {q : ℕ} (_hq : 0 < q)
    (V : Chapter02ReesVeroneseData I q) : Scheme.{u} := by
  letI := V.commRing
  letI := V.algebra
  letI := V.graded
  exact AlgebraicGeometry.«Proj» V.component

theorem chapter02_rees_power_proj_iso
    {R : Type u} [CommRing R] (I : Ideal R) {q : ℕ} (hq : 0 < q)
    : Nonempty (chapter02ReesProj I ≅ chapter02ReesProj (I ^ q)) := by
  sorry

theorem chapter02_rees_power_has_same_projective_spectrum
    {R : Type u} [CommRing R] (I : Ideal R) {q : ℕ} (hq : 0 < q) :
    Nonempty (chapter02ReesProj I ≅ chapter02ReesProj (I ^ q)) := by
  exact chapter02_rees_power_proj_iso I hq

theorem chapter02_invertible_ideal_multiplication_preserves_rees_proj
    {R : Type u} [CommRing R] (I J : Ideal R)
    (hJ : Chapter02InvertibleIdeal J) :
    Nonempty (chapter02ReesProj (J * I) ≅ chapter02ReesProj I) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
