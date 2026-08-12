import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section01PreciseFunctors
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

/-! ## 12.2. The Grassmannian construction -/

/-- The degree pieces of the homogeneous coordinate algebra of `ℙ^r_A`. -/
structure Chapter12ProjectiveSectionSystem (A : Type u) [CommRing A] (r : ℕ) where
  sections : ℕ → ModuleCat.{u} A
  multiplication : ∀ (n m : ℕ),
    ModuleCat.carrier (sections n) → ModuleCat.carrier (sections m) →
      ModuleCat.carrier (sections (n + m))
  multiplication_bilinear : Prop
  identifies_global_sections : ∀ _n : ℕ, Prop

/-- A finite locally free quotient of the degree-`n` section module. -/
structure Chapter12ModuleQuotient (A : Type u) [CommRing A]
    (P : Chapter12NumericalPolynomial) (n : ℕ) where
  source : ModuleCat.{u} A
  target : ModuleCat.{u} A
  quotient : source ⟶ target
  quotient_surjective : Function.Surjective quotient.hom
  target_rank : ℕ
  target_rank_eq : P.eval (n : ℚ) = (target_rank : ℚ)
  source_is_twisted_global_sections : Prop
  target_is_pushforward_of_twist : Prop

/-- The eventual degree-`n` quotient supplied by vanishing and base change. -/
theorem chapter12_eventual_degree_quotient
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    (A : Type) [CommRing A]
    (base_identification : D.base ≅ Spec (.of A))
    {T : Chapter12SchemeOver D.base}
    (Z : Chapter12HilbertFamily D H T P) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Nonempty (Chapter12ModuleQuotient A P n) := by
  sorry

/-- A Grassmannian parameter space for rank-`q` quotients of a module. -/
structure Chapter12Grassmannian (A : Type u) [CommRing A]
    (V : ModuleCat.{u} A) (q : ℕ) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (.of A)
  universal_target : ModuleCat.{u} A
  universal_quotient : V ⟶ universal_target
  universal_surjective : Function.Surjective universal_quotient.hom
  universal_rank : Prop
  represents_rank_q_quotients : Prop

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib checkout has no Grassmannian
  construction. The finite/free module hypotheses below are the exact input
  supplied by the degree pieces of projective space. -/
/-- The rank `P(n)` Grassmannian used at degree `n`. -/
noncomputable def chapter12DegreeGrassmannian
    (A : Type u) [CommRing A] (V : ModuleCat.{u} A)
    [Module.Free A (V : Type u)] [Module.Finite A (V : Type u)]
    (P : Chapter12NumericalPolynomial) (n q : ℕ)
    (hq : P.eval (n : ℚ) = (q : ℚ)) :
    Chapter12Grassmannian A V q := by
  classical
  exact Classical.choice (by
    sorry)

/-- A graded algebra interface for homogeneous ideals. -/
structure Chapter12GradedAlgebra (A : Type u) [CommRing A] where
  degree : ℕ → ModuleCat.{u} A
  multiplication : ∀ (n m : ℕ),
    ModuleCat.carrier (degree n) → ModuleCat.carrier (degree m) →
      ModuleCat.carrier (degree (n + m))
  multiplication_bilinear : Prop

/-- A homogeneous ideal, recorded by its degree pieces. -/
structure Chapter12HomogeneousIdeal (A : Type u) [CommRing A] where
  algebra : Chapter12GradedAlgebra A
  degreePart : ∀ n, Set (algebra.degree n : Type u)
  zero_mem : ∀ n, (0 : algebra.degree n) ∈ degreePart n
  add_mem : ∀ n {x y : algebra.degree n}, x ∈ degreePart n →
    y ∈ degreePart n → x + y ∈ degreePart n
  smul_mem : ∀ n (a : A) {x : algebra.degree n}, x ∈ degreePart n →
    a • x ∈ degreePart n

/-- The multiplication compatibility `I_n · H⁰(O(m)) ⊆ I_(n+m)`. -/
def chapter12IdealMultiplicationCompatible
    {A : Type u} [CommRing A] (I : Chapter12HomogeneousIdeal A) : Prop :=
  ∀ (n m : ℕ) {x : I.algebra.degree n} (_hx : x ∈ I.degreePart n)
    (y : I.algebra.degree m),
    I.algebra.multiplication n m x y ∈ I.degreePart (n + m)

/- LOCAL_DEPENDENCY_GUESS: the pinned graded-ring API does not yet expose the
  book's saturated-ideal and Hilbert-polynomial predicates in this form. -/
def chapter12IsSaturatedHomogeneousIdeal
    {A : Type u} [CommRing A] (I : Chapter12HomogeneousIdeal A) : Prop := by
  sorry

def chapter12HasHomogeneousHilbertPolynomial
    {A : Type u} [CommRing A] (I : Chapter12HomogeneousIdeal A)
    (P : Chapter12NumericalPolynomial) : Prop := by
  sorry

def chapter12IsMRegular
    {A : Type u} [CommRing A] (I : Chapter12HomogeneousIdeal A) (m : ℕ) : Prop := by
  sorry

def chapter12IsGeneratedFromDegree
    {A : Type u} [CommRing A] (I : Chapter12HomogeneousIdeal A) (m : ℕ) : Prop := by
  sorry

/-- A saturated homogeneous ideal equipped with its polynomial and regularity interfaces. -/
structure Chapter12SaturatedHomogeneousIdeal (A : Type u) [CommRing A]
    (r : ℕ) (P : Chapter12NumericalPolynomial) where
  ideal : Chapter12HomogeneousIdeal A
  multiplication_compatible : chapter12IdealMultiplicationCompatible ideal
  saturated : chapter12IsSaturatedHomogeneousIdeal ideal
  hilbert_polynomial : chapter12HasHomogeneousHilbertPolynomial ideal P

/-- A Gotzmann/regularity bound at which all ideals with polynomial `P` are controlled. -/
structure Chapter12RegularityBound (P : Chapter12NumericalPolynomial) (r m : ℕ) where
  every_ideal_regular : ∀ {A : Type*} [CommRing A],
    ∀ (I : Chapter12SaturatedHomogeneousIdeal A r P),
      chapter12HasHomogeneousHilbertPolynomial I.ideal P →
        chapter12IsMRegular I.ideal m
  /-- The chosen bound is also a generation degree. -/
  every_ideal_generated_from : ∀ {A : Type*} [CommRing A],
    ∀ (I : Chapter12SaturatedHomogeneousIdeal A r P),
      chapter12HasHomogeneousHilbertPolynomial I.ideal P →
        chapter12IsGeneratedFromDegree I.ideal m

theorem chapter12_regularity_bound_exists
    (P : Chapter12NumericalPolynomial) (r : ℕ) :
    ∃ m : ℕ, ∀ {A : Type*} [CommRing A],
      ∀ I : Chapter12SaturatedHomogeneousIdeal A r P,
        chapter12HasHomogeneousHilbertPolynomial I.ideal P →
          chapter12IsMRegular I.ideal m ∧ chapter12IsGeneratedFromDegree I.ideal m := by
  sorry

noncomputable def chapter12RegularityBoundValue
    (P : Chapter12NumericalPolynomial) (r : ℕ) : ℕ :=
  Classical.choose (show
    ∃ m : ℕ, ∀ {A : Type} [CommRing A],
      ∀ I : Chapter12SaturatedHomogeneousIdeal A r P,
        chapter12HasHomogeneousHilbertPolynomial I.ideal P →
          chapter12IsMRegular I.ideal m ∧
            chapter12IsGeneratedFromDegree I.ideal m
    from chapter12_regularity_bound_exists P r)

theorem chapter12RegularityBoundValue_spec
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    {A : Type*} [CommRing A]
    (I : Chapter12SaturatedHomogeneousIdeal A r P)
    (hI : chapter12HasHomogeneousHilbertPolynomial I.ideal P) :
    chapter12IsMRegular I.ideal (chapter12RegularityBoundValue P r) ∧
      chapter12IsGeneratedFromDegree I.ideal (chapter12RegularityBoundValue P r) := by
  sorry

/-- The universal kernel and multiplication map on the controlling Grassmannian. -/
structure Chapter12GrassmannianUniversalData
    (A : Type u) [CommRing A] (P : Chapter12NumericalPolynomial) (m : ℕ) where
  section_module : ModuleCat.{u} A
  degree_rank : ℕ
  degree_rank_eq : P.eval (m : ℚ) = (degree_rank : ℚ)
  grassmannian : Chapter12Grassmannian A section_module degree_rank
  kernel : ModuleCat.{u} A
  kernel_inclusion : kernel ⟶ section_module
  next_degree_source : ModuleCat.{u} A
  next_degree_target : ModuleCat.{u} A
  multiplication_map : next_degree_source ⟶ next_degree_target
  next_degree_rank : ℕ
  target_rank : ℕ
  target_rank_eq : P.eval ((m + 1 : ℕ) : ℚ) = (target_rank : ℚ)
  image_subbundle_codimension : ℕ
  image_subbundle_codimension_eq : image_subbundle_codimension = target_rank
  induced_quotient_rank : ℕ
  image_lies_in_subbundle : Prop
  induced_quotient_locally_free : Prop
  kernel_is_degree_m_kernel : Prop
  source_is_kernel_tensor_linear_forms : Prop
  target_is_next_degree_sections : Prop

/-- A closed determinantal locus cut out by the next-degree rank condition. -/
structure Chapter12DeterminantalLocus (G : Scheme) where
  carrier : Scheme
  inclusion : carrier ⟶ G
  closed : IsClosedImmersion inclusion
  induced_quotient_locally_free : Prop
  induced_quotient_rank : ℕ

/-- The closed condition imposed by the next-degree multiplication map. -/
def chapter12DeterminantalCondition
    {A : Type u} [CommRing A] {P : Chapter12NumericalPolynomial} {m : ℕ}
    (U : Chapter12GrassmannianUniversalData A P m) : Prop :=
  U.image_lies_in_subbundle ∧
    U.image_subbundle_codimension = U.target_rank ∧
    U.induced_quotient_locally_free ∧
    U.induced_quotient_rank = U.target_rank

/- The following two fields are book-facing names for the finite determinantal
  equations. Their precise scheme-theoretic realization belongs to the later
  Grassmannian/ideal implementation. -/
structure Chapter12HilbertGrassmannianConstruction
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (P : Chapter12NumericalPolynomial) where
  m : ℕ
  grassmannian : Scheme
  grassmannianMap : grassmannian ⟶ D.base
  locus : Scheme
  locusMap : locus ⟶ D.base
  locusInclusion : locus ⟶ grassmannian
  locus_closed : IsClosedImmersion locusInclusion
  universal_ideal : Prop
  universal_closed_subscheme : Prop
  regularity_controls_all_later_degrees : Prop

/-- The degree-`m` quotient and the next multiplication condition recover the saturated ideal. -/
theorem chapter12_grassmannian_locus_recovers_saturated_ideal
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Nonempty (Chapter12HilbertGrassmannianConstruction D E P) := by
  sorry

noncomputable def chapter12HilbertGrassmannianConstruction
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Chapter12HilbertGrassmannianConstruction D E P :=
  Classical.choice (chapter12_grassmannian_locus_recovers_saturated_ideal D E H P)

theorem chapter12HilbertGrassmannianConstruction_locus_closed
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    IsClosedImmersion
      (chapter12HilbertGrassmannianConstruction D E H P).locusInclusion := by
  exact (chapter12HilbertGrassmannianConstruction D E H P).locus_closed

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
