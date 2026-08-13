import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section01PreciseFunctors
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

/-! ## 12.2. The Grassmannian construction -/

/-- The degree pieces of the homogeneous coordinate algebra of `ℙ^r_A`. -/
structure Chapter12ProjectiveSectionSystem (A : Type u) [CommRing A] (r : ℕ) where
  sections : ℕ → ModuleCat.{u} A
  multiplication : ∀ (n m : ℕ),
    ModuleCat.carrier (sections n) → ModuleCat.carrier (sections m) →
      ModuleCat.carrier (sections (n + m))
  multiplication_zero_left : ∀ (n m : ℕ) (y),
    multiplication n m 0 y = 0
  multiplication_zero_right : ∀ (n m : ℕ) (x),
    multiplication n m x 0 = 0
  multiplication_add_left : ∀ (n m : ℕ) (x x' y),
    multiplication n m (x + x') y =
      multiplication n m x y + multiplication n m x' y
  multiplication_add_right : ∀ (n m : ℕ) (x y y'),
    multiplication n m x (y + y') =
      multiplication n m x y + multiplication n m x y'
  multiplication_smul_left : ∀ (n m : ℕ) (a : A) (x y),
    multiplication n m (a • x) y = a • multiplication n m x y
  multiplication_smul_right : ∀ (n m : ℕ) (a : A) (x y),
    multiplication n m x (a • y) = a • multiplication n m x y

/-- A finite locally free quotient of the degree-`n` section module. -/
structure Chapter12ModuleQuotient (A : Type u) [CommRing A]
    (P : Chapter12NumericalPolynomial) (n : ℕ) where
  source : ModuleCat.{u} A
  target : ModuleCat.{u} A
  quotient : source ⟶ target
  quotient_surjective : Function.Surjective quotient.hom
  source_projective : Module.Projective A (source : Type u)
  source_finite : Module.Finite A (source : Type u)
  target_projective : Module.Projective A (target : Type u)
  target_finite : Module.Finite A (target : Type u)
  target_rank : ℕ
  target_rank_eq : P.value n = (target_rank : ℤ)
  target_free_rank : Nonempty
    (target ≅ ModuleCat.of A (Fin target_rank →₀ A))

theorem chapter12ModuleQuotient_rank_eq
    {A : Type u} [CommRing A] {P : Chapter12NumericalPolynomial} {n : ℕ}
    (Q : Chapter12ModuleQuotient A P n) : P.value n = (Q.target_rank : ℤ) :=
  Q.target_rank_eq

/-- The eventual degree-`n` quotient supplied by vanishing and base change. -/
theorem chapter12_eventual_degree_quotient
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    {P : Chapter12NumericalPolynomial}
    {T : Chapter12SchemeOver D.base}
    (A : Type) [CommRing A]
    (test_identification : T.left ≅ Spec (.of A))
    (Z : Chapter12HilbertFamily D H T P) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Nonempty (Chapter12ModuleQuotient A P n) := by
  sorry

/-- A Grassmannian parameter space for rank-`q` quotients of a module. -/
structure Chapter12LocallyFreeQuotient
    {S : Scheme} (V : S.Modules) {T : Scheme} (f : T ⟶ S) (q : ℕ) where
  target : T.Modules
  quotient : (Scheme.Modules.pullback f).obj V ⟶ target
  quotient_epi : Epi quotient
  target_rank : Chapter02LocallyFreeRank target q

structure Chapter12Grassmannian (S : Scheme) (V : S.Modules) (q : ℕ) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  universal_target : carrier.Modules
  universal_quotient : (Scheme.Modules.pullback structureMap).obj V ⟶ universal_target
  universal_quotient_epi : Epi universal_quotient
  universal_target_rank : Chapter02LocallyFreeRank universal_target q
  represents_rank_q_quotients : ∀ {T : Scheme} (f : T ⟶ S),
    {u : T ⟶ carrier // u ≫ structureMap = f} ≃
      Chapter12LocallyFreeQuotient V f q

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib checkout has no Grassmannian
  construction. The universal quotient and its arbitrary-test-scheme
  property are retained as one explicit dependency interface. -/
/-- The rank `P(n)` Grassmannian used at degree `n`. -/
noncomputable def chapter12DegreeGrassmannian
    (S : Scheme) (V : S.Modules)
    (P : Chapter12NumericalPolynomial) (n q : ℕ)
    (hq : P.value n = (q : ℤ)) :
    Chapter12Grassmannian S V q := by
  classical
  exact Classical.choice (by
    sorry)

/-- A graded algebra interface for homogeneous ideals. -/
structure Chapter12GradedAlgebra (A : Type u) [CommRing A] where
  degree : ℕ → ModuleCat.{u} A
  multiplication : ∀ (n m : ℕ),
    ModuleCat.carrier (degree n) → ModuleCat.carrier (degree m) →
      ModuleCat.carrier (degree (n + m))
  multiplication_zero_left : ∀ (n m : ℕ) (y),
    multiplication n m 0 y = 0
  multiplication_zero_right : ∀ (n m : ℕ) (x),
    multiplication n m x 0 = 0
  multiplication_add_left : ∀ (n m : ℕ) (x x' y),
    multiplication n m (x + x') y =
      multiplication n m x y + multiplication n m x' y
  multiplication_add_right : ∀ (n m : ℕ) (x y y'),
    multiplication n m x (y + y') =
      multiplication n m x y + multiplication n m x y'
  multiplication_smul_left : ∀ (n m : ℕ) (a : A) (x y),
    multiplication n m (a • x) y = a • multiplication n m x y
  multiplication_smul_right : ∀ (n m : ℕ) (a : A) (x y),
    multiplication n m x (a • y) = a • multiplication n m x y
  multiplication_assoc : ∀ (n m k : ℕ) (x y z),
    HEq (multiplication (n + m) k (multiplication n m x y) z)
      (multiplication n (m + k) x (multiplication m k y z))

/-- A homogeneous ideal, recorded by its degree pieces. -/
structure Chapter12HomogeneousIdeal (A : Type u) [CommRing A] where
  algebra : Chapter12GradedAlgebra A
  degreePart : ∀ n, Set (algebra.degree n : Type u)
  zero_mem : ∀ n, (0 : algebra.degree n) ∈ degreePart n
  add_mem : ∀ n {x y : algebra.degree n}, x ∈ degreePart n →
    y ∈ degreePart n → x + y ∈ degreePart n
  smul_mem : ∀ n (a : A) {x : algebra.degree n}, x ∈ degreePart n →
    a • x ∈ degreePart n
  mul_mem : ∀ n m {x : algebra.degree n}, x ∈ degreePart n
    → (y : algebra.degree m) →
      algebra.multiplication n m x y ∈ degreePart (n + m)

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
  every_ideal_regular : ∀ {A : Type*} [Field A],
    ∀ (I : Chapter12SaturatedHomogeneousIdeal A r P),
      chapter12HasHomogeneousHilbertPolynomial I.ideal P →
        chapter12IsMRegular I.ideal m
  /-- The chosen bound is also a generation degree. -/
  every_ideal_generated_from : ∀ {A : Type*} [Field A],
    ∀ (I : Chapter12SaturatedHomogeneousIdeal A r P),
      chapter12HasHomogeneousHilbertPolynomial I.ideal P →
        chapter12IsGeneratedFromDegree I.ideal m

theorem chapter12_regularity_bound_exists
    (P : Chapter12NumericalPolynomial) (r : ℕ) :
    ∃ m : ℕ, ∀ {A : Type*} [Field A],
      ∀ I : Chapter12SaturatedHomogeneousIdeal A r P,
        chapter12HasHomogeneousHilbertPolynomial I.ideal P →
          chapter12IsMRegular I.ideal m ∧ chapter12IsGeneratedFromDegree I.ideal m := by
  sorry

noncomputable def chapter12RegularityBoundValue
    (P : Chapter12NumericalPolynomial) (r : ℕ) : ℕ :=
  Classical.choose (show
    ∃ m : ℕ, ∀ {A : Type} [Field A],
      ∀ I : Chapter12SaturatedHomogeneousIdeal A r P,
        chapter12HasHomogeneousHilbertPolynomial I.ideal P →
          chapter12IsMRegular I.ideal m ∧
            chapter12IsGeneratedFromDegree I.ideal m
    from chapter12_regularity_bound_exists P r)

theorem chapter12RegularityBoundValue_spec
    (P : Chapter12NumericalPolynomial) (r : ℕ)
    {A : Type*} [Field A]
    (I : Chapter12SaturatedHomogeneousIdeal A r P)
    (hI : chapter12HasHomogeneousHilbertPolynomial I.ideal P) :
    chapter12IsMRegular I.ideal (chapter12RegularityBoundValue P r) ∧
      chapter12IsGeneratedFromDegree I.ideal (chapter12RegularityBoundValue P r) := by
  sorry

/-- The universal kernel and multiplication map on the controlling Grassmannian. -/
structure Chapter12GrassmannianUniversalData
    (S : Scheme) (P : Chapter12NumericalPolynomial) (m : ℕ) where
  section_module : S.Modules
  degree_rank : ℕ
  degree_rank_eq : P.value m = (degree_rank : ℤ)
  grassmannian : Chapter12Grassmannian S section_module degree_rank
  kernel : grassmannian.carrier.Modules
  kernel_inclusion : kernel ⟶
    (Scheme.Modules.pullback grassmannian.structureMap).obj section_module
  next_degree_source : grassmannian.carrier.Modules
  next_degree_target : grassmannian.carrier.Modules
  kernel_tensor_linear_forms : kernel ⟶ next_degree_source
  multiplication_map : next_degree_source ⟶ next_degree_target
  next_degree_quotient : grassmannian.carrier.Modules
  universal_next_degree_quotient : next_degree_target ⟶ next_degree_quotient
  next_degree_rank : ℕ
  target_rank : ℕ
  target_rank_eq : P.value (m + 1) = (target_rank : ℤ)
  image_subbundle_codimension : ℕ
  image_subbundle_codimension_eq : image_subbundle_codimension = target_rank
  induced_quotient_rank : ℕ
  image_lies_in_subbundle :
    kernel_tensor_linear_forms ≫ multiplication_map ≫
      universal_next_degree_quotient = 0
  induced_quotient : grassmannian.carrier.Modules
  induced_quotient_locally_free : Chapter02LocallyFreeRank induced_quotient induced_quotient_rank
  kernel_is_degree_m_kernel :
    kernel_inclusion ≫ grassmannian.universal_quotient = 0

/-- A closed determinantal locus cut out by the next-degree rank condition. -/
structure Chapter12DeterminantalLocus (G : Scheme) where
  carrier : Scheme
  inclusion : carrier ⟶ G
  closed : IsClosedImmersion inclusion
  induced_quotient : carrier.Modules
  induced_quotient_rank : ℕ
  induced_quotient_locally_free : Chapter02LocallyFreeRank induced_quotient induced_quotient_rank

/-- The closed condition imposed by the next-degree multiplication map. -/
def chapter12DeterminantalCondition
    {S : Scheme} {P : Chapter12NumericalPolynomial} {m : ℕ}
    (U : Chapter12GrassmannianUniversalData S P m) : Prop :=
  (U.kernel_tensor_linear_forms ≫ U.multiplication_map ≫
      U.universal_next_degree_quotient = 0) ∧
    U.image_subbundle_codimension = U.target_rank ∧
    Chapter02LocallyFreeRank U.induced_quotient U.induced_quotient_rank ∧
    U.induced_quotient_rank = U.target_rank

/- The following two fields are book-facing names for the finite determinantal
  equations. Their precise scheme-theoretic realization belongs to the later
  Grassmannian/ideal implementation. -/
structure Chapter12HilbertGrassmannianConstruction
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) where
  m : ℕ
  grassmannian : Scheme
  grassmannianMap : grassmannian ⟶ D.base
  locus : Scheme
  locusMap : locus ⟶ D.base
  locusInclusion : locus ⟶ grassmannian
  locus_over : locusInclusion ≫ grassmannianMap = locusMap
  locus_closed : IsClosedImmersion locusInclusion
  universal_family : Chapter12HilbertFamily D H (Over.mk locusMap) P

/-- The degree-`m` quotient and the next multiplication condition recover the saturated ideal. -/
theorem chapter12_grassmannian_locus_recovers_saturated_ideal
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Nonempty (Chapter12HilbertGrassmannianConstruction D E H P) := by
  sorry

noncomputable def chapter12HilbertGrassmannianConstruction
    (D : Chapter12ProjectiveFamilySetup)
    (E : Chapter12ProjectiveEmbedding D)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    Chapter12HilbertGrassmannianConstruction D E H P :=
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
