import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14.Section05PrescribingFinitelyManyLocalCompletions

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open Polynomial
open IntermediateField

universe u v w

/-! ## 14.6. What the approximation theorem does not prescribe -/

def chapter14ModelIsGalois
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) : Prop :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  IsGalois F M.carrier

abbrev chapter14ModelGaloisGroup
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) : Type v :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  Gal(M.carrier / F)

def chapter14ModelUnramifiedAt
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F) : Prop :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  ∀ P : Chapter14PrimeAbove F M.carrier p,
    chapter14RamificationIndex M.carrier p P = 1

def chapter14ModelEquivalence
    {F : Type u} [Field F] [NumberField F]
    (M N : Chapter14NumberFieldModel F) : Prop :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  letI : Field N.carrier := N.field_carrier
  letI : NumberField N.carrier := N.number_field_carrier
  letI : Algebra F N.carrier := N.algebra
  letI : FiniteDimensional F N.carrier := N.finite_dimensional
  Nonempty (M.carrier ≃ₐ[F] N.carrier)

/- These predicates are deliberately separate from the local conclusion: they
   are the global properties named by the source warning. -/
def chapter14GlobalGaloisGroupRequest
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (G : Type v) [Group G] : Prop :=
  Nonempty (G ≃* chapter14ModelGaloisGroup M)

def chapter14AwayFromSelectedPrimesRequest
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (S : Set (Chapter14Prime F)) : Prop :=
  ∀ p, p ∉ S → chapter14ModelUnramifiedAt M p

def chapter14UniqueGlobalRealizationRequest
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F)
    (C : Set (Chapter14NumberFieldModel F)) : Prop :=
  ∀ N, N ∈ C → chapter14ModelEquivalence M N

theorem chapter14_theorem_14_1_only_provides_local_scope
    {F : Type u} [Field F] [NumberField F]
    {r : ℕ} (p : Fin r → Chapter14Prime F)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (S : Chapter14ApproximationScope F p L) :
    chapter14ModelDegree S.model = chapter14MaximumLocalDegree p L ∧
      ∀ i,
        letI : Field (L i).carrier := (L i).field_carrier
        Nonempty (Chapter14CompletionChoice S.model (p i) (L i).carrier) := by
  refine ⟨S.degree_eq_max, ?_⟩
  intro i
  let _ : Field (L i).carrier := (L i).field_carrier
  exact ⟨S.choice i⟩

/- The scope structure has no global Galois, away-from-`S` ramification, or
   uniqueness field.  The following theorem records exactly the open
   stability conclusion used by weak approximation. -/
theorem chapter14_weak_approximation_targets_only_open_stability_neighborhoods
    {F : Type u} [Field F] [NumberField F]
    (S : Finset (Chapter14Prime F)) (n : ℕ)
    [∀ p : S, TopologicalSpace ((chapter14BaseCompletion F p.1)[X])]
    (N : Chapter14SimultaneousPolynomialNeighborhood S n) :
    ∃ g : F[X], g.Monic ∧ g.natDegree = n ∧
      ∀ p, chapter14PolynomialMapAt p.1 g ∈ N.neighborhood p := by
  exact chapter14_simultaneous_monic_polynomial_approximation S n N

def chapter14KrasnerStrictInequality
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (x y : L) : Prop :=
  ∀ x' : L, IsConjRoot K x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖

theorem chapter14_strict_krasner_inequality_preserves_the_generated_field
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    [IsKrasner K L] {x y : L}
    (hx : (minpoly K x).Separable)
    (hsplits : ((minpoly K x).map (algebraMap K L)).Splits)
    (hy : IsIntegral K y)
    (hstrict : chapter14KrasnerStrictInequality (K := K) (L := L) x y) :
    x ∈ K⟮y⟯ := by
  exact IsKrasner.krasner hx hsplits hy hstrict

/- The two directions of the chapter are represented by the preceding APIs:
   completion decomposes a global tensor product into selected branches, while
   approximation builds a global scope from finitely many local branches. -/
theorem chapter14_global_to_local_and_local_to_global_interfaces
    {F : Type u} [Field F] [NumberField F]
    {r : ℕ} (p : Fin r → Chapter14Prime F)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i))
    (S : Chapter14ApproximationScope F p L) :
    chapter14ModelDegree S.model = chapter14MaximumLocalDegree p L :=
  S.degree_eq_max

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
