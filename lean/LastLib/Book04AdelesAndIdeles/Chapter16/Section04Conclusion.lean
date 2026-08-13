import LastLib.Book04AdelesAndIdeles.Chapter16.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter16

noncomputable section

open Set Filter
open scoped BigOperators NumberField RestrictedProduct Topology

/-!
## 16.4 Conclusion

The conclusion packages the interfaces already established: the restrictions
are the arithmetic glue, the diagonal is discrete/cocompact, and the norm-one
idele classes are compact.  The later reciprocity and automorphic theories are
deliberately recorded as consumers of this platform, not as declarations in
this chapter.
-/

def chapter16FiniteLocalRestriction
    {ι : Type*} {X : ι → Type*}
    (S : Finset ι) (condition : ∀ i, Set (X i)) (x : ∀ i, X i) : Prop :=
  ∀ i ∈ S, x i ∈ condition i

def chapter16GlobalRealization
    {ι K : Type*} {X : ι → Type*}
    (globalToLocal : K → ∀ i, X i) (x : ∀ i, X i) : Prop :=
  ∃ a : K, globalToLocal a = x

def chapter16LocalGlobalArchitectureStatement
    (K : Type*) [Field K] [NumberField K] : Prop :=
  (∀ x : Chapter16FiniteAdeleRing K, chapter16AdditiveTail K x) ∧
    (∀ x : Chapter16Ideles K, chapter16IdeleUnitTail K x) ∧
    LocallyCompactSpace (Chapter16AdeleRing K) ∧
    LocallyCompactSpace (Chapter16Ideles K) ∧
    DiscreteTopology (Chapter16PrincipalAdeles K) ∧
    IsCompact (Set.univ : Set (Chapter16AdditiveQuotient K)) ∧
    IsCompact (Set.univ : Set (Chapter16NormOneClassGroup K))

theorem chapter16_restricted_product_is_the_local_global_architecture
    (K : Type*) [Field K] [NumberField K] :
    chapter16LocalGlobalArchitectureStatement K := by
  sorry

theorem chapter16_diagonal_balance_and_product_formula
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Chapter16PrincipalAdeles K) ∧
      IsCompact (Set.univ : Set (Chapter16AdditiveQuotient K)) ∧
      chapter16PrincipalIdeles K ≤ chapter16NormOneIdeles K ∧
      IsCompact (Set.univ : Set (Chapter16NormOneClassGroup K)) := by
  sorry

theorem chapter16_finite_conditions_and_global_realization_are_distinct
    {ι K : Type*} {X : ι → Type*}
    (globalToLocal : K → ∀ i, X i) (x : ∀ i, X i)
    (S : Finset ι) (condition : ∀ i, Set (X i)) :
    (chapter16GlobalRealization globalToLocal x ∧
      chapter16FiniteLocalRestriction S condition x) ↔
      ∃ a : K, globalToLocal a = x ∧
        ∀ i ∈ S, globalToLocal a i ∈ condition i := by
  constructor
  · rintro ⟨⟨a, ha⟩, hx⟩
    exact ⟨a, ha, by simpa [chapter16FiniteLocalRestriction, ha] using hx⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨⟨a, rfl⟩, ha⟩

/-!
The source's final outlook is intentionally non-declarative: reciprocity maps,
Galois identifications, Fourier inversion, Poisson summation, and automorphic
representation theory belong to later chapters.  The declarations above are
the common locally compact arithmetic platform on which those theories can be
formulated.
-/

end

end LastLib.Book04AdelesAndIdeles.Chapter16
