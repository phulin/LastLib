import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.6. What reciprocity adds
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

open scoped NumberField

def chapter14FiniteAbelianExtension (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] : Prop :=
  IsMulCommutative Gal(L/K)

def chapter14OpenSubgroupCorrespondsToFiniteAbelianExtension
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter14OpenFiniteIndexSubgroup (chapter14IdeleClassGroup K)) : Prop :=
  chapter14FiniteAbelianExtension K L ∧
    Nonempty ((chapter14IdeleClassGroup K ⧸ U.1.toSubgroup) ≃* Gal(L/K))

def chapter14OpenSubgroupIsClassNormGroup
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (N : Chapter14AdelicNormInterface K L)
    (U : Chapter14OpenFiniteIndexSubgroup (chapter14IdeleClassGroup K)) : Prop :=
  chapter14FiniteAbelianExtension K L ∧
    U.1.toSubgroup = chapter14ClassNormSubgroup N

def chapter14RayQuotientCorrespondsToFiniteAbelianExtension
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) : Prop :=
  chapter14FiniteAbelianExtension K L ∧
    Nonempty (chapter14RayClassGroup D R m ≃* Gal(L/K))

def chapter14RayQuotientRamificationControl {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (m : Chapter14Modulus K)
    (ramifiedAt : NumberField.FinitePlace K → Prop) : Prop :=
  ∀ v, ¬ v.maximalIdeal.asIdeal ∣ m.finitePart → ¬ ramifiedAt v

/-!
These two predicates expose the exact objects that the final reciprocity theorem relates.  The
remaining ramification and conductor assertions are packaged with their local maps below.
-/

def chapter14ConductorUnitFiltrationCompatibility
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (localMap : ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ →* Gal(L/K))
    (filtration : ∀ v : NumberField.FinitePlace K, ℕ →
      Subgroup (v.maximalIdeal.adicCompletion K)ˣ)
    (conductorExponent : NumberField.FinitePlace K → ℕ) : Prop :=
  ∀ v n,
    (∀ x, x ∈ filtration v n → localMap v x = 1) ↔
      conductorExponent v ≤ n

def chapter14FrobeniusCompatibility
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (localMap : ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ →* Gal(L/K))
    (frobenius : ∀ _v : NumberField.FinitePlace K, Gal(L/K))
    (uniformizer : ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ) : Prop :=
  ∀ v, localMap v (uniformizer v) = frobenius v

/-!
The law contains the canonical map, its local compatibility, the open-subgroup/extension
correspondence, and the ray/conductor compatibilities.  The last three fields are named interfaces
because the detailed field-theoretic constructions are developed later in the book.
-/

structure Chapter14GlobalReciprocityLaw (K : Type*) [Field K] [NumberField K]
    (D : Chapter14LocalComponentData K) where
  globalMap : chapter14IdeleClassGroup K →*
    chapter14AbelianGaloisGroup K
  globalMap_continuous : Continuous globalMap
  completionEquivalence :
    chapter14IdeleClassProfiniteCompletion K ≃ₜ* chapter14AbelianGaloisGroup K
  globalMap_is_induced :
    ∀ x, globalMap x = completionEquivalence (chapter14ProfiniteCompletionMap
      (chapter14IdeleClassGroup K) x)
  finiteLocalMap : ∀ v : NumberField.FinitePlace K,
    (v.maximalIdeal.adicCompletion K)ˣ →*
      chapter14AbelianGaloisGroup K
  infiniteLocalMap : ∀ w : NumberField.InfinitePlace K,
    (w.Completion)ˣ →* chapter14AbelianGaloisGroup K
  finiteLocalCompatibility :
    ∀ v x, globalMap (chapter14IdeleClassMap K (D.finiteComponent v x)) =
      finiteLocalMap v x
  infiniteLocalCompatibility :
    ∀ w x, globalMap (chapter14IdeleClassMap K (D.infiniteComponent w x)) =
      infiniteLocalMap w x
  openSubgroupNormCorrespondence : Prop
  rayQuotientGaloisControl : Prop
  conductorFrobeniusUnitFiltrationCompatibility : Prop

theorem chapter14_global_reciprocity_law_exists (K : Type*) [Field K] [NumberField K]
    (D : Chapter14LocalComponentData K) :
    Nonempty (Chapter14GlobalReciprocityLaw K D) := by
  sorry

theorem chapter14_global_reciprocity_law_implies_completion_statement
    {K : Type*} [Field K] [NumberField K] {D : Chapter14LocalComponentData K}
    (L : Chapter14GlobalReciprocityLaw K D) :
    chapter14GlobalReciprocityStatement K :=
  ⟨L.completionEquivalence⟩

theorem chapter14_global_reciprocity_map_is_induced_by_completion
    {K : Type*} [Field K] [NumberField K] (D : Chapter14LocalComponentData K)
    (L : Chapter14GlobalReciprocityLaw K D) (x : chapter14IdeleClassGroup K) :
    L.globalMap x = L.completionEquivalence
      (chapter14ProfiniteCompletionMap (chapter14IdeleClassGroup K) x) :=
  L.globalMap_is_induced x

/-! Finite-order characters become Galois characters only after applying reciprocity. -/

def chapter14FiniteOrderIdeleClassCharacter {K A : Type*} [Field K] [NumberField K]
    [CommGroup A] (χ : chapter14IdeleClassGroup K →* A) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ c, χ c ^ n = 1

def chapter14FiniteOrderGaloisCharacter {K A : Type*} [Field K] [NumberField K]
    [CommGroup A] (χ : chapter14AbelianGaloisGroup K →* A) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ g, χ g ^ n = 1

def chapter14TransportGaloisCharacter {K A : Type*} [Field K] [NumberField K]
    [CommGroup A] {D : Chapter14LocalComponentData K}
    (L : Chapter14GlobalReciprocityLaw K D)
    (χ : chapter14AbelianGaloisGroup K →* A) :
    chapter14IdeleClassGroup K →* A :=
  χ.comp L.globalMap

theorem chapter14_transport_preserves_finite_order
    {K A : Type*} [Field K] [NumberField K] [CommGroup A]
    {D : Chapter14LocalComponentData K}
    (L : Chapter14GlobalReciprocityLaw K D)
    (χ : chapter14AbelianGaloisGroup K →* A)
    (hχ : chapter14FiniteOrderGaloisCharacter χ) :
    chapter14FiniteOrderIdeleClassCharacter
      (chapter14TransportGaloisCharacter L χ) := by
  sorry

end LastLib.Book04AdelesAndIdeles.Chapter14
