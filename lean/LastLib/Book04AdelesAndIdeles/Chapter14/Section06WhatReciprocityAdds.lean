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
    ∃ ρ : chapter14IdeleClassGroup K →* Gal(L/K),
      Function.Surjective ρ ∧ ρ.ker = U.1.toSubgroup

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
    (m : Chapter14Modulus K) : Prop :=
    chapter14FiniteAbelianExtension K L ∧
    ∃ ρ : chapter14IdeleClassGroup K →* Gal(L/K),
      Function.Surjective ρ ∧
        ρ.ker = (chapter14RayClassQuotientMap m).ker

def chapter14RayQuotientRamificationControl {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K)
    (ramifiedAtFinite : NumberField.FinitePlace K → Prop)
    (ramifiedAtReal : NumberField.InfinitePlace K → Prop) : Prop :=
  (∀ v, ¬ v.maximalIdeal.asIdeal ∣ m.finiteIdeal → ¬ ramifiedAtFinite v) ∧
    (∀ w, w ∉ (m.infinitePart : Set (NumberField.InfinitePlace K)) →
      ¬ ramifiedAtReal w)

/-! A quotient-level witness packages the finite abelian extension and the actual kernel of its
reciprocity map.  This keeps the later correspondence fields from degenerating into unconnected
propositions. -/
structure Chapter14FiniteAbelianExtensionWitness
    (K : Type*) [Field K] [NumberField K]
    (N : Subgroup (chapter14IdeleClassGroup K)) where
  L : Type
  [field_L : Field L]
  [numberField_L : NumberField L]
  [algebra_K_L : Algebra K L]
  [finiteDimensional_K_L : FiniteDimensional K L]
  [galois_K_L : IsGalois K L]
  abelian : IsMulCommutative Gal(L/K)
  normData : Chapter14AdelicNormInterface K L
  norm_group : chapter14ClassNormSubgroup normData = N
  reciprocity : chapter14IdeleClassGroup K →* Gal(L/K)
  reciprocity_surjective : Function.Surjective reciprocity
  reciprocity_kernel : reciprocity.ker = N

/-!
These two predicates expose the exact objects that the final reciprocity theorem relates.  The
remaining ramification and conductor assertions are packaged with their local maps below.
-/

def chapter14ConductorUnitFiltrationCompatibility
    {K G : Type*} [Field K] [NumberField K] [Group G]
    (localMap : ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ →* G)
    (filtration : ∀ v : NumberField.FinitePlace K, ℕ →
      Subgroup (v.maximalIdeal.adicCompletion K)ˣ)
    (conductorExponent : NumberField.FinitePlace K → ℕ) : Prop :=
  ∀ v n,
    (∀ x, x ∈ filtration v n → localMap v x = 1) ↔
      conductorExponent v ≤ n

def chapter14FrobeniusCompatibility
    {K G : Type*} [Field K] [NumberField K] [Group G]
    (localMap : ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ →* G)
    (unramifiedAt : NumberField.FinitePlace K → Prop)
    (convention : Chapter14FrobeniusConvention)
    (frobenius : Chapter14FrobeniusConvention →
      NumberField.FinitePlace K → G)
    (uniformizer : ∀ v : NumberField.FinitePlace K,
      (v.maximalIdeal.adicCompletion K)ˣ) : Prop :=
  ∀ v, unramifiedAt v → localMap v (uniformizer v) = frobenius convention v

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
  finiteLocalMap_continuous :
    ∀ v, Continuous (finiteLocalMap v)
  infiniteLocalMap : ∀ w : NumberField.InfinitePlace K,
    (w.Completion)ˣ →* chapter14AbelianGaloisGroup K
  infiniteLocalMap_continuous :
    ∀ w, Continuous (infiniteLocalMap w)
  finiteLocalCompatibility :
    ∀ v x, globalMap (chapter14IdeleClassMap K (D.finiteComponent v x)) =
      finiteLocalMap v x
  infiniteLocalCompatibility :
    ∀ w x, globalMap (chapter14IdeleClassMap K (D.infiniteComponent w x)) =
      infiniteLocalMap w x
  openSubgroupNormCorrespondence :
    ∀ U : Chapter14OpenFiniteIndexSubgroup (chapter14IdeleClassGroup K),
      Nonempty (Chapter14FiniteAbelianExtensionWitness K U.1.toSubgroup)
  rayQuotientGaloisControl :
    ∀ m : Chapter14Modulus K,
      Nonempty (Chapter14FiniteAbelianExtensionWitness K
        (chapter14RayClassQuotientMap m).ker)
  conductorFrobeniusUnitFiltrationCompatibility :
    ∃ filtration : ∀ v : NumberField.FinitePlace K, ℕ →
        Subgroup (v.maximalIdeal.adicCompletion K)ˣ,
      ∃ conductorExponent : NumberField.FinitePlace K → ℕ,
        ∃ unramifiedAt : NumberField.FinitePlace K → Prop,
          ∃ convention : Chapter14FrobeniusConvention,
            ∃ frobenius : Chapter14FrobeniusConvention →
                NumberField.FinitePlace K → chapter14AbelianGaloisGroup K,
              ∃ uniformizer : ∀ v : NumberField.FinitePlace K,
                  (v.maximalIdeal.adicCompletion K)ˣ,
                chapter14ConductorUnitFiltrationCompatibility
                    finiteLocalMap filtration conductorExponent ∧
                  chapter14FrobeniusCompatibility finiteLocalMap unramifiedAt convention
                    frobenius uniformizer

theorem chapter14_global_reciprocity_law_exists (K : Type*) [Field K] [NumberField K]
    : ∃ D : Chapter14LocalComponentData K,
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
    [CommGroup A] [TopologicalSpace A]
    (χ : chapter14IdeleClassGroup K →* A) : Prop :=
  Continuous χ ∧ ∃ n : ℕ, 0 < n ∧ ∀ c, χ c ^ n = 1

def chapter14FiniteOrderGaloisCharacter {K A : Type*} [Field K] [NumberField K]
    [CommGroup A] [TopologicalSpace A]
    (χ : chapter14AbelianGaloisGroup K →* A) : Prop :=
  Continuous χ ∧ ∃ n : ℕ, 0 < n ∧ ∀ g, χ g ^ n = 1

def chapter14TransportGaloisCharacter {K A : Type*} [Field K] [NumberField K]
    [CommGroup A] [TopologicalSpace A] {D : Chapter14LocalComponentData K}
    (L : Chapter14GlobalReciprocityLaw K D)
    (χ : chapter14AbelianGaloisGroup K →* A) :
    chapter14IdeleClassGroup K →* A :=
  χ.comp L.globalMap

theorem chapter14_transport_preserves_finite_order
    {K A : Type*} [Field K] [NumberField K] [CommGroup A] [TopologicalSpace A]
    {D : Chapter14LocalComponentData K}
    (L : Chapter14GlobalReciprocityLaw K D)
    (χ : chapter14AbelianGaloisGroup K →* A)
    (hχ : chapter14FiniteOrderGaloisCharacter χ) :
    chapter14FiniteOrderIdeleClassCharacter
      (chapter14TransportGaloisCharacter L χ) := by
  sorry

end LastLib.Book04AdelesAndIdeles.Chapter14
