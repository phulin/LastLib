import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open NumberField IsDedekindDomain

/-!
## 9.3. Compactness of the norm-one class group
-/

abbrev Chapter09ArchimedeanUnitQuotient
    (K : Type*) [Field K] [NumberField K] :=
  (chapter09KInfinityOne K) ⧸ (chapter09ArchimedeanUnitEmbedding K).range

theorem chapter09_finite_unit_ideles_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09FiniteUnitIdeles K)) := by
  sorry

theorem chapter09_archimedean_unit_quotient_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter09ArchimedeanUnitQuotient K)) := by
  sorry

/- The finite class group contributes only finitely many choices of a finite
idele representative.  The following interface is the precise reduction
statement used in the compactness proof; it contains no compactness claim. -/
structure Chapter09FiniteClassRepresentativeData
    (K : Type*) [Field K] [NumberField K] where
  representatives : Fin (Fintype.card (ClassGroup (𝓞 K))) → (Chapter09FiniteAdele K)ˣ
  represents_every_class :
    ∀ c : ClassGroup (𝓞 K), ∃ i,
      (chapter09CanonicalIdeleIdealData K).idealClassMap (representatives i) = c

theorem chapter09_finite_class_representatives_exist
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter09FiniteClassRepresentativeData K) := by
  sorry

theorem chapter09_normOne_class_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09ClassNormOne K)) := by
  sorry

noncomputable instance chapter09CompactSpaceClassNormOne
    (K : Type*) [Field K] [NumberField K] : CompactSpace (chapter09ClassNormOne K) :=
  ⟨chapter09_normOne_class_compact K⟩

theorem chapter09_normOne_class_has_compact_representatives
    (K : Type*) [Field K] [NumberField K] :
    ∃ S : Set (chapter09NormOneIdeles K), IsCompact S ∧
      ∀ x : chapter09ClassNormOne K, ∃ s ∈ S,
        chapter09NormOneClassGroup_equiv_classNormOne (K := K)
            (QuotientGroup.mk s) = x := by
  sorry

/- Finite local units are profinite, while the archimedean logarithmic part is
compact only after quotienting by the global unit lattice.  This is the API
form of the source's warning that `C_K^1` is generally disconnected. -/
theorem chapter09_normOne_class_finite_unit_factor_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (chapter09FiniteUnitIdeles K)) :=
  chapter09_finite_unit_ideles_compact K

end

end LastLib.Book04AdelesAndIdeles.Chapter09
