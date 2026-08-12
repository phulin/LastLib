import LastLib.Book03RamificationTheory.Chapter13.Core
import LastLib.Book03RamificationTheory.Chapter12.Section01InductionAndArtinCharacters

namespace LastLib.Book03RamificationTheory.Chapter13

noncomputable section

open LastLib.Book03RamificationTheory.Chapter11
open LastLib.Book03RamificationTheory.Chapter12
open scoped BigOperators

/-! ## 13.1. The permutation representation of embeddings -/

/-- The finite embedding set on which the chosen Galois closure acts. -/
abbrev chapter13EmbeddingSet
    (K M Ω : Type*) [Field K] [Field M] [Field Ω]
    [Algebra K M] [Algebra K Ω] := AlgHom K M Ω

theorem chapter13_embedding_set_is_finite
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G) :
    Finite (chapter13EmbeddingSet K M Ω) :=
  C.finite_embeddings

theorem chapter13_embedding_action_is_postcomposition
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G)
    (g : G) (φ : chapter13EmbeddingSet K M Ω) :
    g • φ = (C.group_identification g).toAlgHom.comp φ := by
  exact C.action_compatible g φ

/- The permutation module is the canonical `MonoidAlgebra` linearization of
the G-action on the embedding set. -/
noncomputable def chapter13EmbeddingPermutationRepresentation
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (_C : Chapter13NongaloisExtensionContext K M Ω G) :
  Representation ℚ G (MonoidAlgebra ℚ (chapter13EmbeddingSet K M Ω)) := by
  exact Representation.ofMulAction ℚ G (chapter13EmbeddingSet K M Ω)

@[simp] theorem chapter13EmbeddingPermutationRepresentation_apply
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G)
    (g : G) :
    chapter13EmbeddingPermutationRepresentation C g =
      Representation.ofMulAction ℚ G (chapter13EmbeddingSet K M Ω) g := by
  rfl

/- The subgroup fixing the selected embedding is the finite realization of
`G_M`, while `G` is the finite quotient representing `G_K`. -/
def chapter13InducedTrivialEmbeddingRepresentation
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G) :
    Representation ℚ G
      (Representation.IndV (chapter13EmbeddingStabilizer C).subtype
        (Representation.trivial ℚ (chapter13EmbeddingStabilizer C) ℚ)) :=
  Representation.ind (chapter13EmbeddingStabilizer C).subtype
    (Representation.trivial ℚ (chapter13EmbeddingStabilizer C) ℚ)

theorem chapter13_embedding_permutation_is_induced_trivial
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G) :
    Nonempty
      ((chapter13InducedTrivialEmbeddingRepresentation C).Equiv
        (chapter13EmbeddingPermutationRepresentation C)) := by
  sorry

theorem chapter13_embedding_permutation_is_induced_trivial_symm
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G) :
    Nonempty
      ((chapter13EmbeddingPermutationRepresentation C).Equiv
        (chapter13InducedTrivialEmbeddingRepresentation C)) := by
  sorry

/- The conductor of the permutation action is the discriminant exponent of
the nongalois extension.  The two character comparisons are precisely the
off-identity and identity normalizations supplied by Chapter 12's induction
formula. -/
theorem chapter13_permutation_conductor_discriminant
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G)
    (AK : Chapter12ConductorProfile G)
    (AM : Chapter12ConductorProfile (chapter13EmbeddingStabilizer C))
    (hres : C.residue_extension_separable)
    (hoff : ∀ h, h ≠ 1 →
      AK.artinCharacter ((chapter13EmbeddingStabilizer C).subtype h) =
        (C.numbers.residueDegree : ℚ) * AM.artinCharacter h)
    (hone :
      AK.artinCharacter ((chapter13EmbeddingStabilizer C).subtype 1) -
          (C.numbers.residueDegree : ℚ) * AM.artinCharacter 1 =
        (Nat.card (chapter13EmbeddingStabilizer C) : ℚ) *
          (C.numbers.discriminantExponent : ℚ)) :
    (AK.artinConductor _ (chapter13EmbeddingPermutationRepresentation C) : ℚ) =
      (C.numbers.discriminantExponent : ℚ) := by
  sorry

theorem chapter13_permutation_conductor_eq_relative_discriminant_valuation
    {K M Ω G : Type*}
    [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    [Group G] [Fintype G] [MulAction G (chapter13EmbeddingSet K M Ω)]
    [Fintype (chapter13EmbeddingSet K M Ω)]
    (C : Chapter13NongaloisExtensionContext K M Ω G)
    (AK : Chapter12ConductorProfile G)
    (AM : Chapter12ConductorProfile (chapter13EmbeddingStabilizer C))
    (hres : C.residue_extension_separable)
    (hoff : ∀ h, h ≠ 1 →
      AK.artinCharacter ((chapter13EmbeddingStabilizer C).subtype h) =
        (C.numbers.residueDegree : ℚ) * AM.artinCharacter h)
    (hone :
      AK.artinCharacter ((chapter13EmbeddingStabilizer C).subtype 1) -
          (C.numbers.residueDegree : ℚ) * AM.artinCharacter 1 =
        (Nat.card (chapter13EmbeddingStabilizer C) : ℚ) *
          (C.numbers.discriminantExponent : ℚ)) :
    (AK.artinConductor _ (chapter13EmbeddingPermutationRepresentation C) : ℚ) =
      (C.relative_discriminant_valuation : ℚ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter13
