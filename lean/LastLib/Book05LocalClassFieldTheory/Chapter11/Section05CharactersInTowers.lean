import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section01ExactTopologicalStatement

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.5. Characters in towers -/

def chapter11RestrictedGaloisCharacter
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [TopologicalSpace A]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (T : Chapter11TowerData K L Gₖ Gₗ)
    (χₖ : Kˣ →ₜ* A) : Gₗ →ₜ* A :=
  (chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ |>.comp T.restriction

def chapter11NormPullbackCharacter
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace A] [IsTopologicalGroup A]
    (hcont : Continuous (chapter11NormHom K L))
    (χₖ : Kˣ →ₜ* A) : Lˣ →ₜ* A :=
  χₖ.comp (chapter11ContinuousNormHom K L hcont)

theorem chapter11_restriction_of_galois_character_corresponds_to_norm
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [TopologicalSpace A]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (Rₗ : Chapter11ReciprocityData L Gₗ)
    (T : Chapter11TowerData K L Gₖ Gₗ)
    (χₖ : Kˣ →ₜ* A)
    (hcompat : chapter11NormRestrictionCompatibility Rₖ Rₗ T) :
    (chapter11ContinuousCharacterEquiv (A := A) Rₗ)
        (chapter11RestrictedGaloisCharacter Rₖ T χₖ) =
      chapter11NormPullbackCharacter T.norm_continuous χₖ := by
  sorry

def chapter11RestrictedMultiplicativeCharacter
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommGroup A] [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace A] [IsTopologicalGroup A]
    (hcont : Continuous (chapter11MultiplicativeInclusion K L))
    (χₗ : Lˣ →ₜ* A) : Kˣ →ₜ* A :=
  χₗ.comp (chapter11ContinuousMultiplicativeInclusion K L hcont)

def chapter11TransferredGaloisCharacter
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [TopologicalSpace A]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (Rₗ : Chapter11ReciprocityData L Gₗ)
    (T : Chapter11TowerData K L Gₖ Gₗ)
    (χₗ : Lˣ →ₜ* A) : Kˣ →ₜ* A :=
  chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ
    ((chapter11AbelianContinuousCharacterEquiv (A := A) Rₗ).symm χₗ |>.comp T.transferAb)

theorem chapter11_restriction_of_multiplicative_character_corresponds_to_transfer
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [TopologicalSpace A]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (Rₗ : Chapter11ReciprocityData L Gₗ)
    (T : Chapter11TowerData K L Gₖ Gₗ)
    (χₗ : Lˣ →ₜ* A)
    (hcompat : chapter11TransferInclusionCompatibility Rₖ Rₗ T) :
    chapter11TransferredGaloisCharacter Rₖ Rₗ T χₗ =
      chapter11RestrictedMultiplicativeCharacter T.inclusion_continuous χₗ := by
  sorry

theorem chapter11_norm_restriction_and_transfer_inclusion_dictionary
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Group Gₖ] [Group Gₗ] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace Gₖ] [TopologicalSpace Gₗ] [TopologicalSpace A]
    [IsTopologicalGroup Gₖ] [IsTopologicalGroup Gₗ] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (Rₖ : Chapter11ReciprocityData K Gₖ)
    (Rₗ : Chapter11ReciprocityData L Gₗ)
    (T : Chapter11TowerData K L Gₖ Gₗ)
    (χₖ : Kˣ →ₜ* A) (χₗ : Lˣ →ₜ* A)
    (hₙ : chapter11NormRestrictionCompatibility Rₖ Rₗ T)
    (hₜ : chapter11TransferInclusionCompatibility Rₖ Rₗ T) :
    ((chapter11ContinuousCharacterEquiv (A := A) Rₗ)
        (chapter11RestrictedGaloisCharacter Rₖ T χₖ) =
      chapter11NormPullbackCharacter T.norm_continuous χₖ) ∧
      (chapter11TransferredGaloisCharacter Rₖ Rₗ T χₗ =
        chapter11RestrictedMultiplicativeCharacter T.inclusion_continuous χₗ) := by
  constructor
  · exact chapter11_restriction_of_galois_character_corresponds_to_norm
      Rₖ Rₗ T χₖ hₙ
  · exact chapter11_restriction_of_multiplicative_character_corresponds_to_transfer
      Rₖ Rₗ T χₗ hₜ

/- The chosen embedding and compatible separable closures are represented by
  the explicit restriction and transfer maps in `Chapter11TowerData`. -/

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
