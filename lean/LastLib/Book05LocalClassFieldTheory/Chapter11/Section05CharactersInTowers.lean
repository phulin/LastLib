import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section01ExactTopologicalStatement

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.5. Characters in towers -/

def chapter11RestrictedGaloisCharacter
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
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
    [FiniteDimensional K L] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace A] [IsTopologicalGroup A]
    (χₖ : Kˣ →ₜ* A) : Lˣ →ₜ* A :=
  χₖ.comp (chapter11ContinuousNormHom K L)

theorem chapter11_restriction_of_galois_character_corresponds_to_norm
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group Gₖ] [Group Gₗ] [CommGroup A]
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
      chapter11NormPullbackCharacter χₖ := by
  sorry

def chapter11RestrictedMultiplicativeCharacter
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommGroup A] [TopologicalSpace Kˣ] [TopologicalSpace Lˣ]
    [TopologicalSpace A] [IsTopologicalGroup A]
    (χₗ : Lˣ →ₜ* A) : Kˣ →ₜ* A :=
  χₗ.comp (chapter11ContinuousMultiplicativeInclusion K L)

def chapter11TransferredGaloisCharacter
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
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
      chapter11RestrictedMultiplicativeCharacter χₗ := by
  sorry

theorem chapter11_norm_restriction_and_transfer_inclusion_dictionary
    {K L Gₖ Gₗ A : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group Gₖ] [Group Gₗ] [CommGroup A]
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
      chapter11NormPullbackCharacter χₖ) ∧
      (chapter11TransferredGaloisCharacter Rₖ Rₗ T χₗ =
        chapter11RestrictedMultiplicativeCharacter χₗ) := by
  constructor
  · exact chapter11_restriction_of_galois_character_corresponds_to_norm
      Rₖ Rₗ T χₖ hₙ
  · exact chapter11_restriction_of_multiplicative_character_corresponds_to_transfer
      Rₖ Rₗ T χₗ hₜ

/- SOURCE_ISSUE: the source says, "Let `L/K` be finite separable" and then
  writes `G_L ↪ G_K`.  Finite separability alone does not choose compatible
  separable closures, hence does not canonically define that map.  The
  declarations above make the required restriction and transfer maps
  explicit through `Chapter11TowerData`. -/

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
