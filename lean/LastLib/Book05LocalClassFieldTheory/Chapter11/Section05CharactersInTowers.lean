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
  have hcharAb_symm :
      chapter11CharacterAbelianization
          ((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ) =
        (chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ).symm χₖ := by
    apply DFunLike.ext
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hspec := chapter11CharacterAbelianization_spec
      ((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ)
    exact (DFunLike.congr_fun hspec g).symm
  have hrestriction :
      chapter11CharacterAbelianization
          (((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ).comp
            T.restriction) =
        ((chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ).symm χₖ).comp
          T.restrictionAb := by
    apply DFunLike.ext
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hcomp := chapter11CharacterAbelianization_spec
      (((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ).comp
        T.restriction)
    have hbase := chapter11CharacterAbelianization_spec
      ((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ)
    have htransfer := congrArg (fun f => f g)
      T.restrictionAb_compatibility
    change T.restrictionAb (chapter11AbelianizationMap Gₗ g) =
      chapter11AbelianizationMap Gₖ (T.restriction g) at htransfer
    calc
      chapter11CharacterAbelianization
          (((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ).comp
            T.restriction)
          (chapter11AbelianizationMap Gₗ g) =
          (((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ).comp
            T.restriction) g := (DFunLike.congr_fun hcomp g).symm
      _ = (chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ
          (T.restriction g) := rfl
      _ = chapter11CharacterAbelianization
          ((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ)
          (chapter11AbelianizationMap Gₖ (T.restriction g)) :=
        DFunLike.congr_fun hbase (T.restriction g)
      _ = chapter11CharacterAbelianization
          ((chapter11ContinuousCharacterEquiv (A := A) Rₖ).symm χₖ)
          (T.restrictionAb (chapter11AbelianizationMap Gₗ g)) := by
        rw [← htransfer]
      _ = (chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ).symm χₖ
          (T.restrictionAb (chapter11AbelianizationMap Gₗ g)) := by
        rw [hcharAb_symm]
  simp only [chapter11RestrictedGaloisCharacter, chapter11NormPullbackCharacter,
    chapter11_continuous_character_equiv_apply, hrestriction,
    chapter11_abelian_continuous_character_equiv_apply]
  apply DFunLike.ext
  intro x
  change ((chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ).symm χₖ)
      (T.restrictionAb (Rₗ.reciprocity x)) =
    χₖ (chapter11ContinuousNormHom K L T.norm_continuous x)
  have hcompat' :
      T.restrictionAb.comp Rₗ.reciprocity =
      Rₖ.reciprocity.comp
          (chapter11ContinuousNormHom K L T.norm_continuous) :=
    by
      simpa only [chapter11NormRestrictionCompatibility] using
        hcompat
  have hcompat_apply := congrArg (fun f => f x) hcompat'
  change T.restrictionAb (Rₗ.reciprocity x) =
    Rₖ.reciprocity (chapter11ContinuousNormHom K L T.norm_continuous x) at hcompat_apply
  rw [hcompat_apply]
  have happly := chapter11_abelian_continuous_character_equiv_apply
    (R := Rₖ)
    ((chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ).symm χₖ)
  rw [(chapter11AbelianContinuousCharacterEquiv (A := A) Rₖ).apply_symm_apply χₖ]
    at happly
  exact (DFunLike.congr_fun happly
    (chapter11ContinuousNormHom K L T.norm_continuous x)).symm

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
  simp only [chapter11TransferredGaloisCharacter,
    chapter11RestrictedMultiplicativeCharacter,
    chapter11_abelian_continuous_character_equiv_apply]
  apply DFunLike.ext
  intro x
  change ((chapter11AbelianContinuousCharacterEquiv (A := A) Rₗ).symm χₗ)
      (T.transferAb (Rₖ.reciprocity x)) =
    χₗ (chapter11ContinuousMultiplicativeInclusion K L T.inclusion_continuous x)
  have hcompat' :
      T.transferAb.comp Rₖ.reciprocity =
      Rₗ.reciprocity.comp
          (chapter11ContinuousMultiplicativeInclusion K L T.inclusion_continuous) :=
    by
      simpa only [chapter11TransferInclusionCompatibility] using
        hcompat
  have hcompat_apply := congrArg (fun f => f x) hcompat'
  change T.transferAb (Rₖ.reciprocity x) =
    Rₗ.reciprocity
      (chapter11ContinuousMultiplicativeInclusion K L T.inclusion_continuous x)
    at hcompat_apply
  rw [hcompat_apply]
  have happly := chapter11_abelian_continuous_character_equiv_apply
    (R := Rₗ)
    ((chapter11AbelianContinuousCharacterEquiv (A := A) Rₗ).symm χₗ)
  rw [(chapter11AbelianContinuousCharacterEquiv (A := A) Rₗ).apply_symm_apply χₗ]
    at happly
  exact (DFunLike.congr_fun happly
    (chapter11ContinuousMultiplicativeInclusion K L T.inclusion_continuous x)).symm

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
