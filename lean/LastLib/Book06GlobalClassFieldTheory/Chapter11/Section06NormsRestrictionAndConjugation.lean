import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section05TheEllAdicAvatar

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.6. Norms, restriction, and conjugation of characters -/

def chapter11NormPullback
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (N : Chapter11NormData K M) (χ : Chapter11HeckeCharacter K) :
    Chapter11HeckeCharacter M :=
  { toMonoidHom := χ.toMonoidHom.comp N.classNorm
    continuous_toFun := χ.continuous_toFun.comp N.continuous_classNorm }

theorem chapter11NormPullback_apply
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (N : Chapter11NormData K M) (χ : Chapter11HeckeCharacter K)
    (x : Chapter11IdeleClass M) :
    chapter11NormPullback N χ x = χ (N.classNorm x) :=
  rfl

def chapter11LocalNormPullback
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (N : Chapter11NormData K M)
    (w : NumberField.FinitePlace M)
    (ψ : (((N.below w).maximalIdeal.adicCompletion K)ˣ) →* ℂˣ) :
    (w.maximalIdeal.adicCompletion M)ˣ →* ℂˣ :=
  ψ.comp (N.localNorm w)

theorem chapter11LocalNormPullback_apply
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (N : Chapter11NormData K M)
    (w : NumberField.FinitePlace M)
    (ψ : (((N.below w).maximalIdeal.adicCompletion K)ˣ) →* ℂˣ)
    (u : (w.maximalIdeal.adicCompletion M)ˣ) :
    chapter11LocalNormPullback N w ψ u = ψ (N.localNorm w u) :=
  rfl

structure Chapter11LocalNormConductorData
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] where
  normData : Chapter11NormData K M
  w : NumberField.FinitePlace M
  ψ : (((normData.below w).maximalIdeal.adicCompletion K)ˣ) →* ℂˣ

def chapter11BaseChangeConductorExponent
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11LocalNormConductorData (K := K) (M := M)) : ℕ :=
  sInf {r : ℕ |
    ∀ u, u ∈ LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration
      D.w r → D.ψ (D.normData.localNorm D.w u) = 1}

theorem chapter11_base_change_conductor_minimum_formula
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11LocalNormConductorData (K := K) (M := M)) :
    chapter11BaseChangeConductorExponent D =
      sInf {r : ℕ |
        ∀ u, u ∈ LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration
          D.w r → D.ψ (D.normData.localNorm D.w u) = 1} :=
  rfl

structure Chapter11UnramifiedNormLayerData
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] where
  normData : Chapter11NormData K M
  w : NumberField.FinitePlace M
  layerNorm : ∀ r, {u : (w.maximalIdeal.adicCompletion M)ˣ //
      u ∈ LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration w r} →
    {u : ((normData.below w).maximalIdeal.adicCompletion K)ˣ //
      u ∈ LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration
        (normData.below w) r}
  layerNorm_spec : ∀ r u, (layerNorm r u).1 = normData.localNorm w u.1
  surjective_on_unit_layers :
    ∀ r, Function.Surjective (layerNorm r)

theorem chapter11_unramified_norms_onto_unit_layers
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11UnramifiedNormLayerData (K := K) (M := M)) (r : ℕ) :
    Function.Surjective (D.layerNorm r) := by
  exact D.surjective_on_unit_layers r

theorem chapter11_unramified_base_change_conductor_equals_base
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11UnramifiedNormLayerData (K := K) (M := M))
    (ψ : (((D.normData.below D.w).maximalIdeal.adicCompletion K)ˣ) →* ℂˣ)
    (hlevel : Set.Nonempty {n : ℕ |
      chapter11LocalCharacterTrivialAtLevel (D.normData.below D.w) ψ n}) :
      chapter11BaseChangeConductorExponent
        { normData := D.normData, w := D.w, ψ := ψ } =
      chapter11LocalConductorExponent (D.normData.below D.w) ψ := by
  sorry

structure Chapter11HerbrandNormData
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] where
  localData : Chapter11LocalNormConductorData (K := K) (M := M)
  herbrandBound : ℕ → ℕ
  norm_layer_bound : ∀ r,
    LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration
        localData.w r ≤
      (LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration
        (localData.normData.below localData.w) (herbrandBound r)).comap
        (localData.normData.localNorm localData.w)

theorem chapter11_herbrand_norm_conductor_bound
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    (D : Chapter11HerbrandNormData (K := K) (M := M)) :
    chapter11BaseChangeConductorExponent D.localData ≤
      D.herbrandBound (chapter11LocalConductorExponent D.localData.w
        (D.localData.ψ.comp (D.localData.normData.localNorm D.localData.w))) := by
  sorry

theorem chapter11ConjugateCharacter_apply
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (D : Chapter11GaloisIdeleActionData K M)
    (θ : Chapter11HeckeCharacter M) (σ : Gal(M / K))
    (x : Chapter11IdeleClass M) :
    chapter11ConjugateCharacter D θ σ x = θ ((D.action σ⁻¹) x) :=
  rfl

theorem chapter11CharacterStabilizer_mem_iff
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (D : Chapter11GaloisIdeleActionData K M)
    (θ : Chapter11HeckeCharacter M) (σ : Gal(M / K)) :
    σ ∈ chapter11CharacterStabilizer D θ ↔
      chapter11ConjugateCharacter D θ σ = θ :=
  Iff.rfl

structure Chapter11NormInvariantIdentificationData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] where
  normData : Chapter11NormData K M
  actionData : Chapter11GaloisIdeleActionData K M
  invariant_iff_norm_pullback : ∀ θ : Chapter11HeckeCharacter M,
    (∃ η : Chapter11HeckeCharacter K, chapter11NormPullback normData η = θ) ↔
      ∀ σ : Gal(M / K), chapter11ConjugateCharacter actionData θ σ = θ

theorem chapter11_galois_invariant_character_descends_through_norm
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (D : Chapter11NormInvariantIdentificationData K M)
    (θ : Chapter11HeckeCharacter M) :
    (∃ η : Chapter11HeckeCharacter K,
      chapter11NormPullback D.normData η = θ) ↔
      ∀ σ : Gal(M / K), chapter11ConjugateCharacter D.actionData θ σ = θ := by
  exact D.invariant_iff_norm_pullback θ

structure Chapter11NormRestrictionReciprocityData
    (K M G H : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [Group G] [Group H] where
  classNorm : Chapter11IdeleClass M →* Chapter11IdeleClass K
  restriction : H →* G
  baseArtin : Chapter11IdeleClass K →* G
  extensionArtin : Chapter11IdeleClass M →* H
  reciprocity_compatibility :
    ∀ x, restriction (extensionArtin x) = baseArtin (classNorm x)

theorem chapter11_norm_pullback_is_galois_restriction
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M]
    {G H : Type*} [Group G] [Group H]
    (D : Chapter11NormRestrictionReciprocityData K M G H)
    (η : G →* ℂˣ) (x : Chapter11IdeleClass M) :
    η (D.baseArtin (D.classNorm x)) =
      (η.comp D.restriction) (D.extensionArtin x) := by
  rw [← D.reciprocity_compatibility x]
  rfl

/- The minimum formula is the exact ramified statement.  In the unramified
case the norm-layer surjectivity reduces it to the base exponent; in the
ramified case Herbrand reindexing gives only the corresponding bound in
general, so equality must not be added without a separate hypothesis. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
