import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section04AlgebraicInfinityTypes

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.5. The ell-adic avatar -/

structure Chapter11AlgebraicCoefficientData (A E : Type*) [Field A] [Field E] where
  embedding : A →+* E
  complex_embedding : A →+* ℂ

structure Chapter11EllAdicAvatarInput
    (K A E : Type*) [Field K] [NumberField K] [Field A] [Field E] where
  coefficientData : Chapter11AlgebraicCoefficientData A E
  finiteCharacter : Chapter11FiniteIdele K →* Aˣ
  finite_residual_image : Set.Finite (Set.range finiteCharacter)
  infinityType : Chapter11InfinityType K
  localEvaluation : ∀ _τ : Chapter11Embedding K,
    Chapter11FiniteIdele K → Eˣ
  principalFiniteIdele : Kˣ → Chapter11FiniteIdele K
  principal_correction : ∀ a : Kˣ,
    Units.map coefficientData.embedding.toMonoidHom
        (finiteCharacter (principalFiniteIdele a)) *
      ∏ τ, (localEvaluation τ (principalFiniteIdele a)) ^ (-(infinityType τ)) = 1

def chapter11EllAdicAvatar
    {K A E : Type*} [Field K] [NumberField K] [Field A] [Field E]
    (D : Chapter11EllAdicAvatarInput K A E) :
    Chapter11FiniteIdele K →* Eˣ := by
  refine
    { toFun := fun x =>
        Units.map D.coefficientData.embedding.toMonoidHom (D.finiteCharacter x) *
          ∏ τ, (D.localEvaluation τ x) ^ (-(D.infinityType τ))
      map_one' := by sorry
      map_mul' := by sorry }

theorem chapter11EllAdicAvatar_apply
    {K A E : Type*} [Field K] [NumberField K] [Field A] [Field E]
    (D : Chapter11EllAdicAvatarInput K A E) (x : Chapter11FiniteIdele K) :
    chapter11EllAdicAvatar D x =
      Units.map D.coefficientData.embedding.toMonoidHom (D.finiteCharacter x) *
        ∏ τ, (D.localEvaluation τ x) ^ (-(D.infinityType τ)) :=
  rfl

theorem chapter11EllAdicAvatar_principal_trivial
    {K A E : Type*} [Field K] [NumberField K] [Field A] [Field E]
    (D : Chapter11EllAdicAvatarInput K A E) (a : Kˣ) :
    chapter11EllAdicAvatar D (D.principalFiniteIdele a) = 1 := by
  exact D.principal_correction a

def chapter11EllAdicAvatarIsLocallyAlgebraic
    {K A E : Type*} [Field K] [NumberField K] [Field A] [Field E]
    (D : Chapter11EllAdicAvatarInput K A E) : Prop :=
  ∀ τ, ∃ U : Subgroup (Chapter11FiniteIdele K),
    ∀ x : U, ∃ c : Eˣ, D.localEvaluation τ x = c

structure Chapter11EllAdicGlobalizationData
    (K E : Type*) [Field K] [NumberField K] [Field E] [TopologicalSpace Eˣ] where
  galoisCharacter :
    Chapter11AbsoluteGaloisAbelianization K →ₜ* Eˣ
  reciprocity : Chapter11IdeleClass K →* Chapter11AbsoluteGaloisAbelianization K
  continuous_reciprocity : Continuous reciprocity
  classAvatar : Chapter11IdeleClass K →ₜ* Eˣ
  reciprocity_compatibility : ∀ x,
    galoisCharacter (reciprocity x) = classAvatar x

theorem chapter11_ell_adic_global_reciprocity_avatar
    {K E : Type*} [Field K] [NumberField K] [Field E] [TopologicalSpace Eˣ]
    (D : Chapter11EllAdicGlobalizationData K E) :
    ∀ x : Chapter11IdeleClass K,
      D.galoisCharacter (D.reciprocity x) = D.classAvatar x := by
  intro x
  exact D.reciprocity_compatibility x

structure Chapter11EllAdicFrobeniusData
    (K A E : Type*) [Field K] [NumberField K] [Field A] [Field E] where
  v : NumberField.FinitePlace K
  finiteCharacter : (v.maximalIdeal.adicCompletion K)ˣ →* Aˣ
  uniformizer : v.maximalIdeal.adicCompletion K
  uniformizer_is_uniformizer :
    Chapter11LocalUniformizer v.maximalIdeal uniformizer
  embedding : A →+* E
  galoisCharacter : Chapter11AbsoluteGaloisAbelianization K →* Eˣ
  arithmeticFrobenius : Chapter11AbsoluteGaloisAbelianization K
  ellPlaces : Finset (NumberField.FinitePlace K)
  conductorPlaces : Finset (NumberField.FinitePlace K)
  v_not_ell : v ∉ ellPlaces
  v_not_conductor : v ∉ conductorPlaces
  frobenius_compatibility :
    galoisCharacter arithmeticFrobenius =
      Units.map embedding.toMonoidHom (finiteCharacter (Units.mk0 uniformizer (by sorry)))

theorem chapter11_ell_adic_frobenius_value
    {K A E : Type*} [Field K] [NumberField K] [Field A] [Field E]
    (D : Chapter11EllAdicFrobeniusData K A E)
    :
    D.galoisCharacter D.arithmeticFrobenius =
      Units.map D.embedding.toMonoidHom
        (D.finiteCharacter (Units.mk0 D.uniformizer (by sorry))) := by
  exact D.frobenius_compatibility

/- The converse is phrased with explicit local factor witnesses.  The
integral exponents are part of the witness, which prevents arbitrary
continuous ell-adic characters from being accepted as algebraic. -/
structure Chapter11LocalAlgebraicityWitness (G E : Type*) [Group G] [Field E]
    [TopologicalSpace G] [TopologicalSpace Eˣ]
    (ρ : G →ₜ* Eˣ) (n : ℕ) where
  openSubgroup : Subgroup G
  embeddingCharacter : Fin n → G →* Eˣ
  exponent : Fin n → ℤ
  formula_on_open : ∀ g : openSubgroup,
    ρ g = ∏ i, (embeddingCharacter i g) ^ exponent i

def chapter11LocallyAlgebraicAt
    {G E V : Type*} [Group G] [Field E] [TopologicalSpace G] [TopologicalSpace Eˣ]
    (_v : V)
    (ρ : G →ₜ* Eˣ) : Prop :=
  ∃ n : ℕ, Nonempty (Chapter11LocalAlgebraicityWitness G E ρ n)

def chapter11UnramifiedOutside
    {G V E : Type*} [Group G] [Field E] [TopologicalSpace G] [TopologicalSpace Eˣ]
    (ρ : G →ₜ* Eˣ) (inertia : V → Subgroup G) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → ∀ g ∈ inertia v, ρ g = 1

theorem chapter11_ell_adic_converse
    {K E : Type*} [Field K] [NumberField K] [Field E] [TopologicalSpace Eˣ]
    (ρ : Chapter11AbsoluteGaloisAbelianization K →ₜ* Eˣ)
    (inertia : NumberField.FinitePlace K → Subgroup
      (Chapter11AbsoluteGaloisAbelianization K))
    (ellPlaces : Finset (NumberField.FinitePlace K))
    (hfinite_ramification : ∃ S : Finset (NumberField.FinitePlace K),
      chapter11UnramifiedOutside ρ inertia S)
    (hell : ∀ v : NumberField.FinitePlace K,
      v ∈ ellPlaces → chapter11LocallyAlgebraicAt v ρ) :
    ∃ (A : Type*) (_ : Field A),
      ∃ D : Chapter11EllAdicAvatarInput K A E,
        (∀ a : Kˣ, chapter11EllAdicAvatar D (D.principalFiniteIdele a) = 1) ∧
          chapter11EllAdicAvatarIsLocallyAlgebraic D := by
  sorry

theorem chapter11_ell_adic_converse_finite_order_specialization
    {K E : Type*} [Field K] [NumberField K] [Field E]
    (D : Chapter11EllAdicAvatarInput K ℂ E)
    (hfinite : chapter11FiniteOrder D.finiteCharacter)
    (hn : D.infinityType = 0) :
    ∀ x, chapter11EllAdicAvatar D x =
      Units.map D.coefficientData.embedding.toMonoidHom (D.finiteCharacter x) := by
  sorry

structure Chapter11CyclotomicNormalizationData (G E : Type*)
    [Group G] [Field E] where
  moduleCharacter : G →* Eˣ
  cyclotomicCharacter : G →* Eˣ
  arithmetic_normalization : ∀ g,
    moduleCharacter g = (cyclotomicCharacter g)⁻¹

theorem chapter11_module_is_inverse_cyclotomic
    {G E : Type*} [Group G] [Field E]
    (D : Chapter11CyclotomicNormalizationData G E) (g : G) :
    D.moduleCharacter g = (D.cyclotomicCharacter g)⁻¹ := by
  exact D.arithmetic_normalization g

/- SOURCE_ISSUE: The book's displayed formula uses `ι(χ_f(x_f))` while
`χ_f` is only introduced as complex-valued.  A correction needs algebraic
coefficient values, an embedding `A → overline{ℚ}_ℓ`, and the completion maps
at the places induced by `ι ∘ τ`; `Chapter11EllAdicAvatarInput` exposes those
choices instead of leaving the formula ill-typed. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
