import LastLib.Book06GlobalClassFieldTheory.Chapter12.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter12

noncomputable section

open scoped BigOperators
open LastLib.Book05LocalClassFieldTheory.Chapter11

/-! ## 12.5. Characters at a glance -/

structure Chapter12HeckeCharacterPresentation
    (I K C : Type*) [CommGroup I] [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K] where
  principal : Kˣ →* I
  classMap : I →* C
  ideleCharacter : I →* ℂˣ
  heckeCharacter : Chapter12HeckeCharacter C
  factorization : ideleCharacter = heckeCharacter.toHom.comp classMap
  principal_trivial : ideleCharacter.comp principal = 1

theorem chapter12_hecke_character_is_trivial_on_principal_ideles
    {I K C : Type*} [CommGroup I] [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Field K]
    (D : Chapter12HeckeCharacterPresentation I K C) (a : Kˣ) :
    D.ideleCharacter (D.principal a) = 1 := by
  have h := D.principal_trivial
  simpa [MonoidHom.comp_apply] using DFunLike.congr_fun h a

structure Chapter12LocalHeckeFactorization
    (V I C : Type*) [CommGroup I] [CommGroup C]
    [TopologicalSpace C] [IsTopologicalGroup C]
    (U : V → Type*) [∀ v, CommGroup (U v)] where
  ideleCharacter : I →* ℂˣ
  classMap : I →* C
  heckeCharacter : Chapter12HeckeCharacter C
  component : ∀ v, I →* U v
  localCharacter : ∀ v, U v →* ℂˣ
  finiteSupport : Set V
  finiteSupport_finite : finiteSupport.Finite
  outside_support_unramified :
    ∀ v, v ∉ finiteSupport → ∀ u, localCharacter v u = 1
  factorization :
    ∀ x, heckeCharacter.toHom (classMap x) =
      ∏ v ∈ finiteSupport_finite.toFinset,
        localCharacter v (component v x)

theorem chapter12_hecke_local_factor_product
    {V I C : Type*} [CommGroup I] [CommGroup C]
    [TopologicalSpace C] [IsTopologicalGroup C]
    {U : V → Type*} [∀ v, CommGroup (U v)]
    (D : Chapter12LocalHeckeFactorization V I C U) (x : I) :
    D.heckeCharacter.toHom (D.classMap x) =
      ∏ v ∈ D.finiteSupport_finite.toFinset,
        D.localCharacter v (D.component v x) := by
  exact D.factorization x

def chapter12UnramifiedLocalParameter
    {U : Type*} [CommGroup U] (χ : U →* ℂˣ)
    (_units : Subgroup U) (uniformizer : U) : ℂˣ :=
  χ uniformizer

theorem chapter12_unramified_parameter_independent_of_uniformizer
    {U : Type*} [CommGroup U] (χ : U →* ℂˣ)
    (units : Subgroup U) (π π' : U)
    (hχ : ∀ u, u ∈ units → χ u = 1)
    (hπ : π' * π⁻¹ ∈ units) :
    chapter12UnramifiedLocalParameter χ units π' =
      chapter12UnramifiedLocalParameter χ units π := by
  sorry

structure Chapter12UnramifiedFrobeniusValueData (G : Type*)
    [Group G] where
  localParameter : ℂˣ
  arithmeticFrobenius : G
  galoisCharacter : G →* ℂˣ
  arithmetic_formula : galoisCharacter arithmeticFrobenius = localParameter
  geometric_formula :
    galoisCharacter (chapter12GeometricFrobenius arithmeticFrobenius) =
      localParameter⁻¹

theorem chapter12_unramified_parameter_is_arithmetic_frobenius_value
    {G : Type*} [Group G]
    (D : Chapter12UnramifiedFrobeniusValueData G) :
    D.galoisCharacter D.arithmeticFrobenius = D.localParameter := by
  exact D.arithmetic_formula

theorem chapter12_book05_unramified_character_value_is_arithmetic_frobenius
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    chapter11CorrespondingAbelianGaloisCharacter R χ F.arithmeticFrobenius =
      χ D.uniformizer := by
  exact chapter11_unramified_character_sends_arithmetic_frobenius_to_parameter
    D R F χ hχ

theorem chapter12_finite_order_hecke_iff_finite_image_galois
    {C G : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Group G] [TopologicalSpace G]
    (D : Chapter12FiniteCharacterDictionary C G) :
    chapter12HeckeCharacterFiniteOrder D.heckeCharacter ↔
      Set.Finite (Set.range D.galoisCharacter.toHom) := by
  exact D.finite_order_iff_finite_image

theorem chapter12_book05_finite_image_character_dictionary
    {K G : Type*} [Field K] [Group G]
    [TopologicalSpace Kˣ] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (R : Chapter11ReciprocityData K G) :
    Nonempty
      ({ρ : G →ₜ* ℂˣ // chapter11FiniteImage ρ} ≃
        {χ : Kˣ →ₜ* ℂˣ // chapter11FiniteImage χ}) := by
  exact ⟨chapter11ComplexFiniteImageCharacterEquiv R⟩

theorem chapter12_finite_order_character_dictionary_is_a_bijection
    {C G : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Group G] [TopologicalSpace G]
    (D : Chapter12FiniteCharacterEquivalence C G) :
    Nonempty (chapter12FiniteHeckeCharacters C ≃
      chapter12FiniteGaloisCharacters G) := by
  exact ⟨D.correspondence⟩

theorem chapter12_finite_character_conductor_exponents_agree
    {V : Type*}
    (D : Chapter12LocalCharacterConductorData V) (v : V) :
    D.heckeExponent v = D.galoisExponent v := by
  exact D.exponent_eq v

theorem chapter12_book05_conductor_matches_reciprocity_filtration
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11GaloisRamificationFiltration (TopologicalAbelianization G))
    (χ : Kˣ →ₜ* A) (hχ : chapter11ConductorExists D χ)
    (hρ : ∃ n : ℕ, ∀ g ∈ F.group n,
      chapter11CorrespondingAbelianGaloisCharacter R χ g = 1)
    (hfiltration :
      ∀ n, F.group n = (D.unitFiltration n).map R.reciprocity.toMonoidHom) :
    chapter11Conductor D χ hχ =
      chapter11GaloisConductor F
        (chapter11CorrespondingAbelianGaloisCharacter R χ) hρ := by
  exact chapter11_conductor_matches_reciprocity_filtration D R F χ hχ hρ hfiltration

theorem chapter12_general_hecke_characters_have_a_module_direction
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12ModuleDirectionData C) :
    Function.Surjective D.module := by
  intro x
  refine ⟨D.positiveSection x, ?_⟩
  simpa [MonoidHom.comp_apply] using DFunLike.congr_fun D.section_right_inverse x

theorem chapter12_module_direction_can_be_non_finite_order
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12ModuleDirectionData C) :
    ∃ s : ℂ, ¬chapter12HeckeCharacterFiniteOrder
      { toHom := D.module_character s
        continuous := by sorry } := by
  exact D.module_character_is_not_finite_order

theorem chapter12_book05_nonfinite_unramified_parameter_is_not_a_galois_character
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) (α : ℂˣ)
    (hα : ¬ IsOfFinOrder α) :
    ¬ chapter11FiniteImage (chapter11ComplexUnramifiedQuasicharacter D α) := by
  sorry

structure Chapter12UnitaryModuleDecomposition
    (C : Type*) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] where
  character : Chapter12HeckeCharacter C
  unitaryPart : Chapter12HeckeCharacter C
  sigma : ℝ
  modulePower : C →* ℂˣ
  unitary : Prop
  decomposition : ∀ c,
    character.toHom c = unitaryPart.toHom c * modulePower c
  unique_sigma : Prop

theorem chapter12_hecke_character_module_decomposition
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12UnitaryModuleDecomposition C) :
    ∀ c, D.character.toHom c = D.unitaryPart.toHom c * D.modulePower c := by
  exact D.decomposition

structure Chapter12AlgebraicHeckeCharacter
    (C Sigma : Type*) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] extends Chapter12HeckeCharacter C where
  infinityType : Sigma → ℂ
  infinityType_integral : ∀ τ, ∃ n : ℤ, infinityType τ = (n : ℂ)
  archimedean_formula : Prop

theorem chapter12_algebraic_hecke_characters_have_integral_infinity_type
    {C Sigma : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (χ : Chapter12AlgebraicHeckeCharacter C Sigma)
    (τ : Sigma) : ∃ n : ℤ, χ.infinityType τ = (n : ℂ) := by
  exact χ.infinityType_integral τ

theorem chapter12_A0_purity_is_separate_from_algebraicity
    {Sigma : Type*} (I : Chapter12InfinityTypeData Sigma) (w : ℤ) :
    chapter12InfinityTypePure I w ↔
      ∀ τ, I.exponent τ + I.exponent (I.conjugation τ) = (w : ℂ) := by
  rfl

structure Chapter12AlgebraicUnitCompatibility (U Sigma : Type*)
    [CommGroup U] where
  infinityType : Sigma → ℤ
  finitePart : U → ℂˣ
  archimedeanValue : U → ℂˣ
  principal_relation : ∀ u, finitePart u * archimedeanValue u = 1
  deep_unit_relation : Prop

theorem chapter12_global_units_constrain_infinity_type
    {U Sigma : Type*} [CommGroup U]
    (D : Chapter12AlgebraicUnitCompatibility U Sigma) (u : U) :
    D.finitePart u * D.archimedeanValue u = 1 := by
  exact D.principal_relation u

theorem chapter12_ladic_avatar_is_locally_algebraic_and_unramified_away_from_finite_set
    {C G A Sigma : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Group G] [TopologicalSpace G] [Field A]
    (D : Chapter12LadicAvatarData C G A Sigma) :
    D.unramified_outside_finite_set ∧ D.locally_algebraic_above_l := by
  sorry

theorem chapter12_ladic_avatar_factors_through_global_artin
    {C G A Sigma : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Group G] [TopologicalSpace G] [Field A]
    (D : Chapter12LadicAvatarData C G A Sigma) :
    D.avatar.comp D.artin = D.correctedHeckeCharacter := by
  exact D.avatar_factorization

/- The converse direction is explicit in the condition record: it is the
locally algebraic, finitely ramified one-dimensional correspondence. -/
structure Chapter12AlgebraicLadicCorrespondence
    (C G A Sigma : Type*) [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Group G] [TopologicalSpace G] [Field A]
    [TopologicalSpace Aˣ] where
  unramifiedOutside : (G →* Aˣ) → Prop
  locallyAlgebraic : (G →* Aˣ) → Prop
  eligible : (G →* Aˣ) → Prop
  eligible_iff : ∀ ρ,
    eligible ρ ↔ Continuous ρ ∧ unramifiedOutside ρ ∧ locallyAlgebraic ρ
  fromHecke : Chapter12AlgebraicHeckeCharacter C Sigma → G →* Aˣ
  fromHecke_eligible : ∀ χ, eligible (fromHecke χ)
  toHecke : {ρ : G →* Aˣ // eligible ρ} →
    Chapter12AlgebraicHeckeCharacter C Sigma
  left_inverse : ∀ χ,
    toHecke ⟨fromHecke χ, fromHecke_eligible χ⟩ = χ
  right_inverse : ∀ ρ,
    (⟨fromHecke (toHecke ρ), fromHecke_eligible (toHecke ρ)⟩ :
      {ρ : G →* Aˣ // eligible ρ}) = ρ

theorem chapter12_algebraic_hecke_and_ladic_characters_correspond
    {C G A Sigma : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [Group G] [TopologicalSpace G] [Field A]
    [TopologicalSpace Aˣ]
    (D : Chapter12AlgebraicLadicCorrespondence C G A Sigma) :
    Nonempty (Chapter12AlgebraicHeckeCharacter C Sigma ≃
      {ρ : G →* Aˣ // D.eligible ρ}) := by
  let f : Chapter12AlgebraicHeckeCharacter C Sigma →
      {ρ : G →* Aˣ // D.eligible ρ} := fun χ =>
    ⟨D.fromHecke χ, D.fromHecke_eligible χ⟩
  let g : {ρ : G →* Aˣ // D.eligible ρ} →
      Chapter12AlgebraicHeckeCharacter C Sigma := D.toHecke
  exact ⟨
    { toFun := f
      invFun := g
      left_inv := D.left_inverse
      right_inv := D.right_inverse
      }⟩

structure Chapter12QuadraticFrobeniusSpecialization where
  splitValue : ℂ
  splitConjugateValue : ℂ
  splitPolynomial : Polynomial ℂ
  split_formula :
    splitPolynomial =
      (Polynomial.X - Polynomial.C splitValue) *
        (Polynomial.X - Polynomial.C splitConjugateValue)
  inertValue : ℂ
  inertTrace : ℂ
  inertPolynomial : Polynomial ℂ
  inert_trace_formula : inertTrace = 0
  inert_formula :
    inertPolynomial = Polynomial.X ^ 2 - Polynomial.C inertValue

theorem chapter12_quadratic_split_and_inert_frobenius_formulas
    (D : Chapter12QuadraticFrobeniusSpecialization) :
    D.splitPolynomial =
        (Polynomial.X - Polynomial.C D.splitValue) *
          (Polynomial.X - Polynomial.C D.splitConjugateValue) ∧
      D.inertTrace = 0 ∧
        D.inertPolynomial = Polynomial.X ^ 2 - Polynomial.C D.inertValue := by
  exact ⟨D.split_formula, D.inert_trace_formula, D.inert_formula⟩

structure Chapter12NormRestrictionCharacterSquare
    (C_K C_M G_K G_M : Type*)
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M] where
  norm : C_M →* C_K
  artinK : C_K →* G_K
  artinM : C_M →* G_M
  restriction : G_K →* G_M
  heckeK : C_K →* ℂˣ
  heckeM : C_M →* ℂˣ
  galoisK : G_K →* ℂˣ
  galoisM : G_M →* ℂˣ
  artin_square : artinM = (restriction.comp artinK).comp norm
  heckeK_factor : heckeK = galoisK.comp artinK
  heckeM_factor : heckeM = galoisM.comp artinM
  hecke_norm_pullback : heckeM = heckeK.comp norm
  galois_restriction : galoisK = galoisM.comp restriction

theorem chapter12_norm_pullback_matches_galois_restriction
    {C_K C_M G_K G_M : Type*}
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    (D : Chapter12NormRestrictionCharacterSquare C_K C_M G_K G_M) :
    D.heckeM = D.heckeK.comp D.norm ∧
      D.galoisK = D.galoisM.comp D.restriction := by
  exact ⟨D.hecke_norm_pullback, D.galois_restriction⟩

theorem chapter12_book05_restriction_of_galois_character_is_norm_pullback
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

theorem chapter12_book05_restriction_of_multiplicative_character_is_transfer
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

/-! The induction formulas are kept as one explicit compatibility record until
the Chapter 11 representation API is reconciled. -/

structure Chapter12InductionCompatibility
    (C_K C_M G_K G_M R V W : Type*)
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    [AddCommGroup R] [Fintype W] where
  norm : C_M →* C_K
  diagonal : C_K →* C_M
  transfer : G_K →* G_M
  theta : C_M →* ℂˣ
  eta : C_K →* ℂˣ
  induced : (C_M →* ℂˣ) → R
  twistedInduced : (C_M →* ℂˣ) → (C_K →* ℂˣ) → R
  tensorTwist : R → (C_K →* ℂˣ) → R
  thetaNormPullback : C_M →* ℂˣ
  thetaNormPullback_formula :
    thetaNormPullback = theta * (eta.comp norm)
  twist_formula : ∀ η : C_K →* ℂˣ,
    twistedInduced theta η = tensorTwist (induced theta) η
  determinant : R → C_K →* ℂˣ
  determinantSign : C_K →* ℂˣ
  determinant_formula :
    determinant (induced theta) =
      (determinantSign * (theta.comp diagonal))
  localConductorExponent : V → ℕ
  discriminantExponent : V → ℕ
  residueDegree : V → W → ℕ
  thetaConductorExponent : V → W → ℕ
  conductor_formula :
    ∀ v, localConductorExponent v =
      discriminantExponent v +
        ∑ w, residueDegree v w * thetaConductorExponent v w
  frobeniusPolynomial : (C_M →* ℂˣ) → V → Polynomial ℂ
  thetaFrobeniusValue : V → W → ℂ
  frobenius_cycle_formula :
    ∀ v, frobeniusPolynomial theta v =
      ∏ w, (Polynomial.X ^ (residueDegree v w) -
        Polynomial.C (thetaFrobeniusValue v w))
  induction_transitive : Prop
  norm_transitive : Prop

theorem chapter12_induction_determinant_uses_diagonal_transfer
    {C_K C_M G_K G_M R V W : Type*}
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    [AddCommGroup R] [Fintype W]
    (D : Chapter12InductionCompatibility C_K C_M G_K G_M R V W) :
    D.determinant (D.induced D.theta) =
      D.determinantSign * (D.theta.comp D.diagonal) := by
  exact D.determinant_formula

theorem chapter12_induction_twists_use_norm_pullback
    {C_K C_M G_K G_M R V W : Type*}
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    [AddCommGroup R] [Fintype W]
    (D : Chapter12InductionCompatibility C_K C_M G_K G_M R V W) :
    D.thetaNormPullback = D.theta * (D.eta.comp D.norm) ∧
      D.twistedInduced D.theta D.eta =
        D.tensorTwist (D.induced D.theta) D.eta := by
  exact ⟨D.thetaNormPullback_formula, D.twist_formula D.eta⟩

theorem chapter12_induction_conductor_adds_relative_discriminant
    {C_K C_M G_K G_M R V W : Type*}
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    [AddCommGroup R] [Fintype W]
    (D : Chapter12InductionCompatibility C_K C_M G_K G_M R V W) (v : V) :
    D.localConductorExponent v =
      D.discriminantExponent v +
        ∑ w, D.residueDegree v w * D.thetaConductorExponent v w := by
  exact D.conductor_formula v

theorem chapter12_induction_frobenius_polynomial_is_cycle_product
    {C_K C_M G_K G_M R V W : Type*}
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    [AddCommGroup R] [Fintype W]
    (D : Chapter12InductionCompatibility C_K C_M G_K G_M R V W) (v : V) :
    D.frobeniusPolynomial D.theta v =
      ∏ w, (Polynomial.X ^ (D.residueDegree v w) -
        Polynomial.C (D.thetaFrobeniusValue v w)) := by
  exact D.frobenius_cycle_formula v

theorem chapter12_induction_and_norms_are_transitive
    {C_K C_M G_K G_M R V W : Type*}
    [CommGroup C_K] [CommGroup C_M] [Group G_K] [Group G_M]
    [AddCommGroup R] [Fintype W]
    (D : Chapter12InductionCompatibility C_K C_M G_K G_M R V W) :
    D.induction_transitive ∧ D.norm_transitive := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter12
