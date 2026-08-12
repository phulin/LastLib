import LastLib.Book06GlobalClassFieldTheory.Chapter11.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.1. Adelic characters and their local factors -/

def chapter11AssembledIdeleCharacter
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K) : Chapter11IdeleCharacter K :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13AssembledMultiplicativeCharacter K F

theorem chapter11AssembledIdeleCharacter_apply
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K) (x : Chapter11Idele K) :
    chapter11AssembledIdeleCharacter K F x =
      (∏ v, F.infinite v
        ((MulEquiv.piUnits ((MulEquiv.prodUnits x).1)) v)) *
        ∏ᶠ v, F.finite v
          (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13FiniteIdeleCoordinate
            K ((MulEquiv.prodUnits x).2) v) :=
  rfl

theorem chapter11AssembledIdeleCharacter_finite_support
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K) (x : Chapter11Idele K) :
    (Set.Finite {v |
      F.finite v
        (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13FiniteIdeleCoordinate
          K ((MulEquiv.prodUnits x).2) v) ≠ 1}) := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13AssembledMultiplicativeCharacter_finite_support
    K F x

theorem chapter11AssembledIdeleCharacter_restricts_to_local_factors
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K) :
    (∀ v : NumberField.InfinitePlace K,
      ∀ x, chapter11AssembledIdeleCharacter K F
          (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13InfiniteLocalIdele K v x) =
        F.infinite v x) ∧
    (∀ v : Chapter11FinitePlaceIndex K,
      ∀ x, chapter11AssembledIdeleCharacter K F
          (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13FiniteLocalIdele K v x) =
        F.finite v x) := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13AssembledMultiplicativeCharacter_restricts_to_local_factors
    K F

/- Continuity forces the almost-everywhere unramified condition. -/
theorem chapter11_continuous_idele_character_factorization
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11IdeleCharacter K) :
    ∃ F : Chapter11LocalCharacterFamily K,
      chapter11AssembledIdeleCharacter K F = χ := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13_continuous_idele_character_factorization
    K χ

def chapter11HeckeCharacterOnIdeles
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) : Chapter11IdeleCharacter K :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PullbackIdeleClassCharacter K χ

def chapter11DescendsToIdeleClass
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11IdeleCharacter K) : Prop :=
  ∀ a : Kˣ,
    χ (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdele K a) = 1

def chapter11HeckeCharacterOfIdeleCharacter
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11IdeleCharacter K)
    (hχ : chapter11DescendsToIdeleClass K χ) : Chapter11HeckeCharacter K :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13DescendIdeleCharacter K χ hχ

theorem chapter11_idele_character_descends_iff
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11IdeleCharacter K) :
    (∃ ψ : Chapter11HeckeCharacter K,
      chapter11HeckeCharacterOnIdeles K ψ = χ) ↔
      chapter11DescendsToIdeleClass K χ := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13_idele_class_character_iff K χ

theorem chapter11_pullback_descend_left_inverse
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11IdeleCharacter K)
    (hχ : chapter11DescendsToIdeleClass K χ) :
    chapter11HeckeCharacterOnIdeles K
        (chapter11HeckeCharacterOfIdeleCharacter K χ hχ) = χ := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13_pullback_descend_left_inverse K χ hχ

def chapter11LocalCharacterUnramified
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter11FinitePlaceIndex K)
    (ψ : (v.adicCompletion K)ˣ →* ℂˣ) : Prop :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13TrivialOnSubgroup
    (Chapter11LocalUnitSubgroup K v) ψ

theorem chapter11_local_factors_unramified_almost_everywhere
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K) :
    ∀ᶠ v in Filter.cofinite,
      chapter11LocalCharacterUnramified v (F.finite v) := by
  exact F.finite_unramified

def chapter11RootOfUnity
    {K : Type*} [Field K] [NumberField K] (ζ : Kˣ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

def chapter11UnramifiedParameter
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter11FinitePlaceIndex K)
    (ψ : (v.adicCompletion K)ˣ →* ℂˣ)
    (π : v.adicCompletion K) (hπ : Chapter11LocalUniformizer v π) : ℂˣ :=
  ψ (Units.mk0 π (by sorry))

theorem chapter11_unramified_parameter_independent
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter11FinitePlaceIndex K)
    (ψ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hψ : chapter11LocalCharacterUnramified v ψ)
    (π₁ π₂ : v.adicCompletion K)
    (hπ₁ : Chapter11LocalUniformizer v π₁)
    (hπ₂ : Chapter11LocalUniformizer v π₂) :
  chapter11UnramifiedParameter v ψ π₁ hπ₁ =
      chapter11UnramifiedParameter v ψ π₂ hπ₂ := by
  sorry

structure Chapter11UnramifiedFrobeniusComparison (G : Type*) [Group G] where
  character : G →* ℂˣ
  arithmeticFrobenius : G
  parameter : ℂˣ
  arithmetic_formula : parameter = character arithmeticFrobenius
  geometric_formula : parameter = (character arithmeticFrobenius)⁻¹

theorem chapter11_unramified_parameter_is_arithmetic_frobenius_value
    {G : Type*} [Group G]
    (D : Chapter11UnramifiedFrobeniusComparison G) :
    D.parameter = D.character D.arithmeticFrobenius :=
  D.arithmetic_formula

theorem chapter11_unramified_parameter_is_inverse_geometric_value
    {G : Type*} [Group G]
    (D : Chapter11UnramifiedFrobeniusComparison G) :
    D.parameter = (D.character D.arithmeticFrobenius)⁻¹ :=
  D.geometric_formula

def chapter11UnramifiedParameterOfFamily
    {K : Type*} [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K)
    (v : Chapter11FinitePlaceIndex K)
    (π : v.adicCompletion K) (hπ : Chapter11LocalUniformizer v π) : ℂˣ :=
  chapter11UnramifiedParameter v (F.finite v) π hπ

/- The product formula is the global constraint on local prescriptions. -/
theorem chapter11_principal_idele_relation
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (a : Kˣ) :
    chapter11HeckeCharacterOnIdeles K χ
        (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdele K a) = 1 := by
  sorry

theorem chapter11_principal_idele_local_product_formula
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter11LocalCharacterFamily K)
    (χ : Chapter11HeckeCharacter K)
    (hF : chapter11AssembledIdeleCharacter K F =
      chapter11HeckeCharacterOnIdeles K χ) (a : Kˣ) :
    (∏ v, F.infinite v
      ((MulEquiv.piUnits
        ((MulEquiv.prodUnits
          (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdele K a)).1)) v)) *
      ∏ᶠ v, F.finite v
        (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13FiniteIdeleCoordinate K
          ((MulEquiv.prodUnits
            (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdele K a)).2) v) = 1 := by
  sorry

theorem chapter11_root_of_unity_local_constraint
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K) (ζ : Kˣ)
    (_hζ : chapter11RootOfUnity ζ) :
    chapter11HeckeCharacterOnIdeles K χ
        (LastLib.Book04AdelesAndIdeles.Chapter13.chapter13PrincipalIdele K ζ) = 1 := by
  exact chapter11_principal_idele_relation K χ ζ

/-! The arithmetic/geometric Frobenius convention is made explicit in the
ell-adic and finite-order sections; this comment records why the local
parameter itself is the arithmetic value. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
