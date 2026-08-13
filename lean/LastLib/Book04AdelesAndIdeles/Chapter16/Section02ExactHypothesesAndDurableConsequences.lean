import LastLib.Book04AdelesAndIdeles.Chapter16.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter13.Section06SelfDualityAndTheDiagonalAnnihilator

namespace LastLib.Book04AdelesAndIdeles.Chapter16

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors NumberField RestrictedProduct Topology

/-!
## 16.2 Exact hypotheses and durable consequences

The hypotheses are kept explicit in every declaration.  In particular, the
compactness and finiteness statements below are number-field statements, not
formal consequences of the restricted-product notation alone.  The degree
target here is the continuous real direction of a number field; no function-
field degree or function-field compactness theorem is being imported.
-/

theorem chapter16_adele_and_idele_local_compactness
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter16AdeleRing K) ∧
      IsTopologicalRing (Chapter16AdeleRing K) ∧
      LocallyCompactSpace (Chapter16Ideles K) ∧
      IsTopologicalGroup (Chapter16Ideles K) := by
  sorry

theorem chapter16_diagonal_field_is_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Chapter16PrincipalAdeles K) := by
  sorry

theorem chapter16_diagonal_field_is_cocompact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter16AdditiveQuotient K)) := by
  sorry

theorem chapter16_diagonal_ideles_are_discrete
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (chapter16PrincipalIdeles K) := by
  sorry

theorem chapter16_product_formula_for_principal_ideles
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter16IdeleModule K (chapter16PrincipalIdeleHom K a) = 1 := by
  sorry

theorem chapter16_product_formula_places_principal_ideles_in_norm_one
    (K : Type*) [Field K] [NumberField K] :
    chapter16PrincipalIdeles K ≤ chapter16NormOneIdeles K := by
  sorry

theorem chapter16_module_and_degree_have_common_kernel
    (K : Type*) [Field K] [NumberField K] :
    chapter16NormOneIdeles K = chapter16DegreeZeroIdeles K := by
  sorry

theorem chapter16_module_descends_through_principal_ideles
    (K : Type*) [Field K] [NumberField K] :
    ∃ m : Chapter16IdeleClassGroup K →ₜ* Chapter16PositiveReals,
      ∀ x : Chapter16Ideles K,
        m ((QuotientGroup.mk' (chapter16PrincipalIdeles K)) x) =
          chapter16IdeleModule K x := by
  sorry

theorem chapter16_degree_descends_through_principal_ideles
    (K : Type*) [Field K] [NumberField K] :
    ∃ d : Chapter16IdeleClassGroup K →ₜ* Multiplicative ℝ,
      ∀ x : Chapter16Ideles K,
        (d ((QuotientGroup.mk' (chapter16PrincipalIdeles K)) x)).toAdd =
          chapter16IdeleDegree K x := by
  sorry

theorem chapter16_norm_one_class_group_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter16NormOneClassGroup K)) := by
  sorry

theorem chapter16_norm_one_class_group_is_maximal_compact
    (K : Type*) [Field K] [NumberField K] :
    ∀ H : Subgroup (Chapter16IdeleClassGroup K),
      IsCompact (H : Set (Chapter16IdeleClassGroup K)) →
        H ≤ chapter16NormOneClassSubgroup K := by
  sorry

theorem chapter16_idele_class_group_mod_norm_one_is_positive_reals
    (K : Type*) [Field K] [NumberField K] :
    ∃ e : (Chapter16IdeleClassGroup K ⧸ chapter16NormOneClassSubgroup K) ≃*
        Chapter16PositiveReals,
      ∀ x : Chapter16Ideles K,
        e ((QuotientGroup.mk' (chapter16NormOneClassSubgroup K))
          ((QuotientGroup.mk' (chapter16PrincipalIdeles K)) x)) =
          chapter16IdeleModule K x := by
  sorry

theorem chapter16_finite_idele_valuation_recovers_fractional_ideal
    (K : Type*) [Field K] [NumberField K] (x : Chapter16FiniteIdeles K) :
    ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v (chapter16FiniteIdeleFractionalIdeal K x) =
        chapter16FiniteIdeleValuationValue K x v := by
  sorry

theorem chapter16_finite_ideles_mod_principal_and_units_recover_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      ((Chapter16FiniteIdeles K ⧸ chapter16FiniteIdeleArithmeticSubgroup K) ≃*
        ClassGroup (𝓞 K)) := by
  sorry

theorem chapter16_ray_class_group_is_finite
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :
    Finite (Chapter16RayClassGroup K m) := by
  sorry

theorem chapter16_finite_idele_ray_quotient_recovers_ray_class_group
    (K : Type*) [Field K] [NumberField K] (m : Chapter16Modulus K) :
    Nonempty (Chapter16FiniteIdeleRayClassQuotient K m ≃*
      Chapter16RayClassGroup K m) := by
  sorry

theorem chapter16_extension_norms_exist_coordinatewise
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ∃ N : Chapter16ExtensionNormData K L,
      chapter16ExtensionNormCompatible N := by
  sorry

theorem chapter16_extension_norm_preserves_the_idele_module
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter16ExtensionNormData K L)
    (hN : chapter16ExtensionNormCompatible N) :
    ∀ x : Chapter16Ideles L,
      chapter16IdeleModule K (N.adeleNorm x) = chapter16IdeleModule L x := by
  sorry

theorem chapter16_extension_norm_respects_principal_ideles
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter16ExtensionNormData K L)
    (hN : chapter16ExtensionNormCompatible N) :
    (∀ a : Lˣ,
      N.adeleNorm (chapter16PrincipalIdeleHom L a) =
        chapter16PrincipalIdeleHom K (N.principalNorm a)) ∧
      (∀ a : Lˣ,
        N.finiteNorm (chapter16PrincipalFiniteIdeleHom L a) =
          chapter16PrincipalFiniteIdeleHom K (N.principalNorm a)) := by
  sorry

theorem chapter16_extension_norm_refines_ideal_norm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter16ExtensionNormData K L)
    (hN : chapter16ExtensionNormCompatible N) :
    ∀ x : Chapter16FiniteIdeles L,
      N.idealNorm (chapter16FiniteIdeleFractionalIdeal L x) =
        chapter16FiniteIdeleFractionalIdeal K (N.finiteNorm x) := by
  sorry

abbrev Chapter16IdeleClassCharacter (K : Type*) [Field K] [NumberField K] :=
  Chapter16IdeleClassGroup K →ₜ* ℂˣ

def chapter16CharacterIsUnitary
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter16IdeleClassCharacter K) : Prop :=
  ∀ x, ‖(χ x : ℂ)‖ = 1

def chapter16ComplexCharacterIsPositiveReal
    (K : Type*) [Field K] [NumberField K]
    (ρ : Chapter16IdeleClassCharacter K) : Prop :=
  ∀ x, 0 < (ρ x : ℂ).re ∧ (ρ x : ℂ).im = 0

def chapter16CharacterHasRealPowerModulus
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter16IdeleClassCharacter K) (d : Chapter16IdeleClassGroup K → ℝ) : Prop :=
  ∃ χᵤ : Chapter16IdeleClassCharacter K, ∃ ρ : Chapter16IdeleClassCharacter K,
    ∃ s : ℝ,
      chapter16CharacterIsUnitary K χᵤ ∧
        chapter16ComplexCharacterIsPositiveReal K ρ ∧
        (∀ x, ‖(ρ x : ℂ)‖ = Real.exp (s * d x)) ∧
        (∀ x, χ x = χᵤ x * ρ x)

theorem chapter16_finite_order_idele_class_characters_factor_through_ray_class_groups
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter16IdeleClassCharacter K)
    (hχ : ∃ n : ℕ, 0 < n ∧ ∀ x, χ x ^ n = 1) :
        ∃ m : Chapter16Modulus K,
        ∃ q : Chapter16IdeleClassGroup K →* Chapter16RayClassGroup K m,
          ∃ χₘ : Chapter16RayClassGroup K m →* ℂˣ,
            Function.Surjective q ∧
              ∀ x, χ x = χₘ (q x) := by
  sorry

theorem chapter16_general_idele_class_characters_split_into_unitary_and_real_parts
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter16IdeleClassCharacter K) :
    ∃ d : Chapter16IdeleClassGroup K → ℝ,
      (∀ x : Chapter16Ideles K,
        d ((QuotientGroup.mk' (chapter16PrincipalIdeles K)) x) =
          chapter16IdeleDegree K x) ∧
      (∀ x y, d (x * y) = d x + d y) ∧
        chapter16CharacterHasRealPowerModulus K χ d := by
  sorry

def chapter16TraceCharacterPairing
    (K : Type*) [Field K] [NumberField K]
    (ψ : AddChar (Chapter16AdeleRing K) Circle)
    (x y : Chapter16AdeleRing K) : Circle :=
  ψ (x * y)

theorem chapter16_standard_trace_character_is_self_dual
    (K : Type*) [Field K] [NumberField K]
    (D : LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13AdelicTraceData K)
    (S : LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13AdelicDualityData K D) :
    ∃ ψ : AddChar (Chapter16AdeleRing K) Circle,
      ψ = LastLib.Book04AdelesAndIdeles.Chapter13.chapter13StandardAdditiveCharacter K D ∧
        Continuous (ψ : Chapter16AdeleRing K → Circle) ∧
      chapter16AdditiveAnnihilator ψ (Chapter16PrincipalAdeles K) =
          (Chapter16PrincipalAdeles K : Set (Chapter16AdeleRing K)) ∧
        (∃ e : Chapter16AdeleRing K ≃+
            Additive (PontryaginDual (Multiplicative (Chapter16AdeleRing K))),
          ∀ x y : Chapter16AdeleRing K,
            ((e x : PontryaginDual (Multiplicative (Chapter16AdeleRing K)))
              (Multiplicative.ofAdd y)) =
              chapter16TraceCharacterPairing K ψ x y) ∧
        ∀ x y : Chapter16AdeleRing K, x ≠ y →
          ∃ z, chapter16TraceCharacterPairing K ψ (x - y) z ≠ 1 := by
  sorry

theorem chapter16_GL_n_is_a_restricted_product_with_compact_open_finite_levels
    (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n] :
    Nonempty
        (Chapter16GeneralLinearAdeles K n ≃
          Matrix.GeneralLinearGroup n (NumberField.InfiniteAdeleRing K) ×
            Chapter16FiniteGLnRestrictedProduct K n) ∧
      chapter16HasCompactOpenFiniteLevel (Chapter16GeneralLinearAdeles K n) := by
  sorry

theorem chapter16_GL_n_finite_levels_are_compact_open
    (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n] :
    ∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (chapter16FiniteGLnLevelSubgroup K n v : Set
        (Matrix.GeneralLinearGroup n (v.adicCompletion K))) ∧
        IsCompact (chapter16FiniteGLnLevelSubgroup K n v : Set
          (Matrix.GeneralLinearGroup n (v.adicCompletion K))) := by
  sorry

theorem chapter16_GL_n_has_the_restricted_product_presentation
    (K : Type*) [Field K] [NumberField K]
    (n : Type*) [DecidableEq n] [Fintype n] :
    Nonempty
      (Chapter16GeneralLinearAdeles K n ≃
        Matrix.GeneralLinearGroup n (NumberField.InfiniteAdeleRing K) ×
          Chapter16FiniteGLnRestrictedProduct K n) := by
  sorry

theorem chapter16_rank_one_recovers_idele_class_characters
    (K : Type*) [Field K] [NumberField K] :
    ∃ e : Matrix.GeneralLinearGroup (Fin 1) (Chapter16AdeleRing K) ≃*
        Chapter16Ideles K,
      ∀ χ : Chapter16IdeleClassCharacter K,
        ∃ χ₁ : Matrix.GeneralLinearGroup (Fin 1) (Chapter16AdeleRing K) →ₜ* ℂˣ,
          ∀ x, χ (QuotientGroup.mk' (chapter16PrincipalIdeles K) (e x)) = χ₁ x := by
  sorry

theorem chapter16_number_field_residue_fields_are_finite
    (K : Type*) [Field K] [NumberField K] :
    ∀ v : HeightOneSpectrum (𝓞 K), Finite ((𝓞 K) ⧸ v.asIdeal) := by
  sorry

theorem chapter16_adeles_split_into_archimedean_and_finite_parts
    (K : Type*) [Field K] [NumberField K] :
    Chapter16AdeleRing K =
      (NumberField.InfiniteAdeleRing K × Chapter16FiniteAdeleRing K) := by
  rfl

theorem chapter16_minkowski_bound_is_finite
    (K : Type*) [Field K] [NumberField K] :
    NumberField.mixedEmbedding.minkowskiBound K
        (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) < ⊤ := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter16
