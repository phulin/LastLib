import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section01AdelicCharactersAndLocalFactors

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.2. Finite-order characters and Galois characters -/

abbrev Chapter11AbsoluteGaloisFiniteCharacters
    (K : Type*) [Field K] [NumberField K] :=
  Chapter11FiniteImageCharacters (Chapter11AbsoluteGaloisAbelianization K)

theorem chapter11_absolute_galois_idele_class_finite_character_bijection
    (K : Type*) [Field K] [NumberField K]
    (R : Chapter11GlobalReciprocityData K
      (Chapter11AbsoluteGaloisAbelianization K)) :
    Nonempty (Chapter11AbsoluteGaloisFiniteCharacters K ≃
      Chapter11FiniteOrderHeckeCharacters K) := by
  exact chapter11_finite_character_reciprocity_bijection K
    (Chapter11AbsoluteGaloisAbelianization K) R

/- A finite reciprocity datum records the finite abelian extension used to
realize a particular open kernel.  The extension itself is supplied by the
global reciprocity construction from the preceding chapters. -/
structure Chapter11FiniteOrderRealizationFor
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K) where
  artin : Chapter11IdeleClass K →* Gal(L / K)
  surjective_artin : Function.Surjective artin
  kernel_eq : artin.ker = χ.toMonoidHom.ker

/- LOCAL_DEPENDENCY_GUESS: global reciprocity supplies an `L` and a datum of
this form for each finite-order character.  The factorization theorem below
is independent of how that extension is constructed. -/
theorem chapter11_finite_order_extension_exists
    {K : Type*} [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K)
    (hχ : chapter11FiniteOrder χ.toMonoidHom) :
    ∃ (L : Type*) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      Nonempty (Chapter11FiniteOrderRealizationFor K L χ) := by
  sorry

theorem chapter11_finite_order_galois_character_exists
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K)
    (R : Chapter11FiniteOrderRealizationFor K L χ) :
    ∃ χGal : Gal(L / K) →* ℂˣ,
      χGal.comp R.artin = χ.toMonoidHom := by
  sorry

noncomputable def chapter11GaloisCharacter
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K)
    (R : Chapter11FiniteOrderRealizationFor K L χ) : Gal(L / K) →* ℂˣ :=
  Classical.choose (chapter11_finite_order_galois_character_exists χ R)

theorem chapter11GaloisCharacter_spec
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K)
    (R : Chapter11FiniteOrderRealizationFor K L χ) :
    (chapter11GaloisCharacter χ R).comp R.artin = χ.toMonoidHom := by
  exact Classical.choose_spec (chapter11_finite_order_galois_character_exists χ R)

theorem chapter11GaloisCharacter_unique
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K)
    (R : Chapter11FiniteOrderRealizationFor K L χ)
    {ψ₁ ψ₂ : Gal(L / K) →* ℂˣ}
    (h₁ : ψ₁.comp R.artin = χ.toMonoidHom)
    (h₂ : ψ₂.comp R.artin = χ.toMonoidHom) :
    ψ₁ = ψ₂ := by
  sorry

theorem chapter11_finite_order_factors_through_galois
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K)
    (R : Chapter11FiniteOrderRealizationFor K L χ) :
    ∃ ψ : Gal(L / K) →* ℂˣ, ψ.comp R.artin = χ.toMonoidHom := by
  exact chapter11_finite_order_galois_character_exists χ R

theorem chapter11_galois_character_has_finite_image
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (χ : Chapter11HeckeCharacter K)
    (R : Chapter11FiniteOrderRealizationFor K L χ) :
    chapter11FiniteOrder (chapter11GaloisCharacter χ R) := by
  sorry

/-! A continuous complex character of a profinite group automatically has
finite image.  The hypotheses are stated in the topological form used by the
argument: compactness gives compact image and total disconnectedness rules
out an infinite connected subgroup of the circle. -/
theorem chapter11_continuous_profinite_complex_character_finite_image
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [T2Space G] [IsTopologicalGroup G] [TotallyDisconnectedSpace G]
    (χ : G →ₜ* ℂˣ) :
    chapter11FiniteImage χ := by
  sorry

theorem chapter11_finite_character_kernel_open_and_finite_index
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [T2Space G] [IsTopologicalGroup G] [TotallyDisconnectedSpace G]
    (χ : G →ₜ* ℂˣ) :
    IsOpen (χ.toMonoidHom.ker : Set G) ∧
      Finite (G ⧸ χ.toMonoidHom.ker) := by
  sorry

theorem chapter11_finite_order_hecke_kernel_finite_index
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K)
    (hχ : chapter11FiniteOrder χ.toMonoidHom) :
    Finite (Chapter11IdeleClass K ⧸ χ.toMonoidHom.ker) := by
  sorry

/-! ### Local reciprocity and conductors -/

structure Chapter11LocalArtinConductorData
    (K G : Type*) [Field K] [NumberField K] [Group G] where
  v : NumberField.FinitePlace K
  localReciprocity : (v.maximalIdeal.adicCompletion K)ˣ →* G
  inertiaFiltration : ℕ → Subgroup G
  artinConductor : (G →* ℂˣ) → ℕ
  upperFiltration_compatibility : ∀ n,
    Subgroup.map localReciprocity
        (LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration v n) =
      inertiaFiltration n

theorem chapter11_local_conductor_equals_artin_conductor
    {K G : Type*} [Field K] [NumberField K] [Group G]
    (D : Chapter11LocalArtinConductorData K G)
    (ψ : (D.v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ)
    (ρ : G →* ℂˣ)
    (hrec : ψ = ρ.comp D.localReciprocity)
    (hlevel : Set.Nonempty
      {n : ℕ | chapter11LocalCharacterTrivialAtLevel D.v ψ n}) :
    chapter11LocalConductorExponent D.v ψ = D.artinConductor ρ := by
  sorry

theorem chapter11_local_conductor_displayed_formula
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (ψ : (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ) :
    chapter11LocalConductorExponent v ψ =
      sInf {n : ℕ | chapter11LocalCharacterTrivialAtLevel v ψ n} :=
  rfl

/-! ### Arithmetic versus geometric Frobenius -/

structure Chapter11FrobeniusNormalizationData (G V : Type*) [Group G] [Group V] where
  arithmetic : G → V
  geometric : G → V
  geometric_is_inverse : ∀ g, geometric g = (arithmetic g)⁻¹

theorem chapter11_geometric_frobenius_character_value
    {G V : Type*} [Group G] [Group V]
    (D : Chapter11FrobeniusNormalizationData G V)
    (χ : V →* ℂˣ) (g : G) :
    χ (D.geometric g) = (χ (D.arithmetic g))⁻¹ := by
  rw [D.geometric_is_inverse, map_inv]

/- SOURCE_ISSUE: Section 11.5 later writes a complex-valued finite factor
through an embedding `ι : overline{ℚ} → overline{ℚ}_ℓ` without first making
the finite values algebraic or choosing the induced local completion maps.
The ell-adic section records those choices explicitly. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
