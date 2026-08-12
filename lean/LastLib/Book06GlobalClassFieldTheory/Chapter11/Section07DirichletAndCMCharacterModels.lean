import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section06NormsRestrictionAndConjugation

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.7. Dirichlet and CM character models -/

abbrev Chapter11DirichletCharacter (m : ℕ) := (ZMod m)ˣ →* ℂˣ

structure Chapter11RationalRayReciprocityData (m : ℕ) where
  rayQuotient : Chapter11IdeleClass ℚ →* (ZMod m)ˣ
  pullback : Chapter11DirichletCharacter m → Chapter11HeckeCharacter ℚ
  pullback_factorization : ∀ ψ,
    (ψ.comp rayQuotient) = (pullback ψ).toMonoidHom
  pullback_finite_order : ∀ ψ,
    chapter11FiniteOrder (pullback ψ).toMonoidHom

def chapter11RationalCharactersOfModulus
    (m : ℕ) (Q : Chapter11RationalRayReciprocityData m) : Type :=
  {χ : Chapter11HeckeCharacter ℚ //
    chapter11FiniteOrder χ.toMonoidHom ∧
      ∃ ψ : Chapter11DirichletCharacter m,
        ψ.comp Q.rayQuotient = χ.toMonoidHom}

theorem chapter11_rational_finite_order_hecke_characters_dirichlet
    (m : ℕ) (Q : Chapter11RationalRayReciprocityData m)
    (hcomplete : ∀ χ : Chapter11HeckeCharacter ℚ,
      chapter11FiniteOrder χ.toMonoidHom →
        (∃ ψ : Chapter11DirichletCharacter m,
          ψ.comp Q.rayQuotient = χ.toMonoidHom)) :
    Nonempty (chapter11RationalCharactersOfModulus m Q ≃
      Chapter11DirichletCharacter m) := by
  sorry

structure Chapter11RationalPrimeValueData (m : ℕ) where
  ψ : Chapter11DirichletCharacter m
  primeIndex : Type*
  prime : primeIndex → ℕ
  prime_is_prime : ∀ p, (prime p).Prime
  prime_coprime_to_modulus : ∀ p, Nat.Coprime (prime p) m
  primeValue : primeIndex → ℂˣ
  arithmeticFrobeniusValue : primeIndex → ℂˣ
  residueOfPrime : primeIndex → (ZMod m)ˣ
  prime_value : ∀ p, primeValue p = ψ (residueOfPrime p)
  arithmetic_frobenius_value : ∀ p,
    arithmeticFrobeniusValue p = ψ (residueOfPrime p)
  realLocalValue : ℂˣ
  real_sign_relation : realLocalValue = ψ (-1 : (ZMod m)ˣ)

theorem chapter11_dirichlet_prime_local_value
    (m : ℕ) (D : Chapter11RationalPrimeValueData m) (p : D.primeIndex) :
    D.primeValue p = D.ψ (D.residueOfPrime p) := by
  exact D.prime_value p

theorem chapter11_dirichlet_arithmetic_frobenius_value
    (m : ℕ) (D : Chapter11RationalPrimeValueData m) (p : D.primeIndex) :
    D.arithmeticFrobeniusValue p = D.ψ (D.residueOfPrime p) := by
  exact D.arithmetic_frobenius_value p

theorem chapter11_dirichlet_real_sign_relation
    (m : ℕ) (D : Chapter11RationalPrimeValueData m) :
    D.realLocalValue = D.ψ (-1 : (ZMod m)ˣ) := by
  exact D.real_sign_relation

def chapter11DirichletFactorsThrough
    {m : ℕ} (d : ℕ) (ψ : Chapter11DirichletCharacter m) : Prop :=
  ∃ _h : d ∣ m, ∃ q : (ZMod m)ˣ →* (ZMod d)ˣ,
    ∃ θ : Chapter11DirichletCharacter d, θ.comp q = ψ

def chapter11DirichletConductor (m : ℕ) (ψ : Chapter11DirichletCharacter m) : ℕ :=
  sInf {d : ℕ | d ∣ m ∧ chapter11DirichletFactorsThrough d ψ}

def chapter11DirichletPrimitive
    (m : ℕ) (ψ : Chapter11DirichletCharacter m) : Prop :=
  ∀ d, d ∣ m → d < m → ¬chapter11DirichletFactorsThrough d ψ

theorem chapter11_dirichlet_primitivity_iff_minimal_conductor
    (m : ℕ) (ψ : Chapter11DirichletCharacter m)
    (hconductor : chapter11DirichletConductor m ψ = m) :
    chapter11DirichletPrimitive m ψ := by
  sorry

theorem chapter11_minimal_dirichlet_conductor_iff_primitivity
    (m : ℕ) (ψ : Chapter11DirichletCharacter m)
    (hprimitive : chapter11DirichletPrimitive m ψ) :
    chapter11DirichletConductor m ψ = m := by
  sorry

structure Chapter11CyclotomicGaloisFactorizationData
    (m : ℕ) (G : Type*) [Group G] where
  character : G →* ℂˣ
  cyclotomicQuotient : G →* (ZMod m)ˣ
  dirichletCharacter : (ZMod m)ˣ →* ℂˣ
  factorization : character = dirichletCharacter.comp cyclotomicQuotient
  arithmeticFrobenius : G
  frobenius_value : character arithmeticFrobenius =
    dirichletCharacter (cyclotomicQuotient arithmeticFrobenius)

theorem chapter11_dirichlet_galois_character_factors_through_cyclotomic
    {m : ℕ} {G : Type*} [Group G]
    (D : Chapter11CyclotomicGaloisFactorizationData m G) :
    D.character = D.dirichletCharacter.comp D.cyclotomicQuotient :=
  D.factorization

structure Chapter11ImaginaryQuadraticData
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M]
    [Algebra.IsQuadraticExtension ℚ M] where
  conjugation : M →+* M
  conjugation_sq : conjugation.comp conjugation = RingHom.id M
  units_finite : Set.Finite (Set.univ : Set ((𝓞 M)ˣ))
  imaginary : ∀ τ : M →+* ℂ, ¬ComplexEmbedding.IsReal τ

structure Chapter11CMRayIdealCharacterData
    (M I : Type*) [Field M] [NumberField M] [CommGroup I]
    [Algebra ℚ M] where
  p : ℤ
  q : ℤ
  modulus : Ideal (𝓞 M)
  complexEmbedding : M →+* ℂ
  rayUnits : Subgroup Mˣ
  rayIdealSubgroup : Subgroup I
  principalIdeal : Mˣ → rayIdealSubgroup
  idealCharacter : rayIdealSubgroup →* ℂˣ
  conjugation : M →+* M
  principal_formula : ∀ a : rayUnits,
    idealCharacter (principalIdeal a) =
      Units.mk0 (((complexEmbedding ((a : Mˣ) : M)) ^ p) *
        ((complexEmbedding (conjugation ((a : Mˣ) : M))) ^ q)) (by sorry)
  unit_obstruction : ∀ u : rayUnits,
    Units.mk0 (((complexEmbedding ((u : Mˣ) : M)) ^ p) *
      ((complexEmbedding (conjugation ((u : Mˣ) : M))) ^ q)) (by sorry) = 1

theorem chapter11_cm_ray_character_principal_formula
    {M I : Type*} [Field M] [NumberField M] [CommGroup I]
    [Algebra ℚ M]
    (D : Chapter11CMRayIdealCharacterData M I) (a : D.rayUnits) :
    D.idealCharacter (D.principalIdeal a) =
      Units.mk0 (((D.complexEmbedding ((a : Mˣ) : M)) ^ D.p) *
        ((D.complexEmbedding (D.conjugation ((a : Mˣ) : M))) ^ D.q)) (by sorry) := by
  exact D.principal_formula a

theorem chapter11_cm_unit_obstruction_removed_by_enlarging_modulus
    {M I : Type*} [Field M] [NumberField M] [CommGroup I]
    [Algebra ℚ M] [Algebra.IsQuadraticExtension ℚ M]
    (Q : Chapter11ImaginaryQuadraticData M)
    (D : Chapter11CMRayIdealCharacterData M I)
    (hfinite : Set.Finite (Set.univ : Set ((𝓞 M)ˣ))) :
    ∃ f' : Ideal (𝓞 M), D.modulus ≤ f' ∧
      ∃ U : Subgroup Mˣ, ∀ u : U,
        Units.mk0 (((D.complexEmbedding ((u : Mˣ) : M)) ^ D.p) *
          ((D.complexEmbedding (D.conjugation ((u : Mˣ) : M))) ^ D.q)) (by sorry) = 1 := by
  sorry

theorem chapter11_character_extends_from_finite_abelian_subgroup
    {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) (θ : H →* ℂˣ) :
    ∃ Θ : G →* ℂˣ, Θ.comp H.subtype = θ := by
  sorry

theorem chapter11_cm_ray_character_extends_to_all_ray_ideals
    {M I : Type*} [Field M] [NumberField M] [CommGroup I]
    [Algebra ℚ M]
    (D : Chapter11CMRayIdealCharacterData M I)
    [Finite I] :
    ∃ Θ : I →* ℂˣ,
      Θ.comp D.rayIdealSubgroup.subtype = D.idealCharacter := by
  sorry

theorem chapter11_cm_ray_character_gives_algebraic_infinity_type
    {M I : Type*} [Field M] [NumberField M] [CommGroup I]
    [Algebra ℚ M]
    (D : Chapter11CMRayIdealCharacterData M I) :
    ∀ a : D.rayUnits,
      D.idealCharacter (D.principalIdeal a) =
        Units.mk0 (((D.complexEmbedding ((a : Mˣ) : M)) ^ D.p) *
          ((D.complexEmbedding (D.conjugation ((a : Mˣ) : M))) ^ D.q)) (by sorry) := by
  exact fun a => D.principal_formula a

structure Chapter11CMConjugationData where
  p : ℤ
  q : ℤ
  character : ℂˣ →* ℂˣ
  conjugateCharacter : ℂˣ →* ℂˣ
  infinity_formula : ∀ z : ℂˣ,
    character z = Units.mk0 (((z : ℂ) ^ p) *
      ((starRingEnd ℂ) (z : ℂ) ^ q)) (by sorry)
  conjugate_infinity_formula : ∀ z : ℂˣ,
    conjugateCharacter z = Units.mk0 ((((starRingEnd ℂ) (z : ℂ)) ^ p) *
      ((z : ℂ) ^ q)) (by sorry)
  type_separating_point : ∃ z : ℂˣ,
    Units.mk0 (((z : ℂ) ^ p) * ((starRingEnd ℂ) (z : ℂ) ^ q)) (by sorry) ≠
      Units.mk0 ((((starRingEnd ℂ) (z : ℂ)) ^ p) * ((z : ℂ) ^ q)) (by sorry)

theorem chapter11_cm_nonparallel_type_changes_under_conjugation
    (D : Chapter11CMConjugationData) (hpq : D.p ≠ D.q) :
    D.character ≠ D.conjugateCharacter := by
  sorry

/- The p != q and conjugation-invariant p = q dichotomy is used by the
quadratic induction interface in the next section, where the relevant Galois
action and extension choices are typed explicitly. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
