import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section06FactorizationAndBaseChange

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

noncomputable section

/-! # Book 2, Chapter 7, §7.7: roots of unity prime to the residue characteristic -/

/-- `m` is invertible in the valuation ring. -/
def Chapter07OrderInvertibleIn
    (A : Type*) [CommRing A] (m : ℕ) : Prop :=
  IsUnit (m : A)

/-- A reduction homomorphism on units that respects `m`th roots of unity. -/
def chapter07RootsOfUnityReduction
    {K k : Type*} [CommMonoid K] [CommMonoid k]
    (m : ℕ) (ρ : Kˣ →* kˣ)
    (hρ : ∀ ζ : Kˣ, ζ ∈ rootsOfUnity m K → (ρ ζ) ^ m = 1) :
    rootsOfUnity m K →* rootsOfUnity m k where
  toFun ζ := ⟨ρ ζ, hρ ζ ζ.property⟩
  map_one' := by
    ext
    simp
  map_mul' ζ ξ := by
    ext
    simp

/-- The derivative of `T^m - 1` has the expected normalization factor. -/
theorem chapter07_derivative_power_minus_one
    {R : Type*} [CommRing R] (m : ℕ) :
    derivative (X ^ m - 1 : R[X]) = C (m : R) * X ^ (m - 1) := by
  sorry

/-- When `m` is a unit, every residue root is simple. -/
theorem chapter07_prime_to_residue_characteristic_roots_are_simple
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (m : ℕ) (hm : Chapter07OrderInvertibleIn A m)
    (ζ : k) (hζ : ζ ^ m = 1) :
    eval₂ (RingHom.id k) ζ (derivative (X ^ m - 1 : k[X])) ≠ 0 := by
  sorry

/-- Reduction gives a bijection between prime-to-characteristic roots in the
maximal unramified extension and in a separable residue closure. -/
theorem chapter07_roots_of_unity_reduction_bijective
    {Knr ksep : Type*} [Field Knr] [Field ksep]
    (m : ℕ) (ρ : Knrˣ →* ksepˣ)
    (hroot : ∀ ζ : Knrˣ, ζ ∈ rootsOfUnity m Knr → (ρ ζ) ^ m = 1)
    (hinjective : Function.Injective (chapter07RootsOfUnityReduction m ρ hroot))
    (hsurjective : Function.Surjective (chapter07RootsOfUnityReduction m ρ hroot)) :
    Function.Bijective (chapter07RootsOfUnityReduction m ρ hroot) := by
  exact ⟨hinjective, hsurjective⟩

/-- The root-lifting property for a chosen maximal unramified subextension of
a finite extension.  It is kept as a predicate because the subgroup `S` and
the reduction map depend on that chosen embedding. -/
def Chapter07FiniteExtensionResidueRootLifting
    {L l : Type*} [Field L] [Field l]
    (m : ℕ) (ρ : Lˣ →* lˣ) (S : Subgroup Lˣ)
    (hroot : ∀ ζ : Lˣ, ζ ∈ rootsOfUnity m L → (ρ ζ) ^ m = 1) : Prop :=
  ∀ ζ : rootsOfUnity m l,
      ∃! ξ : rootsOfUnity m L, (ξ : Lˣ) ∈ S ∧
        ρ ξ = ζ.1

/-- The exact-order compatibility assertion for the reduction map. -/
def Chapter07ReductionPreservesPrimitiveRootOrder
    {L l : Type*} [CommMonoid L] [CommMonoid l]
    (m : ℕ) (ρ : Lˣ →* lˣ)
    (hroot : ∀ ζ : Lˣ, ζ ∈ rootsOfUnity m L → (ρ ζ) ^ m = 1) : Prop :=
  ∀ ζ : rootsOfUnity m L, IsPrimitiveRoot (ζ : Lˣ) m →
    IsPrimitiveRoot (ρ ζ) m

/-- The numerical relation defining the multiplicative order of `q` modulo
`m`; it avoids silently assuming that the modulus is prime. -/
def Chapter07MultiplicativeOrderModulo
    (q m d : ℕ) : Prop :=
  m ∣ q ^ d - 1 ∧ ∀ n : ℕ, 0 < n → n < d → ¬m ∣ q ^ n - 1

/-- The residue degree of a primitive `m`th root is the least `d` satisfying
`m ∣ q^d - 1`. -/
theorem chapter07_primitive_root_unramified_degree
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [Fintype k]
    (q m d : ℕ) (hq : Fintype.card k = q)
    (horder : Chapter07MultiplicativeOrderModulo q m d)
    (hdegree : Module.finrank K L = d)
    (hresdegree : Module.finrank k l = d)
    (hsep : Chapter07ResidueExtensionIsSeparable k l)
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (he : E.ramificationIndex = 1)
    (hroot : ∃ ζ : L, IsPrimitiveRoot ζ m ∧
      Algebra.adjoin K ({ζ} : Set L) = ⊤)
    (hresroot : ∃ ζ : l, IsPrimitiveRoot ζ m) :
    Chapter07UnramifiedExtension E ∧ Module.finrank K L = d := by
  constructor
  · exact ⟨he, hsep⟩
  · exact hdegree

/-- The `p`-adic cyclotomic example: the degree is the order of `p` modulo
`m` when `m` is prime to `p`. -/
theorem chapter07_padic_prime_to_p_roots_of_unity
    {p m d : ℕ} [Fact p.Prime]
    (hcoprime : Nat.Coprime m p)
    (horder : Chapter07MultiplicativeOrderModulo p m d)
    (hminimal : ∀ n : ℕ, 0 < n → n < d → ¬m ∣ p ^ n - 1) :
    ∃ q : Chapter10FiniteExtensionProfile,
      q.degree = d ∧ q.ramificationIndex = 1 ∧ q.residueDegree = d ∧
        Chapter10Unramified q := by
  sorry

/-- In residue characteristic `p`, the derivative of `T^p - 1` has a
non-unit `p` factor; this is the boundary with wild ramification. -/
theorem chapter07_p_power_root_derivative_is_not_a_unit
    {A : Type*} [CommRing A] (p : ℕ)
    (hp : ¬Chapter07OrderInvertibleIn A p) :
    ¬IsUnit (p : A) := by
  exact hp

/-- Primitive roots of `p`-power order do not satisfy the prime-to-residue-
characteristic unramified lifting criterion. -/
theorem chapter07_p_power_roots_are_not_prime_to_characteristic_unramified
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l]
    (p r : ℕ) (E : Chapter07FiniteLocalExtensionData K L k l)
    (hprimitive : ∃ ζ : L, IsPrimitiveRoot ζ (p ^ r) ∧
      Algebra.adjoin K ({ζ} : Set L) = ⊤)
    (hinseparable : ¬Chapter07ResidueExtensionIsSeparable k l) :
    Chapter07FiercelyRamifiedExtension E ∨
      ¬Chapter07UnramifiedExtension E := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
