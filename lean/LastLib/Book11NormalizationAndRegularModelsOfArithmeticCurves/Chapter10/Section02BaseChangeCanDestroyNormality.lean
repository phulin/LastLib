import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10.Section01IntegralClosureOfTheBase

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

/-! ## 10.2 Base change can destroy normality -/

def chapter10PthPowers (k : Type u) [CommRing k] (p : ℕ) : Set k :=
  {a | ∃ b : k, b ^ p = a}

def chapter10PurelyInseparablePolynomial (k : Type u) [CommRing k]
    (p : ℕ) (a : k) : Polynomial k :=
  Polynomial.X ^ p - Polynomial.C a

def chapter10PurelyInseparableQuotient (k : Type u) [CommRing k]
    (p : ℕ) (a : k) : Type u :=
  Polynomial k ⧸ Ideal.span ({chapter10PurelyInseparablePolynomial k p a} : Set (Polynomial k))

def chapter10RepeatedRootPolynomial (k' : Type u) [CommRing k']
    (p : ℕ) (α : k') : Polynomial k' :=
  (Polynomial.X - Polynomial.C α) ^ p

def chapter10RepeatedRootQuotient (k' : Type u) [CommRing k']
    (p : ℕ) (α : k') : Type u :=
  Polynomial k' ⧸ Ideal.span ({chapter10RepeatedRootPolynomial k' p α} : Set (Polynomial k'))

def chapter10PurelyInseparableBaseChangeAlgebra
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (p : ℕ) (a : k) : Type u :=
  k' ⊗[k] chapter10PurelyInseparableQuotient k p a

structure Chapter10PthRootFieldExtension (k : Type u) [Field k] (p : ℕ)
    [CharP k p] where
  prime : Nat.Prime p
  a : k
  not_pth_power : a ∉ chapter10PthPowers k p
  k' : Type u
  [fieldK' : Field k']
  [algebraK' : Algebra k k']
  α : k'
  root_equation : algebraMap k k' a = α ^ p

theorem chapter10_purely_inseparable_root_extension_exists
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : Nat.Prime p)
    (a : k) (ha : a ∉ chapter10PthPowers k p) :
    Nonempty (Chapter10PthRootFieldExtension k p) := by
  sorry

def Chapter10NormalZeroDimensionalRing (A : Type u) [CommRing A] : Prop :=
  IsDomain A ∧ IsIntegrallyClosed A ∧
    ∀ p : PrimeSpectrum A, p.asIdeal = ⊥

theorem chapter10_purely_inseparable_quotient_is_normal_zero_dimensional
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : Nat.Prime p)
    (a : k) (ha : a ∉ chapter10PthPowers k p) :
    Chapter10NormalZeroDimensionalRing (chapter10PurelyInseparableQuotient k p a) := by
  sorry

theorem chapter10_purely_inseparable_quotient_is_field
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : Nat.Prime p)
    (a : k) (ha : a ∉ chapter10PthPowers k p) :
    Field (chapter10PurelyInseparableQuotient k p a) := by
  sorry

theorem chapter10_purely_inseparable_quotient_is_integrally_closed
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : Nat.Prime p)
    (a : k) (ha : a ∉ chapter10PthPowers k p) :
    IsIntegrallyClosed (chapter10PurelyInseparableQuotient k p a) := by
  exact (chapter10_purely_inseparable_quotient_is_normal_zero_dimensional k p hp a ha).2.1

theorem chapter10_purely_inseparable_quotient_is_normal_scheme
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : Nat.Prime p)
    (a : k) (ha : a ∉ chapter10PthPowers k p) :
    Chapter10NormalScheme
      (Spec (CommRingCat.of (chapter10PurelyInseparableQuotient k p a))) := by
  sorry

def chapter10PurelyInseparableScheme (k : Type u) [Field k]
    (p : ℕ) (a : k) : Scheme.{u} :=
  Spec (CommRingCat.of (chapter10PurelyInseparableQuotient k p a))

def chapter10RepeatedRootScheme (k' : Type u) [Field k']
    (p : ℕ) (α : k') : Scheme.{u} :=
  Spec (CommRingCat.of (chapter10RepeatedRootQuotient k' p α))

structure Chapter10PurelyInseparableBaseChangeIdentification
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (p : ℕ) (a : k) (α : k') where
  ringEquiv :
    chapter10PurelyInseparableBaseChangeAlgebra k k' p a ≃+*
      chapter10RepeatedRootQuotient k' p α
  baseChanged_not_reduced :
    ¬ IsReduced (chapter10PurelyInseparableBaseChangeAlgebra k k' p a)
  repeatedRoot_not_reduced :
    ¬ IsReduced (chapter10RepeatedRootQuotient k' p α)
  repeatedRoot_not_normal :
    ¬ IsIntegrallyClosed (chapter10RepeatedRootQuotient k' p α)

theorem chapter10_purely_inseparable_base_change_is_repeated_root
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (p : ℕ) [CharP k p] [CharP k' p] (hp : Nat.Prime p)
    (a : k) (α : k') (hα : algebraMap k k' a = α ^ p)
    (ha : a ∉ chapter10PthPowers k p) :
    Nonempty (Chapter10PurelyInseparableBaseChangeIdentification k k' p a α) := by
  sorry

theorem chapter10_repeated_root_quotient_is_not_reduced
    (k' : Type u) [Field k'] (p : ℕ) [CharP k' p]
    (α : k') (hp : Nat.Prime p) :
    ¬ IsReduced (chapter10RepeatedRootQuotient k' p α) := by
  sorry

theorem chapter10_repeated_root_quotient_is_not_regular
    (k' : Type u) [Field k'] (p : ℕ) [CharP k' p]
    (α : k') (hp : Nat.Prime p) :
    ¬ IsRegularRing (chapter10RepeatedRootQuotient k' p α) := by
  sorry

theorem chapter10_normality_not_stable_under_arbitrary_field_extension :
    ∃ (k K A : Type u) (hk : Field k) (hK : Field K) (hKAlg : Algebra k K)
      (hA : CommRing A) (hAAlg : Algebra k A),
      Nonempty (@Chapter02NormalityFieldExtensionCounterexample
        k K A hk hK hKAlg hA hAAlg) := by
  exact chapter02_normality_not_stable_under_arbitrary_field_extension

def Chapter10GeometricallyRegularOverFiniteExtensions
    {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    FiniteDimensional k K →
      Chapter10RegularScheme (chapter10FieldBaseChange f (K := K))

theorem chapter10_smooth_iff_geometricallyRegular_finiteType
    {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k))
    (hfinite : Chapter01FiniteType f) :
    Smooth f ↔ Chapter10GeometricallyRegularOverFiniteExtensions f := by
  sorry

theorem chapter10_normalization_commutes_with_smooth_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (hg : Smooth g) :
    IsIso (chapter02NormalizationPullbackComparison f g) := by
  letI : Smooth g := hg
  exact chapter02_normalization_pullback_isIso f g

theorem chapter10_normalization_commutes_with_etale_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (hg : Etale g) :
    IsIso (chapter02NormalizationPullbackComparison f g) := by
  sorry

theorem chapter10_smooth_ring_base_change_preserves_integral_closure
    {R S B : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing B] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) := by
  exact TensorProduct.toIntegralClosure_bijective_of_smooth

end
end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter10
