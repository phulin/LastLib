import Mathlib.RingTheory.Localization.AtPrime.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Section03NormalCurvesAndRegularModels

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ## 3.4. Where the dictionaries fail -/

/-- The affine nodal equation `xy = 0`. -/
def chapter03NodeRelation (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))

/-- The nodal affine ring `k[x,y]/(xy)`. -/
abbrev Chapter03NodeRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ chapter03NodeRelation k

def chapter03NodeQuotientMap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* Chapter03NodeRing k :=
  Ideal.Quotient.mk (chapter03NodeRelation k)

def chapter03NodeIdeal (k : Type u) [CommRing k] : Ideal (Chapter03NodeRing k) :=
  (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))).map (chapter03NodeQuotientMap k)

def chapter03NodeComponentX (k : Type u) [CommRing k] : Ideal (Chapter03NodeRing k) :=
  (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 2) k))).map
    (chapter03NodeQuotientMap k)

def chapter03NodeComponentY (k : Type u) [CommRing k] : Ideal (Chapter03NodeRing k) :=
  (Ideal.span ({MvPolynomial.X 1} : Set (MvPolynomial (Fin 2) k))).map
    (chapter03NodeQuotientMap k)

def Chapter03NodeComponentCodimensionZero
    {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  I.IsPrime ∧ ∀ J : Ideal R, J.IsPrime → J ≤ I → J = I

theorem chapter03_node_ideal_isMaximal (k : Type u) [Field k] :
    (chapter03NodeIdeal k).IsMaximal := by
  sorry

theorem chapter03_node_ideal_isPrime (k : Type u) [Field k] :
    (chapter03NodeIdeal k).IsPrime := by
  sorry

instance chapter03NodeIdeal_isPrime_instance (k : Type u) [Field k] :
    (chapter03NodeIdeal k).IsPrime :=
  chapter03_node_ideal_isPrime k

theorem chapter03_node_componentX_is_codimensionZero (k : Type u) [Field k] :
    Chapter03NodeComponentCodimensionZero (chapter03NodeComponentX k) := by
  sorry

theorem chapter03_node_componentY_is_codimensionZero (k : Type u) [Field k] :
    Chapter03NodeComponentCodimensionZero (chapter03NodeComponentY k) := by
  sorry

def chapter03NodePoint (k : Type u) [Field k] : PrimeSpectrum (Chapter03NodeRing k) :=
  ⟨chapter03NodeIdeal k, chapter03_node_ideal_isPrime k⟩

theorem chapter03_node_point_is_codimensionOne (k : Type u) [Field k] :
    Order.coheight (chapter03NodePoint k) = 1 := by
  sorry

theorem chapter03_node_ring_not_a_domain (k : Type u) [Field k] :
    ¬ IsDomain (Chapter03NodeRing k) := by
  sorry

abbrev Chapter03NodeLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (chapter03NodeIdeal k)

theorem chapter03_node_localRing_not_a_domain (k : Type u) [Field k] :
    ¬ IsDomain (Chapter03NodeLocalRing k) := by
  sorry

/- The node has codimension-one point data but fails the integral-domain
  hypothesis required by the normal-integral order-of-vanishing API. -/
theorem chapter03_node_normal_integral_divisor_dictionary_unavailable
    (k : Type u) [Field k] :
    ¬ IsDomain (Chapter03NodeLocalRing k) :=
  chapter03_node_localRing_not_a_domain k

/-- The integral cusp equation `y² = x³`. -/
def chapter03CuspRelation (k : Type u) [CommRing k] :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3} :
    Set (MvPolynomial (Fin 2) k))

/-- The cusp ring `k[x,y]/(y²-x³)`. -/
abbrev Chapter03CuspRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ chapter03CuspRelation k

def chapter03CuspQuotientMap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* Chapter03CuspRing k :=
  Ideal.Quotient.mk (chapter03CuspRelation k)

def chapter03CuspX (k : Type u) [CommRing k] : Chapter03CuspRing k :=
  chapter03CuspQuotientMap k (MvPolynomial.X 0)

def chapter03CuspY (k : Type u) [CommRing k] : Chapter03CuspRing k :=
  chapter03CuspQuotientMap k (MvPolynomial.X 1)

def chapter03CuspMaximalIdeal (k : Type u) [CommRing k] :
    Ideal (Chapter03CuspRing k) :=
  (Ideal.span ({MvPolynomial.X 0, MvPolynomial.X 1} :
    Set (MvPolynomial (Fin 2) k))).map (chapter03CuspQuotientMap k)

theorem chapter03_cusp_maximalIdeal_isMaximal (k : Type u) [Field k] :
    (chapter03CuspMaximalIdeal k).IsMaximal := by
  sorry

theorem chapter03_cusp_maximalIdeal_isPrime (k : Type u) [Field k] :
    (chapter03CuspMaximalIdeal k).IsPrime := by
  sorry

instance chapter03CuspMaximalIdeal_isPrime_instance (k : Type u) [Field k] :
    (chapter03CuspMaximalIdeal k).IsPrime :=
  chapter03_cusp_maximalIdeal_isPrime k

def chapter03CuspPoint (k : Type u) [Field k] :
    PrimeSpectrum (Chapter03CuspRing k) :=
  ⟨chapter03CuspMaximalIdeal k, chapter03_cusp_maximalIdeal_isPrime k⟩

theorem chapter03_cusp_point_is_codimensionOne (k : Type u) [Field k] :
    Order.coheight (chapter03CuspPoint k) = 1 := by
  sorry

theorem chapter03_cusp_point_defines_codimensionOne_cycle (k : Type u) [Field k] :
    Nonempty (Chapter03CodimensionOnePoint
      (Spec (CommRingCat.of (Chapter03CuspRing k)))) := by
  sorry

abbrev Chapter03CuspLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (chapter03CuspMaximalIdeal k)

def chapter03CuspLocalMaximalIdeal (k : Type u) [Field k] :
    Ideal (Chapter03CuspLocalRing k) :=
  IsLocalRing.maximalIdeal (Chapter03CuspLocalRing k)

theorem chapter03_cusp_local_maximalIdeal_not_principal (k : Type u) [Field k] :
    ¬ ∃ a : Chapter03CuspLocalRing k,
      chapter03CuspLocalMaximalIdeal k = Ideal.span ({a} : Set (Chapter03CuspLocalRing k)) := by
  sorry

/-- The local effective-Cartier condition at the cusp point. -/
def chapter03CuspPointIsEffectiveCartier (k : Type u) [Field k] : Prop :=
  ∃ a : Chapter03CuspLocalRing k,
    chapter03CuspLocalMaximalIdeal k = Ideal.span ({a} : Set (Chapter03CuspLocalRing k))

theorem chapter03_cusp_point_not_effectiveCartier (k : Type u) [Field k] :
    ¬ chapter03CuspPointIsEffectiveCartier k := by
  exact chapter03_cusp_local_maximalIdeal_not_principal k

/-- The normalization parameter equations `x ↦ t²`, `y ↦ t³`. -/
def chapter03CuspParametrization
    (k : Type u) [CommRing k]
    (φ : Chapter03CuspRing k →+* Polynomial k) : Prop :=
  φ (chapter03CuspX k) = Polynomial.X ^ 2 ∧
    φ (chapter03CuspY k) = Polynomial.X ^ 3

def chapter03CuspNormalizationOriginIdeal (k : Type u) [CommRing k] : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X} : Set (Polynomial k))

theorem chapter03_cusp_normalization_exists (k : Type u) [Field k] :
    ∃ φ : Chapter03CuspRing k →+* Polynomial k,
      chapter03CuspParametrization k φ ∧
        Ideal.comap φ (chapter03CuspNormalizationOriginIdeal k) =
          chapter03CuspMaximalIdeal k := by
  sorry

noncomputable def chapter03CuspNormalizationMap (k : Type u) [Field k] :
    Chapter03CuspRing k →+* Polynomial k :=
  Classical.choose (chapter03_cusp_normalization_exists k)

theorem chapter03_cusp_normalization_map_eq_parametrization (k : Type u) [Field k] :
    chapter03CuspParametrization k (chapter03CuspNormalizationMap k) := by
  exact (Classical.choose_spec (chapter03_cusp_normalization_exists k)).1

theorem chapter03_cusp_normalization_map_preimage_origin (k : Type u) [Field k] :
    Ideal.comap (chapter03CuspNormalizationMap k)
        (chapter03CuspNormalizationOriginIdeal k) = chapter03CuspMaximalIdeal k := by
  exact (Classical.choose_spec (chapter03_cusp_normalization_exists k)).2

/-- A normal surface can have a Weil prime whose local equation does not exist. -/
def Chapter03NormalSurfaceNonCartierPrime
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03CartierDivisorTheory X] : Prop :=
  (∃ x : X, 2 ≤ ringKrullDim (X.presheaf.stalk x)) ∧
    ∃ P : Chapter03PrimeDivisor X,
      ¬ ∃ D : Chapter03CartierDivisor X,
        chapter03CartierDivisorToWeil X D = chapter03PrimeDivisorCycle P 1

theorem chapter03_normal_surface_nonCartierPrime_of_not_locallyFactorial
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Chapter03Normal X]
    [Chapter03CartierDivisorTheory X]
    (hDim : ∃ x : X, 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (h : ¬ Chapter03LocallyFactorial X) :
    Chapter03NormalSurfaceNonCartierPrime (X := X) := by
  exact ⟨hDim, chapter03_normal_nonCartier_prime_exists h⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
