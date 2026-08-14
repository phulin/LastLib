import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators

universe u v

noncomputable section

/-! ### 2.1 The affine construction -/

/-- The integral closure of `A` in the chosen `A`-algebra `L`. -/
def chapter02IntegralClosure (A L : Type u) [CommRing A] [CommRing L] [Algebra A L] :
    Subalgebra A L :=
  integralClosure A L

theorem chapter02_mem_integralClosure_iff (A L : Type u) [CommRing A] [CommRing L]
    [Algebra A L] (x : L) :
    x ∈ chapter02IntegralClosure A L ↔ IsIntegral A x := by
  exact mem_integralClosure_iff

theorem chapter02_integralClosure_isIntegral (A L : Type u) [CommRing A] [CommRing L]
    [Algebra A L] :
    Algebra.IsIntegral A (chapter02IntegralClosure A L) := by
  infer_instance

@[ext]
theorem chapter02_integralClosure_ext (A L : Type u) [CommRing A] [CommRing L]
    [Algebra A L] {S T : Subalgebra A L}
    (h : ∀ x : L, x ∈ S ↔ x ∈ T) : S = T := by
  ext x
  exact h x

/-- Addition and multiplication of integral elements, the subring assertion in Lemma 2.1. -/
theorem chapter02_integral_add_mul (A L : Type u) [CommRing A] [CommRing L] [Algebra A L]
    {x y : L} (hx : IsIntegral A x) (hy : IsIntegral A y) :
    IsIntegral A (x + y) ∧ IsIntegral A (x * y) := by
  exact ⟨hx.add hy, hx.mul hy⟩

/-- Transitivity of integrality in the form used for towers of affine algebras. -/
theorem chapter02_integral_transitive (A B C : Type u) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Algebra.IsIntegral A B]
    {x : C} (hx : IsIntegral B x) : IsIntegral A x := by
  exact isIntegral_trans x hx

/-- Finitely many integral generators give a finite module, in canonical adjoin form. -/
theorem chapter02_finite_adjoin_of_finite_integral_generators
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (s : Set B) (hs : s.Finite) (h_integral : ∀ x ∈ s, IsIntegral A x) :
    Module.Finite A (Algebra.adjoin A s) := by
  exact Algebra.finite_adjoin_of_finite_of_isIntegral hs h_integral

theorem chapter02_integralClosure_has_fractionField_of_finite_extension
    (A F L : Type u) [CommRing A] [IsDomain A] [Field F] [Field L]
    [Algebra A F] [IsFractionRing A F] [Algebra A L] [Algebra F L]
    [IsScalarTower A F L] [FiniteDimensional F L] :
    IsFractionRing (chapter02IntegralClosure A L) L := by
  exact integralClosure.isFractionRing_of_finite_extension F L

/-- The local closure is finite precisely when its integral-closure algebra is finite. -/
def Chapter02FiniteIntegralClosure (A L : Type u) [CommRing A] [CommRing L]
    [Algebra A L] : Prop :=
  Module.Finite A (chapter02IntegralClosure A L)

theorem chapter02_finiteIntegralClosure_iff (A L : Type u) [CommRing A] [CommRing L]
    [Algebra A L] :
    Chapter02FiniteIntegralClosure A L ↔
      Module.Finite A (chapter02IntegralClosure A L) :=
  Iff.rfl

/-- The minimal-prime index used in the total ring of fractions. -/
abbrev Chapter02MinimalPrime (A : Type u) [CommRing A] :=
  {p : Ideal A // p ∈ minimalPrimes A}

/-- The reduction obtained by discarding the nilradical before normalization. -/
abbrev Chapter02Reduction (A : Type u) [CommRing A] :=
  A ⧸ nilradical A

theorem chapter02_reduction_is_reduced (A : Type u) [CommRing A] :
    IsReduced (Chapter02Reduction A) := by
  sorry

/-- The fraction ring of one reduced irreducible component. -/
abbrev Chapter02ComponentFractionRing (A : Type u) [CommRing A]
    (p : Chapter02MinimalPrime A) :=
  FractionRing (A ⧸ p.1)

theorem chapter02_minimalPrime_component_isDomain (A : Type u) [CommRing A]
    (p : Chapter02MinimalPrime A) : IsDomain (A ⧸ p.1) := by
  sorry

/-- The product of the fraction rings of all minimal-prime components. -/
abbrev Chapter02TotalRingOfFractions (A : Type u) [CommRing A] :=
  ∀ p : Chapter02MinimalPrime A, Chapter02ComponentFractionRing A p

/-- The canonical component map into the corresponding fraction ring. -/
def chapter02ComponentFractionRingMap (A : Type u) [CommRing A]
    (p : Chapter02MinimalPrime A) : A →+* Chapter02ComponentFractionRing A p :=
  (algebraMap (A ⧸ p.1) (Chapter02ComponentFractionRing A p)).comp
    (Ideal.Quotient.mk p.1)

/-- The canonical map from a reduced ring to its total ring of fractions. -/
def chapter02TotalRingOfFractionsMap (A : Type u) [CommRing A] :
    A →+* Chapter02TotalRingOfFractions A where
  toFun a p := chapter02ComponentFractionRingMap A p a
  map_one' := by
    funext p
    simp [chapter02ComponentFractionRingMap]
  map_zero' := by
    funext p
    simp [chapter02ComponentFractionRingMap]
  map_add' a b := by
    funext p
    simp [chapter02ComponentFractionRingMap]
  map_mul' a b := by
    funext p
    simp [chapter02ComponentFractionRingMap]

theorem chapter02_totalRingOfFractionsMap_apply (A : Type u) [CommRing A]
    (a : A) (p : Chapter02MinimalPrime A) :
    chapter02TotalRingOfFractionsMap A a p =
      algebraMap (A ⧸ p.1) (Chapter02ComponentFractionRing A p)
        (Ideal.Quotient.mk p.1 a) :=
  rfl

/-- The standing reduced/finitely-many-components hypothesis of the displayed product formula. -/
class Chapter02ReducedFiniteMinimalPrimes (A : Type u) [CommRing A] : Prop where
  reduced : IsReduced A
  finite : Finite (Chapter02MinimalPrime A)

attribute [instance] Chapter02ReducedFiniteMinimalPrimes.reduced

/-- Component closures are indexed by the same minimal-prime product. -/
abbrev Chapter02ComponentIntegralClosure (A : Type u) [CommRing A]
    (p : Chapter02MinimalPrime A) :=
  integralClosure (A ⧸ p.1) (Chapter02ComponentFractionRing A p)

theorem chapter02_integralClosure_totalRing_components
    (A : Type u) [CommRing A] [Chapter02ReducedFiniteMinimalPrimes A] :
    letI : Algebra A (Chapter02TotalRingOfFractions A) :=
      (chapter02TotalRingOfFractionsMap A).toAlgebra
    ∀ x : Chapter02TotalRingOfFractions A,
      x ∈ integralClosure A (Chapter02TotalRingOfFractions A) ↔
        ∀ p : Chapter02MinimalPrime A,
          x p ∈ Chapter02ComponentIntegralClosure A p := by
  sorry

/-- The reduced affine normalization attached to the componentwise total fraction ring. -/
noncomputable def chapter02ReducedAffineNormalization
    (A : Type u) [CommRing A] [Chapter02ReducedFiniteMinimalPrimes A] :
    letI : Algebra A (Chapter02TotalRingOfFractions A) :=
      (chapter02TotalRingOfFractionsMap A).toAlgebra
    Scheme :=
  Spec (CommRingCat.of (integralClosure A (Chapter02TotalRingOfFractions A)))

noncomputable def chapter02ReducedAffineNormalizationMap
    (A : Type u) [CommRing A] [Chapter02ReducedFiniteMinimalPrimes A] :
    letI : Algebra A (Chapter02TotalRingOfFractions A) :=
      (chapter02TotalRingOfFractionsMap A).toAlgebra
    chapter02ReducedAffineNormalization A ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap A (integralClosure A (Chapter02TotalRingOfFractions A))))

theorem chapter02_reducedAffineNormalization_is_integral
    (A : Type u) [CommRing A] [Chapter02ReducedFiniteMinimalPrimes A] :
    letI : Algebra A (Chapter02TotalRingOfFractions A) :=
      (chapter02TotalRingOfFractionsMap A).toAlgebra
    IsIntegralHom (chapter02ReducedAffineNormalizationMap A) := by
  infer_instance

/-! The two affine examples. -/

/-- The cusp subalgebra `k[t²,t³]` inside the polynomial parameter ring. -/
def chapter02CuspSubalgebra (k : Type u) [CommRing k] : Subalgebra k (Polynomial k) :=
  Algebra.adjoin k ({Polynomial.X ^ 2, Polynomial.X ^ 3} : Set (Polynomial k))

/-- The parameter whose square already belongs to the cusp ring. -/
def chapter02CuspParameter (k : Type u) [CommRing k] : Polynomial k :=
  Polynomial.X

def chapter02CuspInclusion (k : Type u) [CommRing k] :
    chapter02CuspSubalgebra k →+* Polynomial k :=
  (chapter02CuspSubalgebra k).val.toRingHom

abbrev Chapter02CuspFunctionField (k : Type u) [CommRing k] :=
  FractionRing (Polynomial k)

def chapter02CuspToFunctionFieldMap (k : Type u) [CommRing k] :
    chapter02CuspSubalgebra k →+* Chapter02CuspFunctionField k :=
  (algebraMap (Polynomial k) (Chapter02CuspFunctionField k)).comp
    (chapter02CuspInclusion k)

theorem chapter02_cusp_parameter_integral (k : Type u) [CommRing k] :
    IsIntegral (chapter02CuspSubalgebra k) (chapter02CuspParameter k) := by
  sorry

theorem chapter02_cusp_integralClosure_eq_top (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    chapter02IntegralClosure (chapter02CuspSubalgebra k) (Polynomial k) = ⊤ := by
  sorry

theorem chapter02_cusp_integralClosure_in_functionField (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    letI : Algebra (chapter02CuspSubalgebra k) (Chapter02CuspFunctionField k) :=
      (chapter02CuspToFunctionFieldMap k).toAlgebra
    ∀ z : Chapter02CuspFunctionField k,
      IsIntegral (chapter02CuspSubalgebra k) z ↔
        ∃ p : Polynomial k,
          algebraMap (Polynomial k) (Chapter02CuspFunctionField k) p = z := by
  sorry

/-- Algebraically, the cusp normalization has no retraction to the cusp ring. -/
theorem chapter02_cusp_identity_does_not_factor (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    ¬ ∃ r : Polynomial k →+* chapter02CuspSubalgebra k,
      (chapter02CuspInclusion k).comp r = RingHom.id _ := by
  sorry

/-- The nodal polynomial ring before imposing `xy = 0`. -/
abbrev Chapter02NodePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

/-- The node ring `k[x,y]/(xy)`. -/
def chapter02NodeIdeal (k : Type u) [CommRing k] : Ideal (Chapter02NodePolynomialRing k) :=
  Ideal.span {MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)}

abbrev Chapter02NodeRing (k : Type u) [CommRing k] :=
  Chapter02NodePolynomialRing k ⧸ chapter02NodeIdeal k

/-- The two branch evaluations of the nodal polynomial ring. -/
def chapter02NodeBranchMap (k : Type u) [CommRing k] :
    Chapter02NodePolynomialRing k →+* Polynomial k × Polynomial k :=
  (MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
      (fun i => if i = (0 : Fin 2) then Polynomial.X else 0)).prod
    (MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
      (fun i => if i = (1 : Fin 2) then Polynomial.X else 0))

/-- The canonical map from the node to the disjoint pair of branch polynomial rings. -/
def chapter02NodeNormalizationMap (k : Type u) [CommRing k] :
    Chapter02NodeRing k →+* Polynomial k × Polynomial k :=
  Ideal.Quotient.lift (chapter02NodeIdeal k) (chapter02NodeBranchMap k) (by
    sorry)

theorem chapter02_node_normalization_injective (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    Function.Injective (chapter02NodeNormalizationMap k) := by
  sorry

theorem chapter02_node_integralClosure_eq_top (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    letI : Algebra (Chapter02NodeRing k) (Polynomial k × Polynomial k) :=
      (chapter02NodeNormalizationMap k).toAlgebra
    integralClosure (Chapter02NodeRing k) (Polynomial k × Polynomial k) = ⊤ := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
