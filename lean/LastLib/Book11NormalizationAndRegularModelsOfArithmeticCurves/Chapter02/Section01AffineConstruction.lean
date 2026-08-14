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
  rfl

theorem chapter02_integralClosure_isIntegral (A L : Type u) [CommRing A] [CommRing L]
    [Algebra A L] :
    Algebra.IsIntegral A (chapter02IntegralClosure A L) := by
  exact ⟨fun x => integralClosure.isIntegral x⟩

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
  constructor
  rintro ⟨x⟩ ⟨n, hn⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [mem_nilradical]
  change (Ideal.Quotient.mk (nilradical A) x) ^ n = 0 at hn
  rw [← map_pow] at hn
  have hxn : x ^ n ∈ nilradical A := Ideal.Quotient.eq_zero_iff_mem.mp hn
  obtain ⟨m, hm⟩ := mem_nilradical.mp hxn
  refine ⟨n * m, ?_⟩
  rw [pow_mul]
  exact hm

/-- The fraction ring of one reduced irreducible component. -/
abbrev Chapter02ComponentFractionRing (A : Type u) [CommRing A]
    (p : Chapter02MinimalPrime A) :=
  FractionRing (A ⧸ p.1)

theorem chapter02_minimalPrime_component_isDomain (A : Type u) [CommRing A]
    (p : Chapter02MinimalPrime A) : IsDomain (A ⧸ p.1) := by
  exact (Ideal.Quotient.isDomain_iff_prime p.1).2 p.2.isPrime

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
attribute [instance] Chapter02ReducedFiniteMinimalPrimes.finite

theorem chapter02_totalRingOfFractionsMap_injective
    (A : Type u) [CommRing A] [Chapter02ReducedFiniteMinimalPrimes A] :
    Function.Injective (chapter02TotalRingOfFractionsMap A) := by
  intro a b hab
  have hmem : a - b ∈ nilradical A := by
    change a - b ∈ (⊥ : Ideal A).radical
    rw [← Ideal.sInf_minimalPrimes (I := (⊥ : Ideal A)), Ideal.mem_sInf]
    intro p hp
    let p' : Chapter02MinimalPrime A := ⟨p, hp⟩
    have hpmap := congr_fun hab p'
    change
      algebraMap (A ⧸ p) (Chapter02ComponentFractionRing A p')
          (Ideal.Quotient.mk p a) =
        algebraMap (A ⧸ p) (Chapter02ComponentFractionRing A p')
          (Ideal.Quotient.mk p b) at hpmap
    have hq : Ideal.Quotient.mk p a = Ideal.Quotient.mk p b :=
      (IsFractionRing.injective (A ⧸ p) (Chapter02ComponentFractionRing A p')) hpmap
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hq, sub_self]
  have hab' : a - b = 0 := by
    have : a - b ∈ (0 : Ideal A) := by
      simpa [nilradical_eq_zero A] using hmem
    exact this
  exact sub_eq_zero.mp hab'

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
  change ∀ (x : Chapter02TotalRingOfFractions A),
    IsIntegral A x ↔ ∀ (p : Chapter02MinimalPrime A),
      IsIntegral (A ⧸ p.1) (x p)
  intro x
  constructor
  · intro hx p
    exact IsIntegral.map_of_comp_eq
      (Ideal.Quotient.mk p.1)
      (Pi.evalRingHom (fun p : Chapter02MinimalPrime A =>
        Chapter02ComponentFractionRing A p) p) (by ext a; rfl) hx
  · intro hx
    classical
    let : Fintype (Chapter02MinimalPrime A) := Fintype.ofFinite _
    have hcoord : ∀ p : Chapter02MinimalPrime A,
        (chapter02ComponentFractionRingMap A p).IsIntegralElem (x p) := by
      intro p
      let : IsDomain (A ⧸ p.1) := chapter02_minimalPrime_component_isDomain A p
      have hp := hx p
      change ∃ q : Polynomial (A ⧸ p.1), q.Monic ∧
        Polynomial.eval₂ (algebraMap (A ⧸ p.1) (Chapter02ComponentFractionRing A p))
          (x p) q = 0 at hp
      obtain ⟨q, hqm, hq⟩ := hp
      obtain ⟨q', hmap, hdeg, hq'm⟩ :=
        Polynomial.lifts_and_degree_eq_and_monic
          (f := Ideal.Quotient.mk p.1)
          (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective q) hqm
      refine ⟨q', hq'm, ?_⟩
      simpa only [chapter02ComponentFractionRingMap, ← Polynomial.eval₂_map, hmap] using hq
    let q : Chapter02MinimalPrime A → Polynomial A := fun p => (hcoord p).choose
    have hqm : ∀ p : Chapter02MinimalPrime A, (q p).Monic :=
      fun p => (hcoord p).choose_spec.1
    have hqr : ∀ p : Chapter02MinimalPrime A,
        Polynomial.eval₂ (chapter02ComponentFractionRingMap A p) (x p) (q p) = 0 :=
      fun p => (hcoord p).choose_spec.2
    refine ⟨∏ p, q p, Polynomial.monic_prod_of_monic Finset.univ q (by
      intro p hp
      exact hqm p), ?_⟩
    funext p
    have hcomp :
        (Pi.evalRingHom (fun p : Chapter02MinimalPrime A =>
          Chapter02ComponentFractionRing A p) p).comp
            (algebraMap A (Chapter02TotalRingOfFractions A)) =
          chapter02ComponentFractionRingMap A p := by
      ext a
      rfl
    have heval :
        Polynomial.eval₂ (chapter02ComponentFractionRingMap A p) (x p) (∏ r, q r) = 0 := by
      rw [Polynomial.eval₂_finsetProd]
      exact Finset.prod_eq_zero (Finset.mem_univ p) (hqr p)
    calc
      (Polynomial.eval₂ (algebraMap A (Chapter02TotalRingOfFractions A)) x
        (∏ r, q r)) p =
          (Pi.evalRingHom (fun p : Chapter02MinimalPrime A =>
            Chapter02ComponentFractionRing A p) p)
            (Polynomial.eval₂ (algebraMap A (Chapter02TotalRingOfFractions A)) x
              (∏ r, q r)) := rfl
      _ = Polynomial.eval₂
            ((Pi.evalRingHom (fun p : Chapter02MinimalPrime A =>
              Chapter02ComponentFractionRing A p) p).comp
                (algebraMap A (Chapter02TotalRingOfFractions A)))
            ((Pi.evalRingHom (fun p : Chapter02MinimalPrime A =>
              Chapter02ComponentFractionRing A p) p) x) (∏ r, q r) := by
        rw [Polynomial.hom_eval₂]
      _ = Polynomial.eval₂
            ((Pi.evalRingHom (fun p : Chapter02MinimalPrime A =>
              Chapter02ComponentFractionRing A p) p).comp
                (algebraMap A (Chapter02TotalRingOfFractions A)))
            (x p) (∏ r, q r) := by
        rfl
      _ = Polynomial.eval₂ (chapter02ComponentFractionRingMap A p) (x p)
            (∏ r, q r) := by rw [hcomp]
      _ = 0 := heval

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
  dsimp [chapter02ReducedAffineNormalizationMap]
  apply IsIntegralHom.SpecMap_iff.mpr
  exact algebraMap_isIntegral_iff.mpr inferInstance

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
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  let x2 : chapter02CuspSubalgebra k :=
    ⟨Polynomial.X ^ 2, Algebra.subset_adjoin (by simp)⟩
  change IsIntegral (chapter02CuspSubalgebra k)
    (algebraMap (chapter02CuspSubalgebra k) (Polynomial k) x2)
  exact isIntegral_algebraMap

theorem chapter02_cusp_integralClosure_eq_top (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    chapter02IntegralClosure (chapter02CuspSubalgebra k) (Polynomial k) = ⊤ := by
  change integralClosure (chapter02CuspSubalgebra k) (Polynomial k) = ⊤
  apply integralClosure_eq_top_iff.mpr
  let S := Algebra.adjoin (chapter02CuspSubalgebra k)
    ({Polynomial.X} : Set (Polynomial k))
  have hS : S = ⊤ := by
    apply Subalgebra.restrictScalars_injective k
    rw [Algebra.restrictScalars_adjoin, Subalgebra.restrictScalars_top]
    apply le_antisymm
    · exact le_top
    · rw [← Polynomial.adjoin_X]
      apply Algebra.adjoin_mono
      exact Set.subset_union_right
  have hI : Algebra.IsIntegral (chapter02CuspSubalgebra k) S :=
    Algebra.IsIntegral.adjoin (by
      rintro x rfl
      exact chapter02_cusp_parameter_integral k)
  let _ : Algebra.IsIntegral (chapter02CuspSubalgebra k) S := hI
  exact Algebra.IsIntegral.of_surjective (R := chapter02CuspSubalgebra k)
    (A := S) (B := Polynomial k) S.val (by
      intro p
      have hp : p ∈ S := by
        rw [hS]
        trivial
      exact ⟨⟨p, hp⟩, rfl⟩)

theorem chapter02_cusp_integralClosure_in_functionField (k : Type u) [Field k] :
    letI : Algebra (chapter02CuspSubalgebra k) (Chapter02CuspFunctionField k) :=
      (chapter02CuspToFunctionFieldMap k).toAlgebra
    ∀ z : Chapter02CuspFunctionField k,
      IsIntegral (chapter02CuspSubalgebra k) z ↔
        ∃ p : Polynomial k,
          algebraMap (Polynomial k) (Chapter02CuspFunctionField k) p = z := by
  intro z
  constructor
  · intro hz
    have hcomp :
        (algebraMap (Polynomial k) (Chapter02CuspFunctionField k)).comp
            (algebraMap (chapter02CuspSubalgebra k) (Polynomial k)) =
          (RingHom.id (Chapter02CuspFunctionField k)).comp
            (algebraMap (chapter02CuspSubalgebra k) (Chapter02CuspFunctionField k)) := by
      ext r
      rfl
    have hz' : IsIntegral (Polynomial k) z := by
      simpa using IsIntegral.map_of_comp_eq
        (algebraMap (chapter02CuspSubalgebra k) (Polynomial k))
        (RingHom.id (Chapter02CuspFunctionField k)) hcomp hz
    exact (inferInstance : IsIntegrallyClosed (Polynomial k)).algebraMap_eq_of_integral hz'
  · rintro ⟨p, rfl⟩
    have hp : IsIntegral (chapter02CuspSubalgebra k) p := by
      change p ∈ chapter02IntegralClosure (chapter02CuspSubalgebra k) (Polynomial k)
      rw [chapter02_cusp_integralClosure_eq_top k]
      trivial
    rcases hp with ⟨q, hqm, hq⟩
    refine ⟨q, hqm, ?_⟩
    change Polynomial.eval₂
      (algebraMap (chapter02CuspSubalgebra k) (Chapter02CuspFunctionField k))
      (algebraMap (Polynomial k) (Chapter02CuspFunctionField k) p) q = 0
    have hcomp :
        (algebraMap (Polynomial k) (Chapter02CuspFunctionField k)).comp
            (algebraMap (chapter02CuspSubalgebra k) (Polynomial k)) =
          algebraMap (chapter02CuspSubalgebra k) (Chapter02CuspFunctionField k) := by
      ext r
      rfl
    have hq' := congrArg (algebraMap (Polynomial k) (Chapter02CuspFunctionField k)) hq
    rw [Polynomial.hom_eval₂, hcomp, map_zero] at hq'
    exact hq'

/-- Algebraically, the cusp normalization has no retraction to the cusp ring. -/
theorem chapter02_cusp_identity_does_not_factor (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    ¬ ∃ r : Polynomial k →+* chapter02CuspSubalgebra k,
      r.comp (chapter02CuspInclusion k) = RingHom.id _ := by
  rintro ⟨r, hr⟩
  have hcoeff : ∀ p : Polynomial k, p ∈ chapter02CuspSubalgebra k → p.coeff 1 = 0 := by
    intro p hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with (rfl | rfl) <;> simp
    | algebraMap r =>
        simp
    | add x y _ _ hx hy =>
        simp [Polynomial.coeff_add, hx, hy]
    | mul x y _ _ hx hy =>
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        norm_num [Finset.sum_range_succ, hx, hy]
  let s2 : chapter02CuspSubalgebra k :=
    ⟨Polynomial.X ^ 2, Algebra.subset_adjoin (by simp)⟩
  let s3 : chapter02CuspSubalgebra k :=
    ⟨Polynomial.X ^ 3, Algebra.subset_adjoin (by simp)⟩
  have h2 := congrArg
    (fun f : chapter02CuspSubalgebra k →+* chapter02CuspSubalgebra k => f s2) hr
  have h3 := congrArg
    (fun f : chapter02CuspSubalgebra k →+* chapter02CuspSubalgebra k => f s3) hr
  have h2' : r (Polynomial.X ^ 2) = s2 := by
    simpa [s2, chapter02CuspInclusion] using h2
  have h3' : r (Polynomial.X ^ 3) = s3 := by
    simpa [s3, chapter02CuspInclusion] using h3
  have ha2 : (r Polynomial.X : Polynomial k) ^ 2 = Polynomial.X ^ 2 := by
    calc
      (r Polynomial.X : Polynomial k) ^ 2 =
          (r (Polynomial.X ^ 2) : Polynomial k) := by
        exact (congrArg Subtype.val (map_pow r Polynomial.X 2)).symm
      _ = Polynomial.X ^ 2 := congrArg Subtype.val h2'
  have ha3 : (r Polynomial.X : Polynomial k) ^ 3 = Polynomial.X ^ 3 := by
    calc
      (r Polynomial.X : Polynomial k) ^ 3 =
          (r (Polynomial.X ^ 3) : Polynomial k) := by
        exact (congrArg Subtype.val (map_pow r Polynomial.X 3)).symm
      _ = Polynomial.X ^ 3 := congrArg Subtype.val h3'
  have hfactor : (r Polynomial.X : Polynomial k) ^ 2 *
      ((r Polynomial.X : Polynomial k) - Polynomial.X) = 0 := by
    calc
      (r Polynomial.X : Polynomial k) ^ 2 *
          ((r Polynomial.X : Polynomial k) - Polynomial.X) =
        (r Polynomial.X : Polynomial k) ^ 3 -
          Polynomial.X * (r Polynomial.X : Polynomial k) ^ 2 := by ring
      _ = Polynomial.X ^ 3 - Polynomial.X * Polynomial.X ^ 2 := by rw [ha2, ha3]
      _ = 0 := by ring
  have hne : (r Polynomial.X : Polynomial k) ^ 2 ≠ 0 := by
    rw [ha2]
    exact pow_ne_zero 2 Polynomial.X_ne_zero
  have hXdiff : (r Polynomial.X : Polynomial k) - Polynomial.X = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hne
  have hX : (r Polynomial.X : Polynomial k) = Polynomial.X :=
    sub_eq_zero.mp hXdiff
  have hmem : Polynomial.X ∈ chapter02CuspSubalgebra k := by
    rw [← hX]
    exact (r Polynomial.X).property
  have hcoeffX : (Polynomial.X : Polynomial k).coeff 1 = 0 := hcoeff _ hmem
  have hcoeffX' : (1 : k) = 0 := by
    simpa only [Polynomial.coeff_X_zero, Polynomial.coeff_X_one] using hcoeffX
  exact (one_ne_zero : (1 : k) ≠ 0) hcoeffX'

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
    intro a ha
    change a ∈ Ideal.span
      ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
        Set (Chapter02NodePolynomialRing k)) at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [chapter02NodeBranchMap])

theorem chapter02_node_normalization_injective (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    Function.Injective (chapter02NodeNormalizationMap k) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Ideal.Quotient.eq.2
  let I : Ideal (Chapter02NodePolynomialRing k) := chapter02NodeIdeal k
  let x0 : Chapter02NodePolynomialRing k := MvPolynomial.X (0 : Fin 2)
  let x1 : Chapter02NodePolynomialRing k := MvPolynomial.X (1 : Fin 2)
  let e0 : Chapter02NodePolynomialRing k →+* Polynomial k :=
    MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
      (fun i => if i = (0 : Fin 2) then Polynomial.X else 0)
  let e1 : Chapter02NodePolynomialRing k →+* Polynomial k :=
    MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
      (fun i => if i = (1 : Fin 2) then Polynomial.X else 0)
  let l0 : Polynomial k →+* Chapter02NodePolynomialRing k :=
    Polynomial.eval₂RingHom (algebraMap k (Chapter02NodePolynomialRing k)) x0
  let l1 : Polynomial k →+* Chapter02NodePolynomialRing k :=
    Polynomial.eval₂RingHom (algebraMap k (Chapter02NodePolynomialRing k)) x1
  have hgen : x0 * x1 ∈ I := by
    simp [I, x0, x1, chapter02NodeIdeal]
  have hcross0 : ∀ q : Polynomial k,
      (l0 q - MvPolynomial.C (q.coeff 0)) * x1 ∈ I := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
        convert I.add_mem hp hq using 1; simp [l0, Polynomial.coeff_add]; ring
    | monomial n a =>
        cases n with
        | zero =>
            simp [l0]
        | succ n =>
            have hm := I.mul_mem_left (MvPolynomial.C a * x0 ^ n) hgen
            convert hm using 1; simp [l0, x0, x1, pow_succ]; ring
  have hcross1 : ∀ q : Polynomial k,
      (l1 q - MvPolynomial.C (q.coeff 0)) * x0 ∈ I := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
        convert I.add_mem hp hq using 1; simp [l1, Polynomial.coeff_add]; ring
    | monomial n a =>
        cases n with
        | zero =>
            simp [l1]
        | succ n =>
            have hm := I.mul_mem_left (MvPolynomial.C a * x1 ^ n) hgen
            convert hm using 1; simp [l1, x0, x1, pow_succ]; ring
  have hconst : ∀ p : Chapter02NodePolynomialRing k,
      (e0 p).coeff 0 = (e1 p).coeff 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        simp [e0, e1]
    | add p q hp hq =>
        simpa [e0, e1, Polynomial.coeff_add] using congrArg₂ (· + ·) hp hq
    | mul_X p i hp =>
        fin_cases i <;> simp [e0, e1]
  let d : Chapter02NodePolynomialRing k → Chapter02NodePolynomialRing k :=
    fun p => p - l0 (e0 p) - l1 (e1 p) + MvPolynomial.C ((e0 p).coeff 0)
  have hdecomp : ∀ p : Chapter02NodePolynomialRing k, d p ∈ I := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        simp [d, e0, e1, l0, l1]
    | add p q hp hq =>
        convert I.add_mem hp hq using 1; simp [d, e0, e1, l0, l1, Polynomial.coeff_add]; ring
    | mul_X p i hp =>
        fin_cases i
        · have hm := I.mul_mem_left x0 hp
          have hc := hcross1 (e1 p)
          rw [← hconst p] at hc
          convert I.add_mem hm hc using 1; simp [d, e0, e1, l0, l1, x0, x1]; ring
        · have hm := I.mul_mem_left x1 hp
          have hc := hcross0 (e0 p)
          convert I.add_mem hm hc using 1; simp [d, e0, e1, l0, l1, x0, x1]; ring
  have h0 : e0 a = e0 b := by
    have h := congrArg Prod.fst hab
    change (chapter02NodeBranchMap k a).1 = (chapter02NodeBranchMap k b).1 at h
    simpa [chapter02NodeBranchMap, e0] using h
  have h1 : e1 a = e1 b := by
    have h := congrArg Prod.snd hab
    change (chapter02NodeBranchMap k a).2 = (chapter02NodeBranchMap k b).2 at h
    simpa [chapter02NodeBranchMap, e1] using h
  have hs := I.sub_mem (hdecomp a) (hdecomp b)
  simpa [d, h0, h1] using hs

theorem chapter02_node_integralClosure_eq_top (k : Type u) [CommRing k]
    [Nontrivial k] [NoZeroDivisors k] :
    letI : Algebra (Chapter02NodeRing k) (Polynomial k × Polynomial k) :=
      (chapter02NodeNormalizationMap k).toAlgebra
    integralClosure (Chapter02NodeRing k) (Polynomial k × Polynomial k) = ⊤ := by
  let : Algebra (Chapter02NodeRing k) (Polynomial k × Polynomial k) :=
    (chapter02NodeNormalizationMap k).toAlgebra
  change integralClosure (Chapter02NodeRing k) (Polynomial k × Polynomial k) = ⊤
  apply integralClosure_eq_top_iff.mpr
  have h01 : (0 : Chapter02NodeRing k) ≠ 1 := by
    intro h
    have hm := congrArg (algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k)) h
    have hm' : (0 : Polynomial k × Polynomial k) = 1 := by
      simpa only [map_zero, map_one] using hm
    exact zero_ne_one hm'
  let : Nontrivial (Chapter02NodeRing k) := ⟨⟨0, 1, h01⟩⟩
  let e : Polynomial k × Polynomial k := (0, 1)
  have hdeg : (Polynomial.X : Polynomial (Chapter02NodeRing k)).degree < 2 := by
    rw [Polynomial.degree_X]
    norm_num
  have heint : IsIntegral (Chapter02NodeRing k) e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X,
      Polynomial.monic_X_pow_sub (p := Polynomial.X) (n := 2) hdeg, ?_⟩
    ext <;> simp [e, pow_two]
  let T := Algebra.adjoin (Chapter02NodeRing k)
    ({e} : Set (Polynomial k × Polynomial k))
  have he : e ∈ T := Algebra.subset_adjoin (by simp)
  have hT : T = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro z hz
      rcases z with ⟨p, q⟩
      let x0 : Chapter02NodePolynomialRing k := MvPolynomial.X (0 : Fin 2)
      let x1 : Chapter02NodePolynomialRing k := MvPolynomial.X (1 : Fin 2)
      let l0 : Polynomial k →+* Chapter02NodePolynomialRing k :=
        Polynomial.eval₂RingHom (algebraMap k (Chapter02NodePolynomialRing k)) x0
      let l1 : Polynomial k →+* Chapter02NodePolynomialRing k :=
        Polynomial.eval₂RingHom (algebraMap k (Chapter02NodePolynomialRing k)) x1
      let e0 : Chapter02NodePolynomialRing k →+* Polynomial k :=
        MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
          (fun i => if i = (0 : Fin 2) then Polynomial.X else 0)
      let e1 : Chapter02NodePolynomialRing k →+* Polynomial k :=
        MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
          (fun i => if i = (1 : Fin 2) then Polynomial.X else 0)
      let a0 : Chapter02NodeRing k :=
        Ideal.Quotient.mk (chapter02NodeIdeal k) (l0 p)
      let r : Polynomial k := q - Polynomial.C (p.coeff 0)
      let a1 : Chapter02NodeRing k :=
        Ideal.Quotient.mk (chapter02NodeIdeal k) (l1 r)
      have he00 : ∀ s : Polynomial k, e0 (l0 s) = s := by
        intro s
        induction s using Polynomial.induction_on' with
        | add p q hp hq =>
            simpa [e0, l0] using congrArg₂ (· + ·) hp hq
        | monomial n a =>
            simp [e0, l0, x0, Polynomial.C_mul_X_pow_eq_monomial]
      have he01 : ∀ s : Polynomial k,
          e1 (l0 s) = Polynomial.C (s.coeff 0) := by
        intro s
        induction s using Polynomial.induction_on' with
        | add p q hp hq =>
            simpa [e1, l0, x0, Polynomial.coeff_add] using
              congrArg₂ (· + ·) hp hq
        | monomial n a =>
            cases n with
            | zero => simp [e1, l0, x0]
            | succ n => simp [e1, l0, x0]
      have he10 : ∀ s : Polynomial k,
          e0 (l1 s) = Polynomial.C (s.coeff 0) := by
        intro s
        induction s using Polynomial.induction_on' with
        | add p q hp hq =>
            simpa [e0, l1, x1, Polynomial.coeff_add] using
              congrArg₂ (· + ·) hp hq
        | monomial n a =>
            cases n with
            | zero => simp [e0, l1, x1]
            | succ n => simp [e0, l1, x1]
      have he11 : ∀ s : Polynomial k, e1 (l1 s) = s := by
        intro s
        induction s using Polynomial.induction_on' with
        | add p q hp hq =>
            simpa [e1, l1] using congrArg₂ (· + ·) hp hq
        | monomial n a =>
            simp [e1, l1, x1, Polynomial.C_mul_X_pow_eq_monomial]
      have ha0 : algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k) a0 =
          (p, Polynomial.C (p.coeff 0)) := by
        change chapter02NodeNormalizationMap k (Ideal.Quotient.mk
          (chapter02NodeIdeal k) (l0 p)) = _
        rw [chapter02NodeNormalizationMap, Ideal.Quotient.lift_mk]
        change (e0 (l0 p), e1 (l0 p)) = _
        exact Prod.ext (he00 p) (he01 p)
      have ha1 : algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k) a1 =
          (Polynomial.C (r.coeff 0), r) := by
        change chapter02NodeNormalizationMap k (Ideal.Quotient.mk
          (chapter02NodeIdeal k) (l1 r)) = _
        rw [chapter02NodeNormalizationMap, Ideal.Quotient.lift_mk]
        change (e0 (l1 r), e1 (l1 r)) = _
        exact Prod.ext (he10 r) (he11 r)
      have hm0 : algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k) a0 ∈ T :=
        Subalgebra.algebraMap_mem T a0
      have hm1 : algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k) a1 ∈ T :=
        Subalgebra.algebraMap_mem T a1
      have hsum :
          algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k) a0 +
              e * algebraMap (Chapter02NodeRing k) (Polynomial k × Polynomial k) a1 =
            (p, q) := by
        rw [ha0, ha1]
        ext <;> simp [e, r]
      rw [← hsum]
      exact T.add_mem hm0 (T.mul_mem he hm1)
  have hTI : Algebra.IsIntegral (Chapter02NodeRing k) T :=
    Algebra.IsIntegral.adjoin (by
      rintro z rfl
      exact heint)
  let _ : Algebra.IsIntegral (Chapter02NodeRing k) T := hTI
  exact Algebra.IsIntegral.of_surjective (R := Chapter02NodeRing k)
    (A := T) (B := Polynomial k × Polynomial k) T.val (by
      intro z
      have hz : z ∈ T := by
        rw [hT]
        trivial
      exact ⟨⟨z, hz⟩, rfl⟩)

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
