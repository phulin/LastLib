import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section01LocalEquationsModuloUnits

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
### 2.2 Effective Cartier divisors
-/

abbrev Chapter02IsEffectiveCartierIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) : Prop :=
  I.IsEffectiveCartier

abbrev Chapter02InvertibleIdealSheaf {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  Chapter02IsEffectiveCartierIdeal I

def Chapter02CartierIdealRepresents {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X)
    (I : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : U.1),
    ∃ (i : D.index) (V : X.affineOpens) (f : Γ(X, V.1))
      (hVD : V.1 ≤ D.openSet i) (hxV : x.1 ∈ V.1),
      V ≤ U ∧
        chapter02RegularSectionIsRegularAt V.1 f x.1 hxV ∧
        I.ideal V = Ideal.span ({f} : Set Γ(X, V.1)) ∧
        chapter02RegularSectionMap X V.1 f =
          chapter02MeromorphicRestriction X hVD
            (D.equation i : Chapter02MeromorphicSection X (D.openSet i))

structure Chapter02EffectiveCartierDivisor (X : Scheme.{u})
    [K : Chapter02MeromorphicSheaf X] where
  divisor : Chapter02CartierDivisor.{u, v} X
  effective : divisor.IsEffective
  ideal : X.IdealSheafData
  ideal_is_effective_cartier : Chapter02IsEffectiveCartierIdeal ideal
  ideal_represents_divisor : Chapter02CartierIdealRepresents divisor ideal

namespace Chapter02EffectiveCartierDivisor

abbrev subscheme {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) : Scheme := D.ideal.subscheme

abbrev inclusion {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) : D.subscheme ⟶ X := D.ideal.subschemeι

theorem ideal_is_invertible {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    Chapter02InvertibleIdealSheaf D.ideal :=
  D.ideal_is_effective_cartier

end Chapter02EffectiveCartierDivisor

theorem chapter02_effective_cartier_divisor_ext
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D E : Chapter02EffectiveCartierDivisor X)
    (hdiv : D.divisor = E.divisor) (hideal : D.ideal = E.ideal) :
    D = E := by
  cases D
  cases E
  cases hdiv
  cases hideal
  rfl

theorem chapter02_effective_cartier_ideal_exists
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02CartierDivisor X) (hD : D.IsEffective) :
    Nonempty {I : X.IdealSheafData //
      Chapter02IsEffectiveCartierIdeal I ∧ Chapter02CartierIdealRepresents D I} := by
  sorry

theorem chapter02_effective_cartier_divisor_of_ideal
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (I : X.IdealSheafData) (hI : Chapter02IsEffectiveCartierIdeal I) :
    Nonempty {D : Chapter02EffectiveCartierDivisor X // D.ideal = I} := by
  sorry

noncomputable def chapter02EffectiveCartierDivisorOf
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02CartierDivisor X) (hD : D.IsEffective) :
    Chapter02EffectiveCartierDivisor X :=
  let E := Classical.choice (chapter02_effective_cartier_ideal_exists D hD)
  { divisor := D
    effective := hD
    ideal := E.1
    ideal_is_effective_cartier := E.2.1
    ideal_represents_divisor := E.2.2 }

theorem chapter02_effective_ideal_closed_subscheme
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    IsClosedImmersion D.inclusion := by
  infer_instance

theorem chapter02_effective_support_eq_ideal_support
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    D.divisor.support = (D.ideal.support : Set X) := by
  sorry

abbrev chapter02StructureSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

noncomputable def chapter02IdealQuotientModule {X : Scheme.{u}}
    (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf)

noncomputable def chapter02IdealQuotient {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    chapter02StructureSheaf X ⟶ chapter02IdealQuotientModule I :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

noncomputable def chapter02IdealOminusD {X : Scheme.{u}}
    (I : X.IdealSheafData) : X.Modules :=
  kernel (chapter02IdealQuotient I)

abbrev chapter02OminusD {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) : X.Modules :=
  chapter02IdealOminusD D.ideal

noncomputable def chapter02IdealInclusion {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    chapter02IdealOminusD I ⟶ chapter02StructureSheaf X :=
  kernel.ι (chapter02IdealQuotient I)

theorem chapter02_ideal_inclusion_comp_quotient {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    chapter02IdealInclusion I ≫ chapter02IdealQuotient I = 0 :=
  kernel.condition _

structure Chapter02CartierExactSequence {X : Scheme.{u}}
    (I : X.IdealSheafData) where
  effective : Chapter02IsEffectiveCartierIdeal I
  comp_zero : chapter02IdealInclusion I ≫ chapter02IdealQuotient I = 0
  mono_inclusion : Mono (chapter02IdealInclusion I)
  epi_quotient : Epi (chapter02IdealQuotient I)
  exact : (ShortComplex.mk (chapter02IdealInclusion I)
    (chapter02IdealQuotient I) comp_zero).Exact

theorem chapter02_effective_cartier_exact_sequence_of_ideal
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : Chapter02IsEffectiveCartierIdeal I) :
    Nonempty (Chapter02CartierExactSequence I) := by
  refine ⟨{
    effective := hI
    comp_zero := chapter02_ideal_inclusion_comp_quotient I
    mono_inclusion := by
      change Mono (kernel.ι (chapter02IdealQuotient I))
      infer_instance
    epi_quotient := by
      let F := SheafOfModules.toSheaf X.ringCatSheaf
      have hEpi : Epi (F.map (chapter02IdealQuotient I)) := by
        rw [← CategoryTheory.Sheaf.isLocallySurjective_iff_epi']
        change TopCat.Presheaf.IsLocallySurjective
          ((F.map (chapter02IdealQuotient I)).hom)
        rw [TopCat.Presheaf.isLocallySurjective_iff]
        intro U t x hxU
        obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
        let V' : X.affineOpens := ⟨V, hV⟩
        obtain ⟨s, hs⟩ := I.subschemeι_app_surjective V'
          (t |_ V)
        refine ⟨V, hVU, ⟨s, ?_⟩, hxV⟩
        exact hs
      refine ⟨fun g h hgh => ?_⟩
      apply F.map_injective
      apply (cancel_epi (F.map (chapter02IdealQuotient I))).1
      change F.map (chapter02IdealQuotient I ≫ g) =
        F.map (chapter02IdealQuotient I ≫ h)
      exact congrArg F.map hgh
    exact := ShortComplex.exact_kernel (chapter02IdealQuotient I) }⟩

theorem chapter02_effective_cartier_exact_sequence_exists
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    Nonempty (Chapter02CartierExactSequence D.ideal) := by
  exact chapter02_effective_cartier_exact_sequence_of_ideal D.ideal
    D.ideal_is_effective_cartier

theorem chapter02EffectiveCartierExactSequence
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    Chapter02CartierExactSequence D.ideal :=
  Classical.choice (chapter02_effective_cartier_exact_sequence_exists D)

theorem chapter02_effective_cartier_exact_sequence_left_mono
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    Mono (chapter02IdealInclusion D.ideal) := by
  exact (chapter02EffectiveCartierExactSequence D).mono_inclusion

theorem chapter02_effective_cartier_exact_sequence
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) :
    (ShortComplex.mk
      (chapter02IdealInclusion D.ideal)
      (chapter02IdealQuotient D.ideal)
      (chapter02EffectiveCartierExactSequence D).comp_zero).Exact :=
  (chapter02EffectiveCartierExactSequence D).exact

theorem chapter02_effective_add_exists
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D E : Chapter02EffectiveCartierDivisor X) :
    Nonempty {F : Chapter02EffectiveCartierDivisor X //
      F.divisor = D.divisor.add E.divisor ∧ F.ideal = D.ideal * E.ideal} := by
  sorry

noncomputable def Chapter02EffectiveCartierDivisor.add
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D E : Chapter02EffectiveCartierDivisor X) :
    Chapter02EffectiveCartierDivisor X :=
  (Classical.choice (chapter02_effective_add_exists D E)).1

theorem chapter02_effective_add_divisor
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D E : Chapter02EffectiveCartierDivisor X) :
    (D.add E).divisor = D.divisor.add E.divisor :=
  (Classical.choice (chapter02_effective_add_exists D E)).2.1

theorem chapter02_effective_add_ideal
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D E : Chapter02EffectiveCartierDivisor X) :
    (D.add E).ideal = D.ideal * E.ideal :=
  (Classical.choice (chapter02_effective_add_exists D E)).2.2

def Chapter02CartierDivisor.nsmul {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) (n : ℕ) :
    Chapter02CartierDivisor X where
  index := D.index
  openSet := D.openSet
  cover := D.cover
  equation i := (D.equation i) ^ n
  equationClass i := Quotient.mk' ((D.equation i) ^ n)
  equationClass_eq i := rfl
  transition := by
    intro i j
    obtain ⟨u, hu⟩ := D.transition i j
    refine ⟨u ^ n, ?_⟩
    rw [map_pow, hu]
    simp only [chapter02MeromorphicRestrictionUnit, map_pow, inv_pow, mul_pow]

theorem chapter02_effective_natMultiple_exists
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    Nonempty {F : Chapter02EffectiveCartierDivisor X //
      F.divisor = D.divisor.nsmul n ∧ F.ideal = D.ideal ^ n} := by
  sorry

noncomputable def Chapter02EffectiveCartierDivisor.natMultiple
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    Chapter02EffectiveCartierDivisor X :=
  (Classical.choice (chapter02_effective_natMultiple_exists D n)).1

theorem chapter02_effective_multiple_local_equation
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    (D.natMultiple n).divisor.IsEffective := by
  exact (D.natMultiple n).effective

theorem chapter02_effective_multiple_divisor
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    (D.natMultiple n).divisor = D.divisor.nsmul n :=
  (Classical.choice (chapter02_effective_natMultiple_exists D n)).2.1

theorem chapter02_effective_multiple_has_power_local_equation
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    ∀ i : D.divisor.index,
      ∀ x : X, x ∈ D.divisor.openSet i →
        ∃ (V : X.Opens) (hxV : x ∈ V) (hV : V ≤ D.divisor.openSet i)
          (f : Γ(X, V)),
          chapter02RegularSectionIsRegularAt V f x hxV ∧
            chapter02RegularSectionMap X V (f ^ n) =
              chapter02MeromorphicRestriction X hV
                ((D.divisor.equation i :
                  Chapter02MeromorphicSection X (D.divisor.openSet i)) ^ n) := by
  sorry

theorem chapter02_effective_multiple_ideal
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    (D.natMultiple n).ideal = D.ideal ^ n :=
  (Classical.choice (chapter02_effective_natMultiple_exists D n)).2.2

theorem chapter02_effective_multiple_support
    {X : Scheme.{u}} [K : Chapter02MeromorphicSheaf X]
    (D : Chapter02EffectiveCartierDivisor X) (n : ℕ) :
    (D.natMultiple (n + 1)).ideal.support = D.ideal.support := by
  rw [chapter02_effective_multiple_ideal]
  simp

def Chapter02PrincipalEquationIsEffective (R : Type u) [CommRing R] (f : R) : Prop :=
  f ∈ nonZeroDivisors R

theorem chapter02_principal_equation_effective_iff_injective
    (R : Type u) [CommRing R] (f : R) :
    Chapter02PrincipalEquationIsEffective R f ↔
      Function.Injective (fun x : R => f * x) := by
  exact chapter02_regular_element_iff_injective_multiplication R f

theorem chapter02_zero_divisor_multiplication_not_injective
    (R : Type u) [CommRing R] (f : R)
    (hf : f ∉ nonZeroDivisors R) :
    ¬ Function.Injective (fun x : R => f * x) := by
  intro h
  exact hf ((chapter02_regular_element_iff_injective_multiplication R f).2 h)

/-!
The nodal example `Spec k[x,y]/(xy)` records both the zero-divisor failure and
the regular equation `x + y`.
-/

abbrev Chapter02NodePolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

abbrev Chapter02NodeRing (k : Type u) [CommRing k] :=
  Chapter02NodePolynomialRing k ⧸
    Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} :
      Set (Chapter02NodePolynomialRing k))

abbrev Chapter02NodeScheme (k : Type u) [CommRing k] : Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (Chapter02NodeRing k))

def chapter02NodeX (k : Type u) [CommRing k] : Chapter02NodeRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

def chapter02NodeY (k : Type u) [CommRing k] : Chapter02NodeRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

def chapter02NodeXPlusY (k : Type u) [CommRing k] : Chapter02NodeRing k :=
  chapter02NodeX k + chapter02NodeY k

theorem chapter02_node_equation_xy_zero (k : Type u) [CommRing k] :
    chapter02NodeX k * chapter02NodeY k = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.2
  exact Ideal.subset_span (by simp)

theorem chapter02_node_y_ne_zero (k : Type u) [Nontrivial k] [CommRing k] :
    chapter02NodeY k ≠ 0 := by
  intro hy
  let φ : Chapter02NodePolynomialRing k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k)
      (fun i => if i = (0 : Fin 2) then 0 else 1)
  have hgen : MvPolynomial.X 0 * MvPolynomial.X 1 ∈ RingHom.ker φ := by
    change φ (MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp [φ]
  have hker : Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} :
      Set (Chapter02NodePolynomialRing k)) ≤ RingHom.ker φ :=
    Ideal.span_le.2 (by simpa using hgen)
  have hy' : MvPolynomial.X 1 ∈
      Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} :
        Set (Chapter02NodePolynomialRing k)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hy
  have hzero : (1 : k) = 0 := by
    have := hker hy'
    simp [φ] at this
  exact one_ne_zero hzero

theorem chapter02_node_x_has_nonzero_annihilator
    (k : Type u) [Nontrivial k] [CommRing k] :
    ∃ y : Chapter02NodeRing k, y ≠ 0 ∧ chapter02NodeX k * y = 0 := by
  exact ⟨chapter02NodeY k, chapter02_node_y_ne_zero k,
    chapter02_node_equation_xy_zero k⟩

theorem chapter02_node_x_is_zero_divisor (k : Type u) [Nontrivial k] [CommRing k] :
    chapter02NodeX k ∉ nonZeroDivisors (Chapter02NodeRing k) := by
  intro hx
  exact chapter02_node_y_ne_zero k (hx.1 _ (chapter02_node_equation_xy_zero k))

theorem chapter02_node_x_not_effective (k : Type u) [Nontrivial k] [CommRing k] :
    ¬ Chapter02PrincipalEquationIsEffective (Chapter02NodeRing k) (chapter02NodeX k) := by
  exact chapter02_node_x_is_zero_divisor k

theorem chapter02_node_x_add_y_is_regular (k : Type u) [Field k] :
    chapter02NodeXPlusY k ∈ nonZeroDivisors (Chapter02NodeRing k) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hmem :
      MvPolynomial.X 0 * MvPolynomial.X 1 ∣
        (MvPolynomial.X 0 + MvPolynomial.X 1) * p := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [mul_comm] at hz
    change Ideal.Quotient.mk
      (Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1} :
        Set (Chapter02NodePolynomialRing k)))
      ((MvPolynomial.X 0 + MvPolynomial.X 1) * p) = 0 at hz
    exact hz
  have hxnot :
      ¬ (MvPolynomial.X 0 : Chapter02NodePolynomialRing k) ∣
        MvPolynomial.X 0 + MvPolynomial.X 1 := by
    intro h
    obtain ⟨q, hq⟩ := h
    let φ : Chapter02NodePolynomialRing k →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i => if i = (0 : Fin 2) then 0 else 1)
    have hzero : (1 : k) = 0 := by
      have := congrArg φ hq
      simp [φ] at this
    exact one_ne_zero hzero
  have hynot :
      ¬ (MvPolynomial.X 1 : Chapter02NodePolynomialRing k) ∣
        MvPolynomial.X 0 + MvPolynomial.X 1 := by
    intro h
    obtain ⟨q, hq⟩ := h
    let φ : Chapter02NodePolynomialRing k →+* k :=
      MvPolynomial.eval₂Hom (RingHom.id k)
        (fun i => if i = (1 : Fin 2) then 0 else 1)
    have hzero : (1 : k) = 0 := by
      have := congrArg φ hq
      simp [φ] at this
    exact one_ne_zero hzero
  have hxmul :
      (MvPolynomial.X 0 : Chapter02NodePolynomialRing k) ∣
        (MvPolynomial.X 0 + MvPolynomial.X 1) * p := by
    exact dvd_trans ⟨MvPolynomial.X 1, by ac_rfl⟩ hmem
  have hxp : (MvPolynomial.X 0 : Chapter02NodePolynomialRing k) ∣ p := by
    rcases MvPolynomial.X_dvd_mul_iff.mp hxmul with h | h
    · exact (hxnot h).elim
    · exact h
  have hymul :
      (MvPolynomial.X 1 : Chapter02NodePolynomialRing k) ∣
        (MvPolynomial.X 0 + MvPolynomial.X 1) * p := by
    exact dvd_trans ⟨MvPolynomial.X 0, by ac_rfl⟩ hmem
  have hyp : (MvPolynomial.X 1 : Chapter02NodePolynomialRing k) ∣ p := by
    rcases MvPolynomial.X_dvd_mul_iff.mp hymul with h | h
    · exact (hynot h).elim
    · exact h
  obtain ⟨q, hpq⟩ := hxp
  have hyx :
      ¬ (MvPolynomial.X 1 : Chapter02NodePolynomialRing k) ∣ MvPolynomial.X 0 := by
    rw [MvPolynomial.X_dvd_X]
    simp
  have hyq : (MvPolynomial.X 1 : Chapter02NodePolynomialRing k) ∣ q := by
    have h : (MvPolynomial.X 1 : Chapter02NodePolynomialRing k) ∣
        MvPolynomial.X 0 * q := by
      rw [← hpq]
      exact hyp
    rcases MvPolynomial.X_dvd_mul_iff.mp h with h | h
    · exact (hyx h).elim
    · exact h
  obtain ⟨r, hqr⟩ := hyq
  apply Ideal.Quotient.eq_zero_iff_mem.2
  apply Ideal.mem_span_singleton.2
  refine ⟨r, ?_⟩
  rw [hpq, hqr]
  ac_rfl

theorem chapter02_node_x_add_y_avoids_minimal_primes (k : Type u) [Field k] :
    ∀ p ∈ minimalPrimes (Chapter02NodeRing k),
      chapter02NodeXPlusY k ∉ p := by
  intro p hp hf
  exact (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hf hp)
    (chapter02_node_x_add_y_is_regular k)

theorem chapter02_node_x_add_y_is_effective (k : Type u) [Field k] :
    Chapter02PrincipalEquationIsEffective (Chapter02NodeRing k)
      (chapter02NodeXPlusY k) := by
  exact chapter02_node_x_add_y_is_regular k

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
