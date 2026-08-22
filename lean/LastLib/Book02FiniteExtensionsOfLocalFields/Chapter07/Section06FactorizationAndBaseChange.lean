import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section05ExamplesBothCharacteristics
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Function
open Polynomial
open scoped BigOperators TensorProduct WithZero
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter09

noncomputable section

universe uK uK' uL uk uk' ul

-- The tensor product has a canonical right-factor algebra structure, but
-- Mathlib keeps it local to avoid ambiguity with the left-factor action.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! # Book 2, Chapter 7, §7.6: unramified factorization and base change -/

/-- A finite family of distinct monic irreducible residue factors. -/
structure Chapter07SeparableResidueFactorization
    (k : Type*) [Field k] (r : ℕ) where
  polynomial : k[X]
  factors : Fin r → k[X]
  monic : ∀ i, (factors i).Monic
  irreducible : ∀ i, Irreducible (factors i)
  separable : ∀ i, (factors i).Separable
  distinct : Pairwise (fun i j => factors i ≠ factors j)
  product : polynomial = ∏ i, factors i

/-- A chosen coefficient lift of a residue factorization. -/
structure Chapter07LiftedFactorization
    (A k : Type*) [CommRing A] [Field k] (res : A →+* k)
    (r : ℕ) (F : Chapter07SeparableResidueFactorization k r) (g : A[X]) where
  factors : Fin r → A[X]
  monic : ∀ i, (factors i).Monic
  pairwise_coprime : Pairwise (fun i j =>
    IsCoprime (Ideal.span ({factors i} : Set A[X]))
      (Ideal.span ({factors j} : Set A[X])))
  reductions : ∀ i, (factors i).map res =
    F.factors i
  product : g = ∏ i, factors i
  reduced_product : g.map res = ∏ i, F.factors i

/-- Coprime residue factors lift uniquely to coprime monic factors over a
henselian local ring. -/
theorem chapter07_separable_factorization_lifts_uniquely
    {A k : Type*} [CommRing A] [Field k] [HenselianLocalRing A]
    (res : A →+* k) (r : ℕ) (F : Chapter07SeparableResidueFactorization k r)
    (g : A[X]) (hgmonic : g.Monic)
    (hgred : g.map res = ∏ i, F.factors i)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A) :
    ∃ G : Chapter07LiftedFactorization A k res r F g,
      ∀ H : Chapter07LiftedFactorization A k res r F g,
        H.factors = G.factors := by
  classical
  have hpair : PairwiseCoprimeFamily F.factors := by
    intro i j hij
    apply (F.irreducible i).coprime_iff_not_dvd.mpr
    intro hdvd
    exact F.distinct hij (eq_of_monic_of_associated (F.monic i) (F.monic j)
      ((F.irreducible i).associated_of_dvd (F.irreducible j) hdvd))
  let P : ∀ (ι : Type) [Fintype ι], Prop := fun ι _ =>
    ∀ (f : A[X]) (f₀ : ι → k[X]), f.Monic →
      (∀ i, (f₀ i).Monic) → PairwiseCoprimeFamily f₀ →
      f.map res = ∏ i, f₀ i →
      ∃! lifts : ι → A[X],
        ((∀ i, (lifts i).Monic ∧ (lifts i).map res = f₀ i) ∧
          f = ∏ i, lifts i)
  have hP : P (Fin r) := by
    apply Fintype.induction_empty_option (P := fun ι _ => P ι)
    · intro α β inst equiv IH f f₀ hf hmonic hcop hred
      let _ : Fintype α := Fintype.ofEquiv β equiv.symm
      let f₀' : α → k[X] := fun a => f₀ (equiv a)
      obtain ⟨lifts, hlifts, huniq⟩ := IH f f₀' hf
        (fun a => hmonic (equiv a))
        (by
          intro a b hab
          apply hcop
          exact fun h => hab (equiv.injective h))
        (by simpa [f₀'] using hred.trans (equiv.prod_comp f₀).symm)
      let lifts' : β → A[X] := fun b => lifts (equiv.symm b)
      refine ⟨lifts', ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro b
          simpa [lifts', f₀'] using hlifts.1 (equiv.symm b)
        · calc
            f = ∏ a, lifts a := hlifts.2
            _ = ∏ b, lifts' b := by
              rw [← equiv.prod_comp lifts']
              simp [lifts']
      · intro other hother
        let other' : α → A[X] := fun a => other (equiv a)
        have heq : other' = lifts := huniq other' (by
          refine ⟨?_, ?_⟩
          · intro a
            simpa [other', f₀'] using hother.1 (equiv a)
          · calc
              f = ∏ b, other b := hother.2
              _ = ∏ a, other' a := by
                rw [equiv.prod_comp])
        funext b
        have heval := congrFun heq (equiv.symm b)
        simpa [other', lifts'] using heval
    · intro f f₀ hf _hmonic _hcop hred
      have hf1 : f = 1 := by
        apply hf.natDegree_eq_zero.mp
        calc
          f.natDegree = (f.map res).natDegree := (hf.natDegree_map res).symm
          _ = 0 := by simpa using congrArg Polynomial.natDegree hred
      refine ⟨fun i => PEmpty.elim i, ?_, ?_⟩
      · exact ⟨fun i => PEmpty.elim i, by simp [hf1]⟩
      · intro other _hother
        funext i
        exact PEmpty.elim i
    · intro α inst IH f f₀ hf hmonic hcop hred
      let g₀ : k[X] := f₀ none
      let h₀ : k[X] := ∏ a, f₀ (some a)
      have hg₀ : g₀.Monic := hmonic none
      have hh₀ : h₀.Monic := monic_prod_of_monic Finset.univ _
        (fun a _ha => hmonic (some a))
      have hcoph : IsCoprime g₀ h₀ := by
        apply IsCoprime.prod_right
        intro a _ha
        exact hcop (by simp)
      have hred' : f.map res = g₀ * h₀ := by
        simpa [g₀, h₀, Fintype.prod_option] using hred
      obtain ⟨gh, hgh, hghuniq⟩ :=
        henselian_lifts_coprime_factorization_along_residue_map
          res hres_surjective hres_kernel f g₀ h₀ hf hg₀ hh₀ hcoph hred'
      obtain ⟨rest, hrest, hrestuniq⟩ := IH gh.2 (fun a => f₀ (some a))
        hgh.2.1 (fun a => hmonic (some a))
        (by
          intro a b hab
          exact hcop (fun h => hab (Option.some.inj h))) hgh.2.2.2.1
      let lifts : Option α → A[X]
        | none => gh.1
        | some a => rest a
      refine ⟨lifts, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro o
          cases o with
          | none => simpa [lifts, g₀] using ⟨hgh.1, hgh.2.2.1⟩
          | some a => simpa [lifts] using hrest.1 a
        · calc
            f = gh.1 * gh.2 := hgh.2.2.2.2
            _ = gh.1 * ∏ a, rest a := by rw [hrest.2]
            _ = ∏ o, lifts o := by rw [Fintype.prod_option]
      · intro other hother
        let otherTail : α → A[X] := fun a => other (some a)
        have htailmonic : (∏ a, otherTail a).Monic :=
          monic_prod_of_monic Finset.univ _ (fun a _ha => (hother.1 (some a)).1)
        have htailred : (∏ a, otherTail a).map res = h₀ := by
          simp only [Polynomial.map_prod]
          apply Finset.prod_congr rfl
          intro a _ha
          exact (hother.1 (some a)).2
        have hotherprod : f = other none * ∏ a, otherTail a := by
          rw [hother.2, Fintype.prod_option]
        have hghEq : (other none, ∏ a, otherTail a) = gh :=
          hghuniq _ ⟨(hother.1 none).1, htailmonic, (hother.1 none).2,
            htailred, hotherprod⟩
        have htailprod : gh.2 = ∏ a, otherTail a :=
          (congrArg Prod.snd hghEq).symm
        have hrestEq : otherTail = rest := hrestuniq otherTail
          ⟨fun a => hother.1 (some a), htailprod⟩
        funext o
        cases o with
        | none => simpa [lifts] using congrArg Prod.fst hghEq
        | some a => simpa [lifts, otherTail] using congrFun hrestEq a
  obtain ⟨lifts, hlifts, huniq⟩ := hP g F.factors hgmonic F.monic hpair hgred
  let G : Chapter07LiftedFactorization A k res r F g :=
    { factors := lifts
      monic := fun i => (hlifts.1 i).1
      pairwise_coprime := by
        intro i j hij
        apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
        exact coprime_of_coprime_reductions_along_residue_map
          res hres_surjective hres_kernel (hlifts.1 i).1 (hlifts.1 j).1
            (hlifts.1 i).2 (hlifts.1 j).2 (hpair hij)
      reductions := fun i => (hlifts.1 i).2
      product := hlifts.2
      reduced_product := hgred }
  refine ⟨G, ?_⟩
  intro H
  exact huniq H.factors ⟨fun i => ⟨H.monic i, H.reductions i⟩, H.product⟩

/-- The quotient of a separable product splits as the product of its field
factors. -/
theorem chapter07_separable_quotient_is_product
    {K : Type*} [Field K] (g : K[X]) {r : ℕ} (gᵢ : Fin r → K[X])
    (hproduct : g = ∏ i, gᵢ i)
    (hirreducible : ∀ i, Irreducible (gᵢ i))
    (hpairwise : Pairwise (fun i j => IsCoprime (Ideal.span ({gᵢ i} : Set K[X]))
      (Ideal.span ({gᵢ j} : Set K[X])))) :
    Nonempty (AdjoinRoot g ≃+* (∀ i, AdjoinRoot (gᵢ i))) ∧
      ∀ i, IsField (AdjoinRoot (gᵢ i)) := by
  classical
  have hcop : Pairwise (IsCoprime on
      fun i : Fin r => Ideal.span ({gᵢ i} : Set K[X])) := by
    intro i j hij
    exact hpairwise hij
  have hideal :
      (Ideal.span ({g} : Set K[X])) =
        ⨅ i : Fin r, Ideal.span ({gᵢ i} : Set K[X]) := by
    calc
      Ideal.span ({g} : Set K[X]) =
          Ideal.span ({∏ i : Fin r, gᵢ i} : Set K[X]) := by rw [hproduct]
      _ = ∏ i : Fin r, Ideal.span ({gᵢ i} : Set K[X]) := by
        symm
        simpa using
          (Ideal.prod_span_singleton (Finset.univ : Finset (Fin r)) gᵢ)
      _ = ⨅ i : Fin r, Ideal.span ({gᵢ i} : Set K[X]) := by
        simpa using
          (Ideal.prod_eq_iInf_of_pairwise_isCoprime
            (s := (Finset.univ : Finset (Fin r)))
            (J := fun i : Fin r => Ideal.span ({gᵢ i} : Set K[X]))
            (by
              intro i hi j hj hij
              exact hcop hij))
  let e : AdjoinRoot g ≃+* (∀ i, AdjoinRoot (gᵢ i)) :=
    (Ideal.quotEquivOfEq hideal).trans
      (Ideal.quotientInfRingEquivPiQuotient
        (fun i : Fin r => Ideal.span ({gᵢ i} : Set K[X])) hcop)
  refine ⟨⟨e⟩, ?_⟩
  intro i
  let _ : Fact (Irreducible (gᵢ i)) := ⟨hirreducible i⟩
  exact Field.toIsField _

/-- The local-field data attached to one lifted factor.  The factor index is
kept in the type so that a later proof can identify the residue polynomial,
residue degree, and unramified profile without choosing a ring homomorphism
by classical choice. -/
structure Chapter07SeparableFactorResidueField
    (A K k l L : Type*) [CommRing A] [Field K] [Field k] [Field l] [Field L]
    [Algebra A K] [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    {r : ℕ} (res : A →+* k)
    (F : Chapter07SeparableResidueFactorization k r)
    (g : A[X]) (G : Chapter07LiftedFactorization A k res r F g)
    (i : Fin r) [Algebra A L] [IsScalarTower A K L] where
  profile : Chapter07FiniteLocalExtensionData K L k l
  unramified : Chapter07UnramifiedExtension profile
  residue_degree : profile.residueDegree = (F.factors i).natDegree
  residue_separable : Chapter07ResidueExtensionIsSeparable k l
  integralModel : Subalgebra A L
  integralModel_finite : Module.Finite A integralModel
  residueMap : integralModel →+* l
  residueMap_surjective : Function.Surjective residueMap
  residueIdeal : Ideal integralModel
  residueMap_kernel : RingHom.ker residueMap = residueIdeal
  integralModel_fractionRing : IsFractionRing integralModel L
  integralModel_etale : Algebra.Etale A integralModel
  /-- The displayed local field is the field factor represented by the
  selected lifted residue factor, rather than an unrelated field with the
  same numerical profile. -/
  factor_quotient_equiv : Nonempty
    (L ≃ₐ[K]
      Chapter07LiftedPolynomialQuotient K
        (chapter07LiftedPolynomial (G.factors i)))
  residueMap_compatible :
    residueMap.comp (algebraMap A integralModel) =
      (algebraMap k l).comp res

/-- A chosen residue-field shadow of an intermediate unramified extension. -/
structure Chapter07IntermediateResidueShadow
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    where
  residue : IntermediateField k κ
  [residueFinite : FiniteDimensional k residue]
  profile : Chapter07FiniteLocalExtensionData K E k residue
  actual :
    Chapter07ActualUnramifiedIntermediateData K Ω k κ E residue profile

/- A residue shadow is defined only on the witnessed unramified carriers.  A
global lattice map on all intermediate fields would incorrectly assign residue
fields to ramified or otherwise unvalued intermediate extensions. -/
structure Chapter07ResidueShadowFunctoriality
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ] where
  classification :
    Chapter07CanonicalUnramifiedClassification K Ω k κ

/-- The residue-field equalities for composita and intersections, with the
chosen reduction equivalence on witnessed unramified carriers made explicit. -/
theorem chapter07_unramified_residue_compositum_and_intersection
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ)
    (R : Chapter07ResidueShadowFunctoriality K Ω k κ) :
    (∃ G : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
      G.1 = chapter07CanonicalUnramifiedCompositum E F ∧
        (R.classification.reduction G).1 =
          chapter07CanonicalResidueCompositum
            (R.classification.reduction E) (R.classification.reduction F)) ∧
      (∃ G : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
        G.1 = chapter07CanonicalUnramifiedIntersection E F ∧
          (R.classification.reduction G).1 =
              chapter07CanonicalResidueIntersection
                (R.classification.reduction E) (R.classification.reduction F)) := by
  exact ⟨R.classification.compositum_preserved E F,
    R.classification.intersection_preserved E F⟩

/-- The residue tensor product is finite étale over the changed residue field,
hence a finite product of separable fields. -/
theorem chapter07_residue_tensor_product_is_separable_product
    {k k' l : Type*} [Field k] [Field k'] [Field l]
    [Algebra k k'] [Algebra k l] [FiniteDimensional k l]
    [Algebra.IsSeparable k l] :
    Chapter07FiniteEtaleExtension k' (l ⊗[k] k') := by
    exact
    (letI : Module.Finite k' (k' ⊗[k] l) :=
        Module.Finite.base_change k k' l
     let e : k' ⊗[k] l ≃ₐ[k'] l ⊗[k] k' :=
       Algebra.TensorProduct.commRight k k' l
     letI : Module.Finite k' (l ⊗[k] k') :=
       Module.Finite.of_surjective e.toLinearMap e.surjective
     letI : Module.FinitePresentation k l :=
        Module.finitePresentation_of_finite k l
     letI : Algebra.FinitePresentation k l := inferInstance
     letI : Algebra.FormallyEtale k l :=
       Algebra.FormallyEtale.of_isSeparable k l
     letI : Algebra.Etale k l := ⟨inferInstance, inferInstance⟩
     letI : Algebra.Etale k' (k' ⊗[k] l) := inferInstance
     letI : Algebra.Etale k' (l ⊗[k] k') :=
       Algebra.Etale.of_equiv e
     ⟨inferInstance, inferInstance⟩)

/-- A finite product of unramified factors after scalar extension. -/
structure Chapter07UnramifiedScalarExtensionProduct
    (K : Type uK) (K' : Type uK') (L : Type uL)
    (k : Type uk) (k' : Type uk') (l : Type ul)
    [Field K] [Field K'] [Field L]
    [Field k] [Field k'] [Field l] [Algebra K K'] [Algebra K L]
    [Algebra k k'] [Algebra k l] (r : ℕ)
    (vK' : Valuation K' ℤᵐ⁰)
    (baseResidueIdentification : Chapter10ResidueField vK' ≃+* k')
    [FiniteDimensional K K'] [FiniteDimensional K L]
    [FiniteDimensional k l] where
  factor : Fin r → Type (max uK (max uK' uL))
  [factorField : ∀ i, Field (factor i)]
  [factorAlgebra : ∀ i, Algebra K' (factor i)]
  [factorFinite : ∀ i, FiniteDimensional K' (factor i)]
  residue : Fin r → Type (max uk (max uk' ul))
  [residueField : ∀ i, Field (residue i)]
  [residueAlgebra : ∀ i, Algebra k' (residue i)]
  [residueFinite : ∀ i, FiniteDimensional k' (residue i)]
  profile : ∀ i,
    Chapter07FiniteLocalExtensionData K' (factor i) k' (residue i)
  unramified : ∀ i, Chapter07UnramifiedExtension (profile i)
  factorValuation : ∀ i, Valuation (factor i) ℤᵐ⁰
  factorValuation_extension : ∀ i,
    vK'.IsEquiv
      ((factorValuation i).comap (algebraMap K' (factor i)))
  factorResidueIdentification : ∀ i,
    Chapter10ResidueField (factorValuation i) ≃+* (residue i)
  factorResidueMap : ∀ i,
    Chapter10ResidueField vK' →+*
      Chapter10ResidueField (factorValuation i)
  factorResidueMap_compatible : ∀ i,
    (factorResidueIdentification i).toRingHom.comp (factorResidueMap i) =
      (algebraMap k' (residue i)).comp baseResidueIdentification.toRingHom
  factorExtensionData : ∀ i,
    Chapter10HeterogeneousExtensionData vK' (factorValuation i)
      (factorValuation_extension i)
  factorProfile_ramificationIndex : ∀ i,
    (profile i).ramificationIndex = (factorExtensionData i).ramificationIndex
  factorProfile_residueDegree : ∀ i,
    (profile i).residueDegree = (factorExtensionData i).residueDegree
  /-- The residue tensor product has the same factor decomposition as the
  scalar-extended field algebra.  This ties the displayed residue fields to
  the residue-side algebra rather than leaving them as unrelated profiles. -/
  residueProductEquiv : Nonempty
    (l ⊗[k] k' ≃ₐ[k'] (∀ i, residue i))
  productEquiv : Nonempty
    (L ⊗[K] K' ≃ₐ[K'] (∀ i, factor i))

/-- Hensel lifting of the residue idempotents gives the product decomposition
of an unramified scalar extension. -/
theorem chapter07_unramified_scalar_extension_is_product
    {K K' L k k' l : Type*} [Field K] [Field K'] [Field L]
    [Field k] [Field k'] [Field l] [Algebra K K'] [Algebra K L]
    [Algebra k k'] [Algebra k l] [FiniteDimensional K K']
    [FiniteDimensional K L] [FiniteDimensional k l]
    [Algebra.IsSeparable k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07UnramifiedExtension E)
    (hLseparable : Algebra.IsSeparable K L)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (baseResidueIdentification : Chapter10ResidueField vK ≃+* k)
    (extensionResidueIdentification : Chapter10ResidueField vL ≃+* l)
    (residueMap : Chapter10ResidueField vK →+* Chapter10ResidueField vL)
    (residueMap_compatible :
      extensionResidueIdentification.toRingHom.comp residueMap =
        (algebraMap k l).comp baseResidueIdentification.toRingHom)
    (vK' : Valuation K' ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK']
    (baseChangeValuation : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (baseChangeComplete :
      IsAdicComplete (IsLocalRing.maximalIdeal vK'.valuationSubring)
        vK'.valuationSubring)
    (baseChangeResidueIdentification : Chapter10ResidueField vK' ≃+* k')
    (d : Chapter10HeterogeneousExtensionData vK vL hext)
    (hprofile : E.ramificationIndex = d.ramificationIndex ∧
      E.residueDegree = d.residueDegree) :
    ∃ r : ℕ, Nonempty
      (Chapter07UnramifiedScalarExtensionProduct K K' L k k' l r vK'
        baseChangeResidueIdentification) := by
  /-
  Proof roadmap (generic/residue factor compatibility is the missing bridge).

  1. Give both tensor products their local right-factor algebra structures.
     Obtain a finite product of generic field factors from
     `Chapter03.chapter03_separable_scalar_extension_is_finite_reduced` and
     `Chapter03.chapter03_separable_scalar_extension_has_field_factors` in
     `Book02FiniteExtensionsOfLocalFields/Chapter03/Section04ScalarExtensionOfALocalField.lean`.
     Equivalently, apply `Algebra.Etale.iff_exists_algEquiv_prod` from
     `Mathlib/RingTheory/Etale/Field.lean`.  Replace its finite index type `I`
     by `Fin r`, where `r := Fintype.card I`, using `Fintype.equivFin` and
     `AlgEquiv.piCongrLeft'`.  The carrier universes in the structure above
     deliberately match the `ULift` construction already used by the Chapter
     3 theorem.
  2. For each projection of the generic product equivalence, use
     `Algebra.TensorProduct.includeLeft` and the projection `Pi.evalAlgHom` to
     install the compatible `K`- and `L`-algebra maps on the factor.  This is
     the `chapter03ScalarExtensionFieldFactor` witness required by
     `Chapter03.chapter03_unramified_scalar_extension_field_factor_is_unramified`.
     Finite-dimensionality over `K'` comes with the Chapter 3 decomposition;
     hence `Algebra.IsAlgebraic K' (factor i)` is available.
  3. Apply
     `Chapter03.chapter03_complete_factor_has_unique_local_valuation` to `vK'`
     and each factor.  Choose its heterogeneous extension, then normalize its
     cyclic value group to `ℤᵐ⁰`; record the resulting valuation as
     `factorValuation i` and its restriction equivalence as
     `factorValuation_extension i`.  Build `factorExtensionData i` with
     `Chapter10HeterogeneousExtensionData`.  The needed normalization lemma is
     not currently exposed by Chapter 10/12; it should say that a finite
     extension of a complete `ℤᵐ⁰`-valued rank-one discrete field admits an
     equivalent extending valuation valued in `ℤᵐ⁰`.
  4. Define `residue i := Chapter10ResidueField (factorValuation i)`, initially
     with identity `factorResidueIdentification`, and use
     `Chapter10ResidueFieldMap vK' (factorValuation i)` for
     `factorResidueMap`.  Its compatibility with the base identification is
     then definitional after transporting the `k'`-algebra structure.  Define
     each numerical profile from its `Chapter10HeterogeneousExtensionData`;
     the Chapter 3 unramified-factor theorem supplies ramification index one
     and residue separability, while the Chapter 10 residue-degree definition
     supplies the two profile equalities.
  5. The essential missing theorem must lift the primitive idempotents of
     `l ⊗[k] k'` across the integral models and identify their generic fibers
     with the factors chosen in step 1.  Its output should use the *same* `I`
     and provide both
       `l ⊗[k] k' ≃ₐ[k'] (∀ i, Chapter10ResidueField (factorValuation i))`
     and `L ⊗[K] K' ≃ₐ[K'] (∀ i, factor i)`.
     Assemble these as `residueProductEquiv` and `productEquiv` and package the
     fields, valuations, profiles, and maps into the structure.

  Sufficiency check: `baseChangeComplete` gives the Henselian base;
  `baseChangeValuation` transfers the original valuation branch to `K'`;
  `hext`, the two residue identifications, and `residueMap_compatible` identify
  the old residue extension with `k → l`; `hprofile` ties the numerical profile
  to that actual branch; and `hLseparable` makes the generic tensor product
  finite reduced.  No extra residue-map hypothesis is needed.  However,
  independent applications of `Algebra.Etale.iff_exists_algEquiv_prod` on the
  generic and residue tensor products are a dead end: they do not identify
  their index sets or corresponding factors.  The idempotent-lifting bridge
  in step 5 is required.
  -/
  sorry

theorem chapter07_galois_over_intersection_linearly_disjoint
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (K₁ K₂ : IntermediateField K Ω)
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    [IsGalois (↥(K₁ ⊓ K₂))
      (↥(IntermediateField.extendScalars
        (F := K₁ ⊓ K₂) (E := K₁) inf_le_left))] :
    (IntermediateField.extendScalars
      (F := K₁ ⊓ K₂) (E := K₁) inf_le_left).LinearDisjoint
      (IntermediateField.extendScalars
        (F := K₁ ⊓ K₂) (E := K₂) inf_le_right) := by
  let F := K₁ ⊓ K₂
  let E₁ := IntermediateField.extendScalars
    (F := F) (E := K₁) inf_le_left
  let E₂ := IntermediateField.extendScalars
    (F := F) (E := K₂) inf_le_right
  let : Algebra K E₁ := Algebra.compHom E₁ (algebraMap K F)
  let : Algebra K E₂ := Algebra.compHom E₂ (algebraMap K F)
  let : IsScalarTower K F E₁ := IsScalarTower.of_algebraMap_eq (by
    intro x
    rfl)
  let : IsScalarTower K F E₂ := IsScalarTower.of_algebraMap_eq (by
    intro x
    rfl)
  let : Module.Finite K E₁ := by
    change Module.Finite K K₁
    infer_instance
  let : Module.Finite K E₂ := by
    change Module.Finite K K₂
    infer_instance
  let : Module.Finite F E₁ :=
    Module.Finite.of_restrictScalars_finite K F E₁
  let : Module.Finite F E₂ :=
    Module.Finite.of_restrictScalars_finite K F E₂
  change E₁.LinearDisjoint E₂
  apply (IntermediateField.LinearDisjoint.iff_inf_eq_bot).2
  dsimp [E₁, E₂, F]
  rw [IntermediateField.extendScalars_inf,
    IntermediateField.extendScalars_self]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
