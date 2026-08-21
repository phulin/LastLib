import LastLib.Book05LocalClassFieldTheory.Chapter03.Section04CyclicAlgebras

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open scoped BigOperators

/-! ## 3.5. The unramified cyclic computation -/

/- A reduction identification is the datum from which the arithmetic Frobenius upstairs is
   obtained.  The definition itself is inherited from Book 2, while this abbreviation gives it
   the chapter-3 name used in the cyclic-algebra statements. -/
noncomputable abbrev chapter03ArithmeticFrobenius
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l) : Gal(L/K) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius D

noncomputable abbrev chapter03GeometricFrobenius
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l) : Gal(L/K) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedGeometricFrobenius D

theorem chapter03_arithmetic_frobenius_is_inverse_of_geometric
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l) :
    chapter03GeometricFrobenius D = (chapter03ArithmeticFrobenius D)⁻¹ := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_unramified_geometric_frobenius_is_inverse D

theorem chapter03_arithmetic_frobenius_generates
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l) :
    chapter03CyclicGeneratorCondition K L (chapter03ArithmeticFrobenius D) := by
  intro τ
  obtain ⟨r, hr⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_unramified_arithmetic_frobenius_generates D τ
  exact ⟨r, hr⟩

/- The local normalization used in §3.5 is an integer-valued nonzero valuation.  Stating this
   interface explicitly prevents a general `WithTop ℤ` valuation from silently being treated as
   discrete at zero. -/
def chapter03IntegerValuedOnNonzero
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∀ x : K, x ≠ 0 → ∃ r : ℤ, v x = (r : WithTop ℤ)

theorem chapter03_unramified_norm_valuation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (hdegree : Module.finrank K L = n)
    (hfres : n =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (x : L) :
    vK (Algebra.norm K x) = (n : WithTop ℤ) * vL x := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_comparison_norm_valuation
    K L vK vL n hunram hunique hdegree hfres x

theorem chapter03_unramified_norm_valuation_divisible
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    (hdegree : Module.finrank K L = n)
    (hfres : n =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    (hdiscrete : chapter03IntegerValuedOnNonzero vL) (x : L) (hx : x ≠ 0) :
    ∃ r : ℤ, vK (Algebra.norm K x) = (((n : ℤ) * r : ℤ) : WithTop ℤ) := by
  sorry

theorem chapter03_unramified_units_are_norms
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    (_hdegree_n : Module.finrank K L = n)
    [Finite (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)]
    [Finite (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [Algebra (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [FiniteDimensional
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [Algebra.IsSeparable
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    (hdegree : Module.finrank K L =
      Module.finrank
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL))
    (hred : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
      vK vL
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL))
    (N : (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing vL)ˣ →*
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing vK)ˣ)
    (hnormunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormUnitLiftCompatibility
        K L vK vL N)
    (hnormred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormResidueCompatibility
        K L
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)
        vK vL
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL)
        1 N) :
    Set.SurjOn (Algebra.norm K (S := L))
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnitFiltration vL 0)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnitFiltration vK 0) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_comparison_units_are_norms
    K L vK vL hunram hdegree hred N hnormunit hnormred

theorem chapter03_unramified_uniformizer_not_a_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hn : 1 < n)
    (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (hdegree : Module.finrank K L = n)
    (hfres : n =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (π : K) (hπ : vK π = (1 : WithTop ℤ)) :
    ¬ ∃ x : L, Algebra.norm K x = π := by
  have hnorm :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormValuationFormula
        K L vK vL n := by
    intro x _
    exact chapter03_unramified_norm_valuation K L vK vL n hunram hunique hdegree hfres x
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_comparison_uniformizer_not_a_norm
    K L vK vL n hn hunram hnorm hdegree hfres π hπ

theorem chapter03_unramified_full_norm_image
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (π : K) (hπ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11IsUniformizer vK π)
    (hdegree : Module.finrank K L = n)
    (hfres : n =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)]
    [Algebra (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [FiniteDimensional
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [Algebra.IsSeparable
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    (hred : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
      vK vL
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL))
    (N : (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing vL)ˣ →*
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing vK)ˣ)
    (hnormunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormUnitLiftCompatibility
        K L vK vL N)
    (hnormred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormResidueCompatibility
        K L
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)
        vK vL
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL)
        1 N) :
    {x : K | ∃ y : L, y ≠ 0 ∧ x = Algebra.norm K y} =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValueUnitProductSet vK π n := by
  have hnorm :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormValuationFormula
        K L vK vL n := by
    intro x _
    exact chapter03_unramified_norm_valuation K L vK vL n hunram hunique hdegree hfres x
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_full_norm_image
    K L vK vL π n hunram hπ hnorm hdegree hfres hred N hnormunit hnormred

theorem chapter03_unramified_norm_quotient_index
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (π : K) (hπ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11IsUniformizer vK π)
    (hdegree : Module.finrank K L = n)
    (hfres : n =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)]
    [Algebra (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [FiniteDimensional
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [Algebra.IsSeparable
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    (hred : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
      vK vL
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL))
    (N : (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing vL)ˣ →*
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationRing vK)ˣ)
    (hnormunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormUnitLiftCompatibility
        K L vK vL N)
    (hnormred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormResidueCompatibility
        K L
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)
        vK vL
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL)
        1 N) :
    Nat.card (chapter03NormQuotient K L) = n := by
  have hnorm :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormValuationFormula
        K L vK vL n := by
    intro x _
    exact chapter03_unramified_norm_valuation K L vK vL n hunram hunique hdegree hfres x
  simpa [chapter03NormQuotient, chapter03NormSubgroup] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_norm_subgroup_index
      K L vK vL π n hunram hπ hnorm hdegree hfres hred N hnormunit hnormred)

def chapter03UniformizerUnit
    {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) : Kˣ :=
  Units.mk0 π hπ

def chapter03UniformizerClass
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (π : K) (hπ : π ≠ 0) : chapter03NormQuotient K L :=
  QuotientGroup.mk' (chapter03NormSubgroup K L) (chapter03UniformizerUnit π hπ)

theorem chapter03_uniformizer_class_mem_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (π : K) (hπ : π ≠ 0) :
    chapter03UniformizerClass K L π hπ = 1 ↔
      chapter03UniformizerUnit π hπ ∈ chapter03NormSubgroup K L := by
  simp [chapter03UniformizerClass]

/- The source's `ℤ/nℤ` is written multiplicatively here as `Multiplicative (ZMod n)` so that the
   quotient equivalence is a group equivalence.  Its distinguished element is the additive class
   of `1`. -/
structure Chapter03UnramifiedNormOrientation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (n : ℕ) (π : K) (hπ : π ≠ 0) where
  quotientEquiv : chapter03NormQuotient K L ≃* Multiplicative (ZMod n)
  uniformizer_maps_to_one :
    quotientEquiv (chapter03UniformizerClass K L π hπ) = Multiplicative.ofAdd 1
  uniformizer_generates :
    Subgroup.zpowers (chapter03UniformizerClass K L π hπ) = ⊤

theorem chapter03_uniformizer_class_generates
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (n : ℕ) (π : K) (hπ : π ≠ 0)
    (O : Chapter03UnramifiedNormOrientation K L n π hπ) :
    Subgroup.zpowers (chapter03UniformizerClass K L π hπ) = ⊤ :=
  O.uniformizer_generates

theorem chapter03_unramified_norm_quotient_equiv_zmod
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (n : ℕ) (hunram :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
        vK vL)
    (π : K) (hπ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11IsUniformizer vK π)
    (hdegree : Module.finrank K L = n)
    (hfres : n =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)]
    [Algebra (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [FiniteDimensional
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    [Algebra.IsSeparable
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueField vL)]
    (hred : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
      vK vL
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vK)
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueMap vL)) :
    Nonempty (Chapter03UnramifiedNormOrientation K L n π hπ.1) := by
  sorry

/- The normalization convention is recorded by using the same distinguished generator of
   `Multiplicative (ZMod n)` on the norm quotient and on the Galois group. -/
structure Chapter03UnramifiedFrobeniusOrientation
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l)
    (n : ℕ) (π : K) (hπ : π ≠ 0) where
  normOrientation : Chapter03UnramifiedNormOrientation K L n π hπ
  galoisEquiv : Gal(L/K) ≃* Multiplicative (ZMod n)
  arithmetic_maps_to_one :
    galoisEquiv (chapter03ArithmeticFrobenius D) = Multiplicative.ofAdd 1

theorem chapter03_unramified_frobenius_orientation_exists
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l)
    (n : ℕ) (π : K) (hπ : π ≠ 0)
    (hO : Nonempty (Chapter03UnramifiedNormOrientation K L n π hπ))
    (hcyc : chapter03CyclicExtension K L n (chapter03ArithmeticFrobenius D)) :
    Nonempty (Chapter03UnramifiedFrobeniusOrientation D n π hπ) := by
  obtain ⟨O⟩ := hO
  have hncard : Nat.card (Gal(L/K)) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hcyc.1]
  let e : Gal(L/K) ≃* Multiplicative (ZMod n) :=
    (zmodMulEquivOfGenerator (G := Gal(L/K))
      (g := chapter03ArithmeticFrobenius D) hcyc.2 hncard).symm
  refine ⟨{ normOrientation := O, galoisEquiv := e, arithmetic_maps_to_one := ?_ }⟩
  exact zmodMulEquivOfGenerator_symm_apply_generator
    (G := Gal(L/K)) (g := chapter03ArithmeticFrobenius D) hcyc.2 hncard

theorem chapter03_geometric_frobenius_maps_to_inverse_generator
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l)
    (n : ℕ) (π : K) (hπ : π ≠ 0)
    (O : Chapter03UnramifiedFrobeniusOrientation D n π hπ) :
    O.galoisEquiv (chapter03GeometricFrobenius D) =
      (Multiplicative.ofAdd 1)⁻¹ := by
  rw [chapter03_arithmetic_frobenius_is_inverse_of_geometric D, map_inv,
    O.arithmetic_maps_to_one]

theorem chapter03_cyclic_algebra_split_over_extension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (C : chapter03CyclicAlgebra K L n σ a) :
    chapter03ScalarExtensionSplits K L C.carrier C.algebraL n :=
  C.split_by_L

/- The source treats the degree-one case separately; the hypothesis `hn` records the nontrivial
   case in the theorem below. -/
theorem chapter03_unramified_cyclic_algebra_basic_nontrivial
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l)
    (n : ℕ) (hcyc : chapter03CyclicExtension K L n (chapter03ArithmeticFrobenius D))
    (hn : 1 < n) (π : K) (hπ : π ≠ 0)
    (C : chapter03CyclicAlgebra K L n (chapter03ArithmeticFrobenius D)
      (chapter03UniformizerUnit π hπ))
    (hnotnorm : ¬ ∃ x : L, Algebra.norm K x = π) :
    chapter03ScalarExtensionSplits K L C.carrier C.algebraL n ∧
      ¬ chapter03CyclicAlgebraSplitsOverBase K L n (chapter03ArithmeticFrobenius D)
        (chapter03UniformizerUnit π hπ) C := by
  constructor
  · exact C.split_by_L
  · have _ : 1 < n := hn
    intro hsplit
    apply hnotnorm
    obtain ⟨u, hu⟩ :=
      (chapter03_mem_norm_subgroup_iff K L
        (chapter03UniformizerUnit π hπ)).mp
        ((chapter03_cyclic_algebra_split_iff_norm K L n
          (chapter03ArithmeticFrobenius D) (chapter03UniformizerUnit π hπ)
          hcyc C).mp hsplit)
    refine ⟨(u : L), ?_⟩
    have hu' : (chapter03NormUnit K L u : K) =
        (chapter03UniformizerUnit π hπ : K) :=
      congrArg (fun z : Kˣ => (z : K)) hu
    rw [chapter03_norm_unit_apply] at hu'
    change Algebra.norm K (u : L) = π at hu'
    exact hu'

/- Norms in a tower are the compatibility relation needed to transport the chosen orientation of
   a fundamental class through successive unramified extensions. -/
theorem chapter03_norm_transitive_in_tower
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] (x : L) :
    Algebra.norm K (S := L) x =
      Algebra.norm K (S := M) (Algebra.norm M (S := L) x) := by
  exact (Algebra.norm_norm (R := K) (S := M) (a := x)).symm

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
