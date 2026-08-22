import LastLib.Book04AdelesAndIdeles.Chapter12.Core
import LastLib.Book04AdelesAndIdeles.Chapter10.Section01TheLocalNormAsAMultiplicativeDeterminant

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Set
open scoped BigOperators TensorProduct

/-! # Book 4, Chapter 12, §12.5: Split places and norm components -/

local instance chapter12LocalTensorProductRightAlgebra
    (K L Kv : Type*) [Field K] [Field L] [Field Kv]
    [Algebra K L] [Algebra K Kv] :
    Algebra Kv (L ⊗[K] Kv) :=
  Algebra.TensorProduct.rightAlgebra

def chapter12LocalSplitTensorShape
    (K L Kv : Type*) [Field K] [Field L] [Field Kv]
    [Algebra K L] [Algebra K Kv] (d : ℕ) : Prop :=
  Nonempty (chapter12TensorAlgEquiv K L Kv (Fin d → Kv))

structure Chapter12CompletelySplitPlaceData
    (K L Kv : Type*) [Field K] [Field L] [Field Kv]
    [Algebra K L] [Algebra K Kv] [FiniteDimensional K L]
    (d : ℕ) where
  degree_pos : 0 < d
  degree_eq_finrank : d = Module.finrank K L
  local_equiv : chapter12TensorAlgEquiv K L Kv (Fin d → Kv)

def chapter12SplitPlaceLocalNorm {Kv : Type*} [CommMonoid Kv] (d : ℕ) :
    (Fin d → Kv) →* Kv :=
  chapter12CoordinateProductNorm d

theorem chapter12_split_place_local_norm_apply
    {Kv : Type*} [CommMonoid Kv] (d : ℕ) (y : Fin d → Kv) :
    chapter12SplitPlaceLocalNorm d y = ∏ i, y i :=
  rfl

theorem chapter12_split_place_tensor_product_norm_formula
    (K L Kv : Type*) [Field K] [Field L] [Field Kv]
    [Algebra K L] [Algebra K Kv] [FiniteDimensional K L]
    (d : ℕ) (P : Chapter12CompletelySplitPlaceData K L Kv d)
    [FiniteDimensional Kv (L ⊗[K] Kv)] (y : Fin d → Kv) :
    Algebra.norm Kv (P.local_equiv.symm y) = ∏ i, y i := by
  sorry

theorem chapter12_split_place_local_norm_is_surjective
    {K L Kv : Type*} [Field K] [Field L] [Field Kv]
    [Algebra K L] [Algebra K Kv] [FiniteDimensional K L]
    (d : ℕ) (P : Chapter12CompletelySplitPlaceData K L Kv d) :
    Function.Surjective (fun y : Fin d → Kv =>
      chapter12SplitPlaceLocalNorm d y) := by
  sorry

theorem chapter12_split_place_norm_surjective_by_first_coordinate
    {K L Kv : Type*} [Field K] [Field L] [Field Kv]
    [Algebra K L] [Algebra K Kv] [FiniteDimensional K L]
    (d : ℕ) [NeZero d] (P : Chapter12CompletelySplitPlaceData K L Kv d) :
    ∀ b : Kv, ∃ y : Fin d → Kv,
      y 0 = b ∧ (∀ i : Fin d, i ≠ 0 → y i = 1) ∧
        chapter12SplitPlaceLocalNorm d y = b := by
  sorry

/-! ## The inert unramified comparison -/

structure Chapter12UnramifiedLocalNormBridge
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (degree : ℕ) (base_valuation : AddValuation K (WithTop ℤ))
    (extension_valuation : AddValuation E (WithTop ℤ)) where
  unramified_extension :
    LastLib.Book04AdelesAndIdeles.Chapter10.chapter10UnramifiedLocalExtension
      base_valuation extension_valuation
  unique_extension :
    ∀ w : AddValuation E (WithTop ℤ),
      base_valuation.IsEquiv (AddValuation.comap (algebraMap K E) w) →
        extension_valuation.IsEquiv w
  residue_degree_eq :
    degree =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        base_valuation extension_valuation unramified_extension.1

structure Chapter12UnramifiedLocalNormData
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.Unramified K E]
    [Algebra.IsSeparable K E] where
  degree : ℕ
  degree_eq_finrank : degree = Module.finrank K E
  base_valuation : AddValuation K (WithTop ℤ)
  extension_valuation : AddValuation E (WithTop ℤ)
  base_valuation_discrete :
    Valuation.IsRankOneDiscrete base_valuation.toValuation
  extension_valuation_discrete :
    Valuation.IsRankOneDiscrete extension_valuation.toValuation
  restriction_preserves_valuation :
    ∀ y : K,
      extension_valuation (algebraMap K E y) = base_valuation y
  norm_bridge : Chapter12UnramifiedLocalNormBridge K E degree
    base_valuation extension_valuation
  extension_values_are_integer :
    ∀ x : E, x ≠ 0 → ∃ z : ℤ, extension_valuation x = z

theorem chapter12_unramified_local_norm_bridge_formula
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.Unramified K E] [Algebra.IsSeparable K E]
    (P : Chapter12UnramifiedLocalNormData K E) :
    LastLib.Book04AdelesAndIdeles.Chapter10.chapter10NormValuationFormula
      K E P.base_valuation P.extension_valuation P.degree := by
  sorry

def chapter12UnramifiedNormValuationMultiple
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.Unramified K E] [Algebra.IsSeparable K E]
    (P : Chapter12UnramifiedLocalNormData K E) (x : E) : Prop :=
  ∃ z : ℤ,
    P.base_valuation (Algebra.norm K x) =
      (P.degree : WithTop ℤ) * (z : WithTop ℤ)

theorem chapter12_inert_unramified_norm_valuations_are_multiples
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.Unramified K E] [Algebra.IsSeparable K E]
    (P : Chapter12UnramifiedLocalNormData K E) {x : E} (hx : x ≠ 0) :
    chapter12UnramifiedNormValuationMultiple P x := by
  sorry

theorem chapter12_inert_unramified_norm_valuation_formula
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.Unramified K E] [Algebra.IsSeparable K E]
    (P : Chapter12UnramifiedLocalNormData K E) (x : E) (hx : x ≠ 0) :
    P.base_valuation (Algebra.norm K x) =
      (P.degree : WithTop ℤ) * P.extension_valuation x :=
  by sorry

/- The two local images are deliberately exposed as separate sets. -/
def chapter12SplitNormImage {Kv : Type*} [CommMonoid Kv] (d : ℕ) : Set Kv :=
  Set.range (chapter12SplitPlaceLocalNorm d)

def chapter12UnramifiedNormImage
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.Unramified K E] [Algebra.IsSeparable K E]
    (_P : Chapter12UnramifiedLocalNormData K E) : Set K :=
  {x | ∃ y : E, Algebra.norm K y = x}

theorem chapter12_split_norm_image_is_all
    {Kv : Type*} [CommMonoid Kv] (d : ℕ) [NeZero d] :
    chapter12SplitNormImage (Kv := Kv) d = (Set.univ : Set Kv) := by
  ext b
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hy⟩ := chapter12_coordinate_product_norm_surjective d b
    exact ⟨y, hy⟩

end
end LastLib.Book04AdelesAndIdeles.Chapter12
