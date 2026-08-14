import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section03FourKindsOfNormAssertion
import LastLib.Book06GlobalClassFieldTheory.Chapter09.Section01TheKnotBetweenLocalAndGlobalNorms

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

universe uK uL uV uKV uAV

/-!
At a split place the local algebra is a finite product.  The product norm is
recorded by an equivalence of multiplicative monoids together with the factor
norm; this keeps the construction independent of a particular completion
implementation.
-/
structure Chapter09SplitPlaceNormData
    (V : Type uV) (K_v : V → Type uKV) (A_v : V → Type uAV)
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)] where
  splitPlace : V → Prop
  factorCount : V → ℕ
  factorCount_pos : ∀ v, splitPlace v → 0 < factorCount v
  factor : ∀ v, Fin (factorCount v) → Type (max uKV uAV)
  [factorMonoid : ∀ v i, Monoid (factor v i)]
  productEquiv : ∀ v, splitPlace v →
    (A_v v) ≃* (∀ i, factor v i)
  factorNorm : ∀ v, (∀ i, factor v i)ˣ →* (K_v v)ˣ
  localNorm : ∀ v, (A_v v)ˣ →* (K_v v)ˣ
  localNorm_eq_product : ∀ v (h : splitPlace v),
    localNorm v =
      (factorNorm v).comp (Units.map (productEquiv v h).toMonoidHom)

attribute [instance] Chapter09SplitPlaceNormData.factorMonoid

theorem chapter09_split_place_local_norm_is_product
    {V : Type*} {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (P : Chapter09SplitPlaceNormData V K_v A_v)
    (v : V) (h : P.splitPlace v) :
    P.localNorm v =
      (P.factorNorm v).comp (Units.map (P.productEquiv v h).toMonoidHom) :=
  P.localNorm_eq_product v h

/-!
Mathlib currently supplies the category of central simple algebras but not the
cyclic-algebra construction or the number-field Brauer invariant sequence.
This is the book-facing interface for those two canonical constructions.  The substantive split
and local--global assertions are theorem-level interfaces below rather than fields of the input
record, so the Hasse norm theorem cannot be discharged merely by packaging its conclusion as data.
-/
def chapter09CsaIsSplit {K : Type uK} [Field K] (A : CSA.{uK, uK} K) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/- LOCAL_DEPENDENCY_GUESS: construct the cyclic algebra attached to a cyclic
extension and identify its split locus with the field norm subgroup. -/
structure Chapter09CyclicNormData
    (K : Type uK) (L : Type uL) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))] where
  places : Type uK
  K_v : places → Type uL
  A_v : places → Type uL
  [localFieldMonoid : ∀ v, Monoid (K_v v)]
  [localAlgebraMonoid : ∀ v, Monoid (A_v v)]
  baseEmbedding : ∀ v, Kˣ →* (K_v v)ˣ
  localNorm : ∀ v, (A_v v)ˣ →* (K_v v)ˣ
  splitPlaceData : Chapter09SplitPlaceNormData places K_v A_v
  splitPlaceData_localNorm : ∀ v, splitPlaceData.localNorm v = localNorm v
  cyclicAlgebra : Kˣ → CSA.{uK, uK} K
  localSplit : places → CSA.{uK, uK} K → Prop

attribute [instance] Chapter09CyclicNormData.localFieldMonoid
  Chapter09CyclicNormData.localAlgebraMonoid

def chapter09CyclicEverywhereLocalNorm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) : Prop :=
  ∀ v, P.baseEmbedding v a ∈ (P.localNorm v).range

theorem chapter09_cyclic_algebra_split_iff_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) :
    chapter09CsaIsSplit (P.cyclicAlgebra a) ↔
      a ∈ chapter09FieldNormSubgroup K L := by
  sorry

theorem chapter09_cyclic_algebra_local_split_iff_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) (v : P.places) :
    P.localSplit v (P.cyclicAlgebra a) ↔
      P.baseEmbedding v a ∈ (P.localNorm v).range := by
  sorry

theorem chapter09_cyclic_split_place_product_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (v : P.places)
    (h : P.splitPlaceData.splitPlace v) :
    P.localNorm v =
      (P.splitPlaceData.factorNorm v).comp
        (Units.map (P.splitPlaceData.productEquiv v h).toMonoidHom) := by
  rw [← P.splitPlaceData_localNorm v]
  exact P.splitPlaceData.localNorm_eq_product v h

theorem chapter09_cyclic_algebra_hasse_split_iff
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) :
    chapter09CsaIsSplit (P.cyclicAlgebra a) ↔
      ∀ v, P.localSplit v (P.cyclicAlgebra a) := by
  sorry

/-!
The family `A_v` in `Chapter09CyclicNormData` is also the split-place
convention from the text: at a split place it is a finite product of local
fields, and its norm is the product norm.  The following theorem is the exact
Hasse norm statement in unit-group form.
-/
theorem chapter09_hasse_norm_theorem
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) :
    a ∈ chapter09FieldNormSubgroup K L ↔
      chapter09CyclicEverywhereLocalNorm P a := by
  constructor
  · intro ha v
    have hsplit : chapter09CsaIsSplit (P.cyclicAlgebra a) :=
      (chapter09_cyclic_algebra_split_iff_norm P a).2 ha
    have hlocal : ∀ v, P.localSplit v (P.cyclicAlgebra a) :=
      (chapter09_cyclic_algebra_hasse_split_iff P a).1 hsplit
    exact (chapter09_cyclic_algebra_local_split_iff_norm P a v).1 (hlocal v)
  · intro ha
    apply (chapter09_cyclic_algebra_split_iff_norm P a).1
    apply (chapter09_cyclic_algebra_hasse_split_iff P a).2
    intro v
    exact (chapter09_cyclic_algebra_local_split_iff_norm P a v).2 (ha v)

/-!
The preceding witness-based API is useful for the cyclic-algebra proof
interface, but the theorem itself must not quantify over a guessed package of
local fields and split criteria.  Chapter 1 already exposes the canonical
local tensor algebra and the unconditional cyclic Hasse-norm principle.
-/
abbrev chapter09CanonicalLocalScalarExtensionAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.LocalScalarExtensionAt K L v

def chapter09CanonicalLocalElementNormAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K)
    (y : chapter09CanonicalLocalScalarExtensionAt K L v) :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.localElementNormAt K L v y

def chapter09CanonicalEverywhereLocalElementNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) : Prop :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalElementNorm K L a

theorem chapter09_canonical_local_scalar_extension_is_product
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ∀ v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K,
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalProductAlgebra K L v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.local_tensor_product_product_decomposition

theorem chapter09_hasse_norm_principle_unconditional
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L / K))] :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.HasseNormPrinciple K L :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.cyclic_extensions_satisfy_hasse_norm_principle

theorem chapter09_hasse_norm_theorem_unconditional
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L / K))] {a : K} (ha : a ≠ 0) :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.IsElementNorm K L a ↔
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalElementNorm K L a := by
  constructor
  · exact LastLib.Book06GlobalClassFieldTheory.Chapter01.elementNorm_implies_local_elementNorm ha
  · intro hlocal
    exact chapter09_hasse_norm_principle_unconditional ha hlocal

/-!
This is the element-level, canonical local/global form of the displayed
Hasse norm theorem.  The unit-group formulation above remains available for
clients that already supply an explicit cyclic-algebra realization.
-/
theorem chapter09_hasse_norm_theorem_unconditional_units
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L / K))] (a : Kˣ) :
    a ∈ chapter09FieldNormSubgroup K L ↔
      chapter09CanonicalEverywhereLocalElementNorm K L (a : K) := by
  sorry

def chapter09PositiveRealUnit (a : ℝˣ) : Prop :=
  0 < (a : ℝ)

/-!
At the real place of a complex quadratic extension, the local norm subgroup is
the positive reals.  This is recorded separately because it is the only
archimedean sign condition needed in the cyclic theorem.
-/
theorem chapter09_real_quadratic_norm_iff (a : ℝˣ) :
    a ∈ chapter09FieldNormSubgroup ℝ ℂ ↔ chapter09PositiveRealUnit a := by
  sorry

theorem chapter09_real_quadratic_norm_is_positive (a : ℂˣ) :
    chapter09PositiveRealUnit (chapter09FieldNormUnitHom ℝ ℂ a) := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
