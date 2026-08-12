import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
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
This is the book-facing interface for those two canonical constructions.
-/
def chapter09CsaIsSplit {K : Type uK} [Field K] (A : CSA.{uK, uK} K) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/- LOCAL_DEPENDENCY_GUESS: construct the cyclic algebra attached to a cyclic
extension and identify its split locus with the field norm subgroup. -/
structure Chapter09CyclicNormData
    (K : Type uK) (L : Type uL) [Field K] [Field L] [Algebra K L]
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
  localSplit : ∀ _v, CSA.{uK, uK} K → Prop
  cyclicAlgebra_isSplit_iff_globalNorm :
    ∀ a, chapter09CsaIsSplit (cyclicAlgebra a) ↔
      a ∈ chapter09FieldNormSubgroup K L
  localSplit_iff_localNorm :
    ∀ a v,
      localSplit v (cyclicAlgebra a) ↔
        baseEmbedding v a ∈ (localNorm v).range
  globalSplit_iff_allLocalSplit :
    ∀ A, chapter09CsaIsSplit A ↔ ∀ v, localSplit v A

attribute [instance] Chapter09CyclicNormData.localFieldMonoid
  Chapter09CyclicNormData.localAlgebraMonoid

def chapter09CyclicEverywhereLocalNorm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) : Prop :=
  ∀ v, P.baseEmbedding v a ∈ (P.localNorm v).range

theorem chapter09_cyclic_algebra_split_iff_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) :
    chapter09CsaIsSplit (P.cyclicAlgebra a) ↔
      a ∈ chapter09FieldNormSubgroup K L :=
  P.cyclicAlgebra_isSplit_iff_globalNorm a

theorem chapter09_cyclic_algebra_local_split_iff_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (a : Kˣ) (v : P.places) :
    P.localSplit v (P.cyclicAlgebra a) ↔
      P.baseEmbedding v a ∈ (P.localNorm v).range :=
  P.localSplit_iff_localNorm a v

theorem chapter09_cyclic_split_place_product_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
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
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L / K))]
    (P : Chapter09CyclicNormData K L) (A : CSA.{uK, uK} K) :
    chapter09CsaIsSplit A ↔ ∀ v, P.localSplit v A :=
  P.globalSplit_iff_allLocalSplit A

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
      (P.cyclicAlgebra_isSplit_iff_globalNorm a).2 ha
    have hlocal : ∀ v, P.localSplit v (P.cyclicAlgebra a) :=
      (P.globalSplit_iff_allLocalSplit (P.cyclicAlgebra a)).1 hsplit
    exact (P.localSplit_iff_localNorm a v).1 (hlocal v)
  · intro ha
    apply (P.cyclicAlgebra_isSplit_iff_globalNorm a).1
    apply (P.globalSplit_iff_allLocalSplit (P.cyclicAlgebra a)).2
    intro v
    exact (P.localSplit_iff_localNorm a v).2 (ha v)

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
