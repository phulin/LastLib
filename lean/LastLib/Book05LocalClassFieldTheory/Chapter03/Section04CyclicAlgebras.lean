import LastLib.Book05LocalClassFieldTheory.Chapter03.Section03TateCohomologyOfACyclicGroup
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.TensorProduct.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open scoped BigOperators TensorProduct

/-! ## 3.4. Cyclic algebras -/

universe u

/- Mathlib's `CSA` and `BrauerGroup` are polymorphic in the universe of the
   underlying algebra.  The chapter uses the same universe as its base field,
   which gives these quotient interfaces a canonical instantiation. -/
abbrev chapter03CentralSimpleAlgebra (K : Type u) [Field K] := CSA.{u, u} K

abbrev chapter03BrauerGroup (K : Type u) [Field K] := BrauerGroup.{u, u} K

/-- A basis-style interface for a left `L`-basis, written without installing a temporary
`Algebra L A` instance in a dependent structure field. -/
def chapter03IsLeftLBasis
    (L A : Type*) [Field L] [Ring A] (hL : Algebra L A)
    (n : ℕ) (e : Fin n → A) : Prop :=
  (∀ x : A, ∃ c : Fin n → L,
    x = ∑ i, hL.algebraMap (c i) * e i) ∧
    (∀ c : Fin n → L,
      (∑ i, hL.algebraMap (c i) * e i) = 0 → ∀ i, c i = 0)

/-- Scalar extension of a central simple algebra is split by `L` when it is a matrix algebra. -/
def chapter03ScalarExtensionSplits
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (A : chapter03CentralSimpleAlgebra K) (hL : Algebra L A) (n : ℕ) : Prop :=
  letI : Algebra L A := hL
  Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

/-- Book-facing cyclic-algebra data.  The carrier is a `CSA K`; the additional fields record the
chosen copy of `L`, the symbol `z`, its crossed-product relations, and the split scalar extension.
This is an explicit interface because pinned Mathlib currently defines `CSA`/`BrauerGroup` but does
not yet construct cyclic algebras or their restriction/product maps. -/
structure Chapter03CyclicAlgebraPresentation
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ) where
  carrier : chapter03CentralSimpleAlgebra K
  algebraL : Algebra L carrier
  embedL : L →ₐ[K] carrier
  embedL_eq_algebraL : ∀ x : L, embedL x = algebraL.algebraMap x
  symbol : carrier
  symbol_pow : symbol ^ n = algebraMap K carrier (a : K)
  symbol_mul_embed : ∀ x : L,
    symbol * embedL x = embedL (σ x) * symbol
  leftL_basis :
    chapter03IsLeftLBasis L carrier algebraL n
      (fun i : Fin n => symbol ^ (i : ℕ))
  finrank_eq : Module.finrank K carrier = n ^ 2
  center_eq_base :
    {x : carrier | ∀ y : carrier, x * y = y * x} =
      Set.range (algebraMap K carrier)
  split_by_L : chapter03ScalarExtensionSplits K L carrier algebraL n

/-- The cyclic algebra presentation attached to the parameter `a`. -/
abbrev chapter03CyclicAlgebra
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ) : Type _ :=
  Chapter03CyclicAlgebraPresentation K L n σ a

theorem chapter03_cyclic_algebra_exists
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (hcyc : chapter03CyclicExtension K L n σ) :
    Nonempty (chapter03CyclicAlgebra K L n σ a) := by
  sorry

/-- A chosen presentation, useful for statements that need a concrete symbol or matrix algebra. -/
noncomputable def chapter03CyclicAlgebraChoice
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (hcyc : chapter03CyclicExtension K L n σ) :
    chapter03CyclicAlgebra K L n σ a :=
  Classical.choice (chapter03_cyclic_algebra_exists K L n σ a hcyc)

/-- The algebra is split over `K` when it is a full matrix algebra over `K`. -/
def chapter03CyclicAlgebraSplitsOverBase
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (C : chapter03CyclicAlgebra K L n σ a) : Prop :=
  Nonempty (C.carrier ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-- The Brauer class represented by a cyclic-algebra presentation. -/
def chapter03CyclicAlgebraBrauerClass
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (C : chapter03CyclicAlgebra K L n σ a) : chapter03BrauerGroup K :=
  @Quotient.mk' _ (Brauer.CSA_Setoid K) C.carrier

/-- Replacing `z` by `bz` is the book's crossed-product parameter change. -/
def chapter03TwistedSymbol
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (C : chapter03CyclicAlgebra K L n σ a) (_b : Lˣ) : C.carrier :=
  C.embedL (_b : L) * C.symbol

/- The longer name is retained as a book-facing alias for the extension-unit twist. -/
abbrev chapter03TwistedSymbolByExtensionUnit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (C : chapter03CyclicAlgebra K L n σ a) (b : Lˣ) : C.carrier :=
  chapter03TwistedSymbol K L n σ a C b

theorem chapter03_twisted_symbol_pow
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (hcyc : chapter03CyclicExtension K L n σ)
    (C : chapter03CyclicAlgebra K L n σ a) (b : Lˣ) :
    (chapter03TwistedSymbolByExtensionUnit K L n σ a C b) ^ n =
      algebraMap K C.carrier
        (Algebra.norm K (b : L) * (a : K)) := by
  classical
  have hpow (i : ℕ) (x : L) :
      C.symbol ^ i * C.embedL x =
        C.embedL ((σ ^ i) x) * C.symbol ^ i := by
    induction i generalizing x with
    | zero => simp
    | succ i ih =>
        calc
          C.symbol ^ (i + 1) * C.embedL x =
              C.symbol ^ i * (C.symbol * C.embedL x) := by rw [pow_succ, mul_assoc]
          _ = C.symbol ^ i * (C.embedL (σ x) * C.symbol) := by
            rw [C.symbol_mul_embed]
          _ = (C.symbol ^ i * C.embedL (σ x)) * C.symbol := by rw [mul_assoc]
          _ = (C.embedL ((σ ^ i) (σ x)) * C.symbol ^ i) * C.symbol := by
            rw [ih]
          _ = C.embedL ((σ ^ (i + 1)) x) * C.symbol ^ (i + 1) := by
            rw [show (σ ^ i) (σ x) = (σ ^ (i + 1)) x by
              rw [pow_succ]; rfl]
            rw [pow_succ C.symbol i]
            simp only [mul_assoc]
  have hprod (i : ℕ) :
      (C.embedL (b : L) * C.symbol) ^ i =
        C.embedL (∏ j ∈ Finset.range i, (σ ^ j) (b : L)) * C.symbol ^ i := by
    induction i with
    | zero => simp
    | succ i ih =>
        calc
          (C.embedL (b : L) * C.symbol) ^ (i + 1) =
              (C.embedL (b : L) * C.symbol) ^ i *
                (C.embedL (b : L) * C.symbol) := by rw [pow_succ]
          _ = (C.embedL (∏ j ∈ Finset.range i, (σ ^ j) (b : L)) *
                C.symbol ^ i) * (C.embedL (b : L) * C.symbol) := by rw [ih]
          _ = C.embedL (∏ j ∈ Finset.range i, (σ ^ j) (b : L)) *
                (C.symbol ^ i * C.embedL (b : L)) * C.symbol := by
                simp only [mul_assoc]
          _ = C.embedL (∏ j ∈ Finset.range i, (σ ^ j) (b : L)) *
                (C.embedL ((σ ^ i) (b : L)) * C.symbol ^ i) * C.symbol := by
                rw [hpow i (b : L)]
          _ = C.embedL (∏ j ∈ Finset.range (i + 1), (σ ^ j) (b : L)) *
                C.symbol ^ (i + 1) := by
                rw [Finset.prod_range_succ, map_mul, pow_succ]
                simp only [mul_assoc]
  have hncard : Nat.card (Gal(L/K)) = n := by
    rw [IsGalois.card_aut_eq_finrank K L, hcyc.1]
  have hσn : σ ^ n = 1 := by
    rw [← hncard]
    exact pow_card_eq_one'
  have himage :
      Finset.image (fun i : ℕ => σ ^ i) (Finset.range n) = Finset.univ := by
    rw [← hncard]
    exact IsCyclic.image_range_card hcyc.2
  let e : Fin n → Gal(L/K) := fun i => σ ^ (i : ℕ)
  have he_surj : Function.Surjective e := by
    intro τ
    have hτ : τ ∈ Finset.image (fun i : ℕ => σ ^ i) (Finset.range n) := by
      rw [himage]
      simp
    rcases Finset.mem_image.mp hτ with ⟨i, hi, rfl⟩
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  have he : Function.Bijective e := by
    apply (Fintype.bijective_iff_surjective_and_card e).2
    have hcard : Fintype.card (Gal(L/K)) = n := by
      simpa only [Nat.card_eq_fintype_card] using hncard
    exact ⟨he_surj, (Fintype.card_fin n).trans hcard.symm⟩
  have hprod_norm :
      (∏ j ∈ Finset.range n, (σ ^ j) (b : L)) =
        algebraMap K L (Algebra.norm K (b : L)) := by
    calc
      (∏ j ∈ Finset.range n, (σ ^ j) (b : L)) =
          ∏ j : Fin n, (σ ^ (j : ℕ)) (b : L) := by
            exact (Fin.prod_univ_eq_prod_range
              (fun j : ℕ => (σ ^ j) (b : L)) n).symm
      _ = ∏ τ : Gal(L/K), τ (b : L) :=
        Fintype.prod_bijective e he _ _ (fun _ => rfl)
      _ = algebraMap K L (Algebra.norm K (b : L)) := by
        rw [Algebra.norm_eq_prod_automorphisms]
  change (C.embedL (b : L) * C.symbol) ^ n =
    algebraMap K C.carrier (Algebra.norm K (b : L) * (a : K))
  rw [hprod n, hprod_norm, C.symbol_pow, C.embedL.commutes]
  rw [← map_mul]

theorem chapter03_cyclic_algebra_split_iff_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) (a : Kˣ)
    (hcyc : chapter03CyclicExtension K L n σ)
    (C : chapter03CyclicAlgebra K L n σ a) :
    chapter03CyclicAlgebraSplitsOverBase K L n σ a C ↔
      a ∈ chapter03NormSubgroup K L := by
  sorry

def chapter03CyclicAlgebraIsomorphic
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : Gal(L/K)) (a b : Kˣ)
    (C₁ : chapter03CyclicAlgebra K L n σ a)
    (C₂ : chapter03CyclicAlgebra K L n σ b) : Prop :=
  Nonempty (C₁.carrier ≃ₐ[K] C₂.carrier)

/- LOCAL_DEPENDENCY_GUESS: Pinned Mathlib has no universal crossed-product construction yet.  The
   choice below is the chapter-facing representative of the canonical presentation; the
   classification theorem is stated for those representatives rather than for arbitrary records
   carrying the same equations. -/
theorem chapter03_cyclic_algebra_parameter_classification
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) (a b : Kˣ)
    (hcyc : chapter03CyclicExtension K L n σ) :
    chapter03CyclicAlgebraIsomorphic K L n σ a b
      (chapter03CyclicAlgebraChoice K L n σ a hcyc)
      (chapter03CyclicAlgebraChoice K L n σ b hcyc) ↔
      a * b⁻¹ ∈ chapter03NormSubgroup K L := by
  sorry

/-- The parameter class in the norm quotient. -/
def chapter03CyclicParameterClass
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : Kˣ) : chapter03NormQuotient K L :=
  QuotientGroup.mk' (chapter03NormSubgroup K L) a

def chapter03CyclicAlgebraClassMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) : Kˣ → chapter03BrauerGroup K :=
  fun a => chapter03CyclicAlgebraBrauerClass K L n σ a
    (chapter03CyclicAlgebraChoice K L n σ a hcyc)

theorem chapter03_parameter_class_tensor_product_rule
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a b : Kˣ) :
    chapter03CyclicParameterClass K L (a * b) =
      chapter03CyclicParameterClass K L a * chapter03CyclicParameterClass K L b := by
  rfl

/- LOCAL_DEPENDENCY_GUESS: Mathlib currently exposes the Brauer quotient but not its tensor
   product.  This is the minimal chapter-local interface for the tensor-product calculation. -/
structure Chapter03CyclicBrauerProductData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) where
  product : chapter03BrauerGroup K → chapter03BrauerGroup K → chapter03BrauerGroup K
  parameter_rule : ∀ a b : Kˣ,
    product (chapter03CyclicAlgebraClassMap K L n σ hcyc a)
        (chapter03CyclicAlgebraClassMap K L n σ hcyc b) =
      chapter03CyclicAlgebraClassMap K L n σ hcyc (a * b)

theorem chapter03_cyclic_algebra_tensor_product_rule
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    Nonempty (Chapter03CyclicBrauerProductData K L n σ hcyc) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: Pinned Mathlib's Brauer definitions do not yet expose restriction or
   tensor-product group laws; this structure records the missing restriction interface used by the
   book's `Br(L/K)`. -/
structure Chapter03BrauerRestrictionData
    (K L : Type*) [Field K] [Field L] [Algebra K L] where
  restriction : chapter03BrauerGroup K → chapter03BrauerGroup L
  splitClass : chapter03BrauerGroup L

/-- The kernel-style relative Brauer class space for an explicit restriction interface. -/
def chapter03RelativeBrauerKernel
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (R : Chapter03BrauerRestrictionData K L) : Type _ :=
  {c : chapter03BrauerGroup K // R.restriction c = R.splitClass}

theorem chapter03_norm_quotient_relative_brauer_equiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    ∃ R : Chapter03BrauerRestrictionData K L,
      Nonempty (chapter03NormQuotient K L ≃ chapter03RelativeBrauerKernel K L R) := by
  sorry

/-- The inverse residue-class factor appearing when a cyclic generator is replaced by `σ^r`. -/
def chapter03GeneratorChangeFactor (n r : ℕ) : ZMod n :=
  (r : ZMod n)⁻¹

theorem chapter03_generator_change_factor_mul
    (n r : ℕ) (hr : Nat.Coprime r n) :
    (r : ZMod n) * chapter03GeneratorChangeFactor n r = 1 := by
  exact ZMod.coe_mul_inv_eq_one r hr

/-- A numerical invariant convention records the generator-dependence by the inverse of `r mod n`. -/
structure Chapter03GeneratorInvariantConvention
    (G : Type*) [CommGroup G] [Fintype G] (n : ℕ) where
  invariant : G → ZMod n
  card_eq : Nat.card G = n
  generator_change : ∀ (σ : G), Subgroup.zpowers σ = ⊤ →
    ∀ (r : ℕ), Nat.Coprime r n →
      invariant (σ ^ r) = chapter03GeneratorChangeFactor n r * invariant σ

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
