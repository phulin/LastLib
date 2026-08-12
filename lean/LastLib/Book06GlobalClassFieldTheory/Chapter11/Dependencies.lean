import LastLib.Book04AdelesAndIdeles.Chapter02.Section04LocalIntegersAndLocalUnits
import LastLib.Book04AdelesAndIdeles.Chapter13.Section04FiniteOrderCharactersAndConductors
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section04ArchitectureOfTheProof
import LastLib.Book06GlobalClassFieldTheory.Chapter07.Section03ConductorsOfExtensionsAndCharacters
import LastLib.Book06GlobalClassFieldTheory.Chapter10.Section04KroneckerWeberRevisited
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-!
## Shared interfaces for Chapter 11

Book 04, Chapter 13 already supplies the restricted-product ideles, the
continuous idele-class characters, their local-factor families, the module
character, and finite-order conductor levels.  The aliases below keep the
Chapter 11 statements in the notation of the global class-field-theory book.
The remaining records are narrow interfaces for reciprocity, local norm
maps, algebraic coefficient embeddings, and induced representations; none of
them builds a later conclusion into its hypotheses.
-/

abbrev Chapter11Idele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13Idele K

abbrev Chapter11IdeleClass (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13IdeleClass K

abbrev Chapter11HeckeCharacter (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13HeckeCharacter K

abbrev Chapter11IdeleCharacter (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13ContinuousComplexCharacter
    (Chapter11Idele K)

abbrev Chapter11LocalCharacterFamily (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13MultiplicativeCharacterFamily K

abbrev Chapter11FiniteIdele (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13FiniteIdele K

abbrev Chapter11FinitePlaceIndex (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)

abbrev Chapter11LocalUnitSubgroup (K : Type*) [Field K] [NumberField K]
    (v : Chapter11FinitePlaceIndex K) : Subgroup (v.adicCompletion K)ˣ :=
  LastLib.Book04AdelesAndIdeles.Chapter13.Chapter13LocalUnitSubgroup K v

abbrev Chapter11LocalUniformizer
    {K : Type*} [Field K] [NumberField K]
    (v : Chapter11FinitePlaceIndex K) (π : v.adicCompletion K) : Prop :=
  LastLib.Book04AdelesAndIdeles.Chapter02.Chapter02LocalUniformizer v π

abbrev chapter11IdeleClassModule
    (K : Type*) [Field K] [NumberField K] :
    Chapter11IdeleClass K →* ℝ :=
  LastLib.Book04AdelesAndIdeles.Chapter13.chapter13IdeleClassModule K

theorem chapter11_idele_class_module_positive
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter11IdeleClass K) : 0 < chapter11IdeleClassModule K x := by
  exact LastLib.Book04AdelesAndIdeles.Chapter13.chapter13_idele_class_module_positive K x

def chapter11FiniteOrder
    {G : Type*} [Monoid G] (χ : G →* ℂˣ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x, χ x ^ n = 1

def chapter11FiniteImage
    {G : Type*} [Monoid G] [TopologicalSpace G] (χ : G →ₜ* ℂˣ) : Prop :=
  Set.Finite (Set.range χ)

def chapter11CharacterKernel
    {G : Type*} [Group G] (χ : G →* ℂˣ) : Subgroup G :=
  χ.ker

theorem chapter11_finite_order_iff_finite_image
    (K : Type*) [Field K] [NumberField K] (χ : Chapter11HeckeCharacter K) :
    chapter11FiniteOrder χ.toMonoidHom ↔ chapter11FiniteImage χ := by
  sorry

theorem chapter11_finite_order_kernel_open
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter11HeckeCharacter K)
    (hχ : chapter11FiniteOrder χ.toMonoidHom) :
    IsOpen (chapter11CharacterKernel χ.toMonoidHom : Set (Chapter11IdeleClass K)) := by
  sorry

/- The continuous global reciprocity map is the only input needed to turn a
continuous Galois character into a Hecke character. -/
structure Chapter11GlobalReciprocityData
    (K G : Type*) [Field K] [NumberField K] [Group G]
    [TopologicalSpace G] where
  artin : Chapter11IdeleClass K →* G
  continuous_artin : Continuous artin
  surjective_artin : Function.Surjective artin

structure Chapter11FiniteGaloisReciprocityData
    (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] where
  artin : Chapter11IdeleClass K →* Gal(L / K)
  surjective_artin : Function.Surjective artin

abbrev Chapter11AbsoluteGaloisAbelianization (K : Type*) [Field K] :=
  Field.absoluteGaloisGroupAbelianization K

abbrev Chapter11FiniteImageCharacters (G : Type*) [Group G] [TopologicalSpace G] :=
  {χ : G →ₜ* ℂˣ // chapter11FiniteImage χ}

abbrev Chapter11FiniteOrderHeckeCharacters
    (K : Type*) [Field K] [NumberField K] :=
  {χ : Chapter11HeckeCharacter K // chapter11FiniteOrder χ.toMonoidHom}

/- LOCAL_DEPENDENCY_GUESS: the inverse-limit character dictionary is supplied
by infinite reciprocity once the preceding global completion is identified
with the absolute Galois abelianization. -/
theorem chapter11_finite_character_reciprocity_bijection
    (K G : Type*) [Field K] [NumberField K] [Group G]
    [TopologicalSpace G]
    (R : Chapter11GlobalReciprocityData K G) :
    Nonempty (Chapter11FiniteImageCharacters G ≃
      Chapter11FiniteOrderHeckeCharacters K) := by
  sorry

/- Local unit layers and conductor exponents.  The finite-place version uses
the local filtration already recorded in Book 06, Chapter 7. -/
def chapter11LocalCharacterTrivialAtLevel
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (ψ : (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ) (n : ℕ) : Prop :=
  ∀ u, u ∈ LastLib.Book06GlobalClassFieldTheory.Chapter07.finiteUnitFiltration v n →
    ψ u = 1

noncomputable def chapter11LocalConductorExponent
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (ψ : (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  sInf {n : ℕ | chapter11LocalCharacterTrivialAtLevel v ψ n}

theorem chapter11_local_conductor_exponent_is_least
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (ψ : (v.maximalIdeal.adicCompletion K)ˣ →* ℂˣ)
    (hψ : Set.Nonempty {n : ℕ | chapter11LocalCharacterTrivialAtLevel v ψ n}) :
    chapter11LocalCharacterTrivialAtLevel v ψ
        (chapter11LocalConductorExponent v ψ) ∧
      ∀ n, chapter11LocalCharacterTrivialAtLevel v ψ n →
        chapter11LocalConductorExponent v ψ ≤ n := by
  sorry

/-! ### Infinity types -/

abbrev Chapter11Embedding (K : Type*) [Field K] := K →+* ℂ

def chapter11ConjugateEmbedding
    {K : Type*} [Field K] (τ : Chapter11Embedding K) : Chapter11Embedding K :=
  ComplexEmbedding.conjugate τ

abbrev Chapter11InfinityType (K : Type*) [Field K] :=
  Chapter11Embedding K → ℤ

def chapter11A0InfinityType
    {K : Type*} [Field K]
    (n : Chapter11InfinityType K) (w : ℤ) : Prop :=
  (∀ τ, ComplexEmbedding.IsReal τ → 2 * n τ = w) ∧
    (∀ τ, ¬ComplexEmbedding.IsReal τ →
      n τ + n (chapter11ConjugateEmbedding τ) = w)

abbrev Chapter11ArchimedeanParameter (K : Type*) [Field K] :=
  Chapter11Embedding K → ℂˣ

def chapter11InfinityMonomial
    {K : Type*} [Field K] [NumberField K]
    (n : Chapter11InfinityType K) (x : Chapter11ArchimedeanParameter K) : ℂˣ :=
  ∏ τ, x τ ^ (-(n τ))

def chapter11HasInfinityType
    {K : Type*} [Field K] [NumberField K]
    (χinf : Chapter11ArchimedeanParameter K →* ℂˣ)
    (n : Chapter11InfinityType K) : Prop :=
  ∃ U : Subgroup (Chapter11ArchimedeanParameter K),
    IsConnected (U : Set (Chapter11ArchimedeanParameter K)) ∧
      ∀ x : U, χinf x = chapter11InfinityMonomial n x

structure Chapter11AlgebraicHeckeCharacter
    (K A : Type*) [Field K] [NumberField K] [Field A] where
  character : Chapter11HeckeCharacter K
  coefficientEmbedding : A →+* ℂ
  infinityType : Chapter11InfinityType K
  archimedeanCharacter : Chapter11ArchimedeanParameter K →* ℂˣ
  infinity_type_realized : chapter11HasInfinityType archimedeanCharacter infinityType
  finiteValueCharacter : Chapter11FiniteIdele K →* Aˣ
  finite_value_restriction : Prop

/-!
The finite-value restriction is the remaining bridge from the chosen finite
idele factor to the class character.  Its coefficient-valued source is
explicit, while the ell-adic section supplies the completion maps needed to
evaluate the infinity correction.
-/

/-! ### Local norms and Galois conjugation -/

structure Chapter11NormData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] where
  classNorm : Chapter11IdeleClass M →* Chapter11IdeleClass K
  continuous_classNorm : Continuous classNorm
  below : NumberField.FinitePlace M → NumberField.FinitePlace K
  localNorm : ∀ w : NumberField.FinitePlace M,
    (w.maximalIdeal.adicCompletion M)ˣ →*
      ((below w).maximalIdeal.adicCompletion K)ˣ
  finiteClassEmbeddingM : ∀ w : NumberField.FinitePlace M,
    (w.maximalIdeal.adicCompletion M)ˣ → Chapter11IdeleClass M
  finiteClassEmbeddingK : ∀ w : NumberField.FinitePlace M,
    ((below w).maximalIdeal.adicCompletion K)ˣ → Chapter11IdeleClass K
  local_norm_compatibility : ∀ w u,
    classNorm (finiteClassEmbeddingM w u) =
      finiteClassEmbeddingK w (localNorm w u)

structure Chapter11GaloisIdeleActionData
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] where
  action : Gal(M / K) → Chapter11IdeleClass M ≃* Chapter11IdeleClass M
  action_continuous : ∀ σ, Continuous (action σ)
  action_one : action 1 = MulEquiv.refl _
  action_mul : ∀ σ τ, action (σ * τ) = (action σ).trans (action τ)

def chapter11ConjugateCharacter
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (D : Chapter11GaloisIdeleActionData K M)
    (θ : Chapter11HeckeCharacter M) (σ : Gal(M / K)) :
    Chapter11HeckeCharacter M :=
  { toMonoidHom := θ.toMonoidHom.comp (D.action σ⁻¹).toMonoidHom
    continuous_toFun := θ.continuous_toFun.comp (D.action_continuous σ⁻¹) }

def chapter11CharacterStabilizer
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (D : Chapter11GaloisIdeleActionData K M)
    (θ : Chapter11HeckeCharacter M) : Subgroup (Gal(M / K)) where
  carrier := {σ | chapter11ConjugateCharacter D θ σ = θ}
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

/-! ### One-dimensional and induced representations -/

noncomputable def chapter11CharacterRepresentation
    (E H : Type*) [Field E] [Group H]
    (θ : H →* Eˣ) : Representation E H E where
  toFun h := (θ h : E) • LinearMap.id
  map_one' := by sorry
  map_mul' h₁ h₂ := by sorry

abbrev Chapter11InducedSpace
    (E G H : Type*) [Field E] [Group G] [Group H]
    (φ : H →* G) (θ : H →* Eˣ) :=
  Representation.IndV φ (chapter11CharacterRepresentation E H θ)

noncomputable def chapter11InducedRepresentation
    (E G H : Type*) [Field E] [Group G] [Group H]
    (φ : H →* G) (θ : H →* Eˣ) :
    Representation E G (Chapter11InducedSpace E G H φ θ) :=
  Representation.ind φ (chapter11CharacterRepresentation E H θ)

def chapter11RestrictRepresentation
    {E G H V : Type*} [Field E] [Group G] [Group H]
    [AddCommGroup V] [Module E V]
    (φ : H →* G) (ρ : Representation E G V) : Representation E H V :=
  ρ.comp φ

def chapter11RepresentationIrreducible
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) : Prop :=
  ∀ W : Submodule E V,
    (∀ g, W ≤ W.comap (ρ g)) → W = ⊥ ∨ W = ⊤

def chapter11RepresentationCharacter
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) : G → E :=
  ρ.character

noncomputable def chapter11RepresentationDeterminant
    {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V]
    (ρ : Representation E G V) : G →* Eˣ := by
  refine
    { toFun := fun g => Units.mk0 (LinearMap.det (ρ g)) (by sorry)
      map_one' := by sorry
      map_mul' := by sorry }

def chapter11RepresentationCharacteristicPolynomial
    {E G V ι : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] [FiniteDimensional E V]
    (b : Module.Basis ι E V) (ρ : Representation E G V) (g : G) : Polynomial E :=
  Matrix.charpoly (LinearMap.toMatrix b b (ρ g))

/- LOCAL_DEPENDENCY_GUESS: the preceding ramification chapters supply the
Artin-conductor function for representations.  Keeping it as a function
interface lets the induction formulas use the exact local exponents without
pretending that a global conductor API is already canonical. -/
structure Chapter11ArtinConductorData
    (K G E V : Type*) [Field K] [NumberField K] [Group G] [Field E]
    [AddCommGroup V] [Module E V] where
  exponent : Representation E G V → NumberField.FinitePlace K → ℕ

structure Chapter11TransferData (G H : Type*) [Group G] [Group H] where
  transfer : G →* H

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
