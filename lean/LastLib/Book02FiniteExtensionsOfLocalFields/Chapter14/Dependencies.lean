import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section03CompletionOfALocalization
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section03CompletionSeparatesBranches
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section02DecompositionGroups
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section06FactorizationAndBaseChange
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section03TheGaloisPicture
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Ring.Basic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open Polynomial
open IntermediateField
open scoped BigOperators NumberField Pointwise TensorProduct Topology

universe u v w

/-! Shared interfaces for Chapter 14.  The number-field prime and completion
aliases are canonical Mathlib constructions.  The small bundled structures
below keep the later approximation theorem independent of choices of carrier
types and of local algebra instances. -/

abbrev Chapter14Prime (F : Type u) [Field F] [NumberField F] : Type u :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 F)

abbrev Chapter14PrimeAbove
    (F : Type u) (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (p : Chapter14Prime F) : Type v :=
  p.asIdeal.primesOver (𝓞 E)

/-- The completion attached to a finite place of a number field. -/
abbrev chapter14BaseCompletion
    (F : Type u) [Field F] [NumberField F] (p : Chapter14Prime F) : Type u :=
  p.adicCompletion F

/-- The fraction field of the completed localization at a prime above `p`. -/
abbrev chapter14BranchCompletion
    (F : Type u) (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p) : Type v :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.branchFractionField
    (𝓞 E) P.1

def chapter14PrimeNorm
    {F : Type u} [Field F] [NumberField F] (p : Chapter14Prime F) : ℕ :=
  Ideal.absNorm p.asIdeal

def chapter14RamificationIndex
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p) : ℕ :=
  P.1.ramificationIdx (𝓞 F)

def chapter14ResidueDegree
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p) : ℕ :=
  P.1.inertiaDeg (𝓞 F)

/-! A bundled global extension is used only when a theorem has to return a
field extension together with all its typeclass data. -/

structure Chapter14NumberFieldModel (F : Type u) [Field F] [NumberField F] where
  carrier : Type v
  [field_carrier : Field carrier]
  [number_field_carrier : NumberField carrier]
  [algebra : Algebra F carrier]
  [finite_dimensional : FiniteDimensional F carrier]

noncomputable def chapter14ModelDegree
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) : ℕ :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  Module.finrank F M.carrier

abbrev chapter14ModelPrimeAbove
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F) : Type v :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  Chapter14PrimeAbove F M.carrier p

abbrev chapter14ModelBranchCompletion
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F)
    (P : chapter14ModelPrimeAbove M p) : Type v :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  chapter14BranchCompletion F M.carrier p P

abbrev chapter14ModelScalarExtension
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F)
    [Algebra F (chapter14BaseCompletion F p)] : Type _ :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  M.carrier ⊗[F] chapter14BaseCompletion F p

def chapter14ModelTensorRightBaseMap
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F)
    [Algebra F (chapter14BaseCompletion F p)] :
    chapter14BaseCompletion F p →+* chapter14ModelScalarExtension M p :=
  letI : Field M.carrier := M.field_carrier
  letI : NumberField M.carrier := M.number_field_carrier
  letI : Algebra F M.carrier := M.algebra
  letI : FiniteDimensional F M.carrier := M.finite_dimensional
  Algebra.TensorProduct.includeRight.toRingHom

/-!
DEPENDENCY_GUESS: The canonical branch-to-completion algebra map is not packaged by the
preceding chapters with the prime-above subtype as its index.  This record
keeps that map explicit; it is the global-to-local dependency guess used
by the approximation theorem.
-/

structure Chapter14CompletionChoice
    {F : Type u} [Field F] [NumberField F]
    (M : Chapter14NumberFieldModel F) (p : Chapter14Prime F)
    (L : Type w) where
  [field_carrier : Field L]
  place : chapter14ModelPrimeAbove M p
  branchBaseMap : chapter14BaseCompletion F p →+*
    chapter14ModelBranchCompletion M p place
  targetBaseMap : chapter14BaseCompletion F p →+* L
  equivalence : chapter14ModelBranchCompletion M p place ≃+* L
  commutes : ∀ x, equivalence (branchBaseMap x) = targetBaseMap x

/-! The exact local-algebra variant is useful when a canonical `Algebra`
instance is already available. -/

structure Chapter14LocalCompletionChoice
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (p : Chapter14Prime F)
    (P : Chapter14PrimeAbove F E p) (L : Type*) where
  [field_carrier : Field L]
  branchBaseMap : chapter14BaseCompletion F p →+*
    chapter14BranchCompletion F E p P
  targetBaseMap : chapter14BaseCompletion F p →+* L
  equivalence : chapter14BranchCompletion F E p P ≃+* L
  commutes : ∀ x, equivalence (branchBaseMap x) = targetBaseMap x

/-! DEPENDENCY_GUESS: A reduction interface indexed by a global prime.  Its fields are the
surjective reduction map and its kernel, so the exact sequence and the
ramified Frobenius coset can be stated without choosing a valuation model. -/

structure Chapter14PrimeReduction
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (p : Chapter14Prime F)
    (P : Chapter14PrimeAbove F E p)
    (D : Subgroup (Gal(E / F)))
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField] where
  inertia : Subgroup D
  reduction : D →* Gal(P.1.ResidueField / p.asIdeal.ResidueField)
  kernel_eq_inertia : inertia = MonoidHom.ker reduction
  surjective : Function.Surjective reduction

instance chapter14PrimeReduction.inertiaNormal
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) : R.inertia.Normal := by
  rw [R.kernel_eq_inertia]
  infer_instance

def chapter14PrimeReductionExact
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {p : Chapter14Prime F} {P : Chapter14PrimeAbove F E p}
    {D : Subgroup (Gal(E / F))}
    [Field p.asIdeal.ResidueField] [Field P.1.ResidueField]
    [Algebra p.asIdeal.ResidueField P.1.ResidueField]
    [FiniteDimensional p.asIdeal.ResidueField P.1.ResidueField]
    [IsGalois p.asIdeal.ResidueField P.1.ResidueField]
    (R : Chapter14PrimeReduction F E p P D) : Prop :=
  Function.MulExact (Subgroup.subtype R.inertia) R.reduction

/-! Approximation and Krasner interfaces. -/

def chapter14CoefficientPolynomial
    {R : Type*} [Semiring R] (n : ℕ) (c : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

def chapter14PolynomialMapAt
    {F : Type u} [Field F] [NumberField F]
    (p : Chapter14Prime F) : F[X] →+* (chapter14BaseCompletion F p)[X] :=
  Polynomial.mapRingHom
    (NumberField.FinitePlace.embedding (R := 𝓞 F) (K := F) p)

structure Chapter14KrasnerNeighborhoodData
    (K L : Type*) [NormedField K] [NormedField L] [Algebra K L]
    (g : K[X]) (α : L) where
  monic : g.Monic
  neighborhood : Set (Fin g.natDegree → K)
  open_neighborhood : IsOpen neighborhood
  contains_polynomial : (fun i => g.coeff i) ∈ neighborhood
  factor_field : ∀ h, h.Monic → h.natDegree = g.natDegree →
    (fun i => h.coeff i) ∈ neighborhood →
    ∃ q : K[X], q ∣ h ∧ q.Monic ∧
      Nonempty (AdjoinRoot q ≃ₐ[K] K⟮α⟯)

structure Chapter14HenselProductData
    (K : Type*) [Field K] (g : ℕ) where
  local_polynomial : K[X]
  factors : Fin g → K[X]
  monic : local_polynomial.Monic
  separable : local_polynomial.Separable
  factor_monic : ∀ i, (factors i).Monic
  pairwise_coprime : Pairwise (fun i j =>
    IsCoprime (Ideal.span ({factors i} : Set K[X]))
      (Ideal.span ({factors j} : Set K[X])))
  product : local_polynomial = ∏ i, factors i

/-! A finite list of prescribed local branches, used in §14.5. -/

structure Chapter14PrescribedLocalExtension
    (F : Type u) [Field F] [NumberField F]
    (p : Chapter14Prime F) where
  carrier : Type v
  [field_carrier : Field carrier]
  [algebra : Algebra (chapter14BaseCompletion F p) carrier]
  [finite_dimensional : FiniteDimensional (chapter14BaseCompletion F p) carrier]

noncomputable def chapter14PrescribedLocalDegree
    {F : Type u} [Field F] [NumberField F]
    {p : Chapter14Prime F} (L : Chapter14PrescribedLocalExtension F p) : ℕ :=
  letI : Field L.carrier := L.field_carrier
  letI : Algebra (chapter14BaseCompletion F p) L.carrier := L.algebra
  letI : FiniteDimensional (chapter14BaseCompletion F p) L.carrier := L.finite_dimensional
  Module.finrank (chapter14BaseCompletion F p) L.carrier

def chapter14MaximumLocalDegree
    {F : Type u} [Field F] [NumberField F]
    {r : ℕ} (p : Fin r → Chapter14Prime F)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i)) : ℕ :=
  Finset.univ.sup fun i => chapter14PrescribedLocalDegree (L i)

structure Chapter14ApproximationScope
    (F : Type u) [Field F] [NumberField F]
    {r : ℕ}
    (p : Fin r → Chapter14Prime F)
    (L : ∀ i, Chapter14PrescribedLocalExtension F (p i)) where
  model : Chapter14NumberFieldModel.{u, v} F
  degree_eq_max : chapter14ModelDegree model = chapter14MaximumLocalDegree p L
  choice : ∀ i,
    letI : Field (L i).carrier := (L i).field_carrier
    Chapter14CompletionChoice.{u, v, v} model (p i) (L i).carrier

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
