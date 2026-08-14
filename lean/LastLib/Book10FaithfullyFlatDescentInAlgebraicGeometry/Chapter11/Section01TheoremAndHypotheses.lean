import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Sites.Descent.DescentData

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Scheme

variable {S T : Scheme.{u}}

/-- The book-facing abbreviation for a faithfully flat morphism of schemes. -/
def IsFaithfullyFlat (p : T ⟶ S) : Prop :=
  Flat p ∧ Surjective p

/-- A faithfully flat quasi-compact morphism, i.e. a singleton fpqc cover. -/
def IsFpqcMorphism (p : T ⟶ S) : Prop :=
  Flat p ∧ Surjective p ∧ QuasiCompact p

@[simp]
theorem isFaithfullyFlat_iff (p : T ⟶ S) :
    IsFaithfullyFlat p ↔ Flat p ∧ Surjective p :=
  Iff.rfl

@[simp]
theorem isFpqcMorphism_iff (p : T ⟶ S) :
    IsFpqcMorphism p ↔ Flat p ∧ Surjective p ∧ QuasiCompact p :=
  Iff.rfl

theorem IsFpqcMorphism.toIsFaithfullyFlat {p : T ⟶ S}
    (hp : IsFpqcMorphism p) : IsFaithfullyFlat p :=
  ⟨hp.1, hp.2.1⟩

theorem IsFpqcMorphism.flat {p : T ⟶ S} (hp : IsFpqcMorphism p) : Flat p :=
  hp.1

theorem IsFpqcMorphism.surjective {p : T ⟶ S} (hp : IsFpqcMorphism p) : Surjective p :=
  hp.2.1

theorem IsFpqcMorphism.quasiCompact {p : T ⟶ S} (hp : IsFpqcMorphism p) :
    QuasiCompact p :=
  hp.2.2

theorem IsFpqcMorphism.mem_fpqcPrecoverage {p : T ⟶ S}
    (hp : IsFpqcMorphism p) :
    Presieve.singleton p ∈ AlgebraicGeometry.Scheme.fpqcPrecoverage S := by
  letI : Flat p := hp.1
  letI : Surjective p := hp.2.1
  letI : QuasiCompact p := hp.2.2
  exact AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage p

theorem IsFpqcMorphism.effectiveEpi {p : T ⟶ S} (hp : IsFpqcMorphism p) :
    EffectiveEpi p := by
  letI : Flat p := hp.1
  letI : Surjective p := hp.2.1
  letI : QuasiCompact p := hp.2.2
  infer_instance

end Scheme

open Scheme

/-- The affine-local finite-reduction condition used for an arbitrary fpqc family.

The image notation is deliberately kept at the level of the underlying topological spaces:
the condition says that every affine open of the base is covered by finitely many affine opens
in members of the family. -/
def HasAffineLocallyFiniteReduction {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{v} S) : Prop :=
  ∀ {U : S.Opens}, IsAffineOpen U →
    ∃ (n : ℕ) (a : Fin n → 𝒰.I₀) (V : ∀ i, (𝒰.X (a i)).Opens),
      (∀ i, IsAffineOpen (V i)) ∧
        ⋃ i, 𝒰.f (a i) '' (V i) = (U : Set S)

/-- A set-indexed fpqc family together with the finite affine reduction required in Section 2.1.

The cover field supplies flatness and joint surjectivity; the last field is the quasi-compactness
condition in the form used by the affine-local proof. -/
structure FpqcFamily (S : Scheme.{u}) where
  cover : S.Cover (Scheme.precoverage (fun f => Flat f))
  affineLocallyFinite : HasAffineLocallyFiniteReduction cover.toPreZeroHypercover

namespace FpqcFamily

variable {S : Scheme.{u}} (𝒰 : FpqcFamily S)

theorem flat (i : 𝒰.cover.I₀) : Flat (𝒰.cover.f i) := by
  have h := 𝒰.cover.mem₀
  rw [Scheme.presieve₀_mem_precoverage_iff] at h
  exact h.2 i

theorem jointlySurjective :
    ∀ x : S, ∃ i : 𝒰.cover.I₀, x ∈ Set.range (𝒰.cover.f i) := by
  have h := 𝒰.cover.mem₀
  rw [Scheme.presieve₀_mem_precoverage_iff] at h
  exact h.1

theorem quasiCompactCover :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover := by
  sorry

end FpqcFamily

namespace SchemeDescent

/-- The pseudofunctor whose fiber over `S` is the category of schemes over `S` and whose
morphisms are pullback functors. -/
noncomputable def overPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Over X.unop))
    (fun f => (Over.pullback f.unop).toCat)
    (fun X => Cat.Hom.isoMk (Over.pullbackId X.unop))
    (fun f g => Cat.Hom.isoMk (Over.pullbackComp g.unop f.unop))

abbrev Data {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) :=
  overPseudofunctor.DescentData f

abbrev Datum {S T : Scheme.{u}} (p : T ⟶ S) : Type _ :=
  Data (fun _ : PUnit => p)

/-- An object downstairs together with its comparison isomorphism to a descent datum upstairs. -/
structure Effective {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (D : Data f) where
  descended : Over S
  comparison : D ≅ overPseudofunctor.toDescentData f descended

def IsEffective {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) : Prop :=
  ∀ D : Data f, Nonempty (Effective f D)

def CompatibleIso {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} {D : Data f}
    (A B : Effective f D) :=
  { e : A.descended ≅ B.descended //
      A.comparison.hom ≫ (overPseudofunctor.toDescentData f).map e.hom = B.comparison.hom }

theorem singleton_effective_of_fpqc {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Scheme.IsFpqcMorphism p) :
    IsEffective (fun _ : PUnit => p) := by
  sorry

theorem family_effective_of_fpqc (𝒰 : FpqcFamily S) :
    IsEffective (fun i => 𝒰.cover.f i) := by
  sorry

theorem singleton_morphisms_descend_uniquely {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Scheme.IsFpqcMorphism p) :
    (overPseudofunctor.toDescentData (fun _ : PUnit => p)).FullyFaithful := by
  sorry

theorem family_morphisms_descend_uniquely (𝒰 : FpqcFamily S) :
    (overPseudofunctor.toDescentData (fun i => 𝒰.cover.f i)).FullyFaithful := by
  sorry

theorem effective_unique_up_to_unique_iso {ι : Type v} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S} {D : Data f}
    (A B : Effective f D)
    (hfullyFaithful :
      (overPseudofunctor.toDescentData f).FullyFaithful) :
    Nonempty (CompatibleIso A B) ∧
      ∀ e₁ e₂ : CompatibleIso A B, e₁ = e₂ := by
  sorry

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
