import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
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
  exact @Scheme.Hom.singleton_mem_fpqcPrecoverage _ _ p hp.1 hp.2.1 hp.2.2

theorem IsFpqcMorphism.effectiveEpi {p : T ⟶ S} (hp : IsFpqcMorphism p) :
    EffectiveEpi p := by
  rw [← Sieve.effectiveEpimorphic_singleton,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck hp.mem_fpqcPrecoverage)

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
  cover : S.Cover (Scheme.precoverage @Flat)
  affineLocallyFinite : HasAffineLocallyFiniteReduction cover.toPreZeroHypercover

namespace FpqcFamily

variable {S : Scheme.{u}} (𝒰 : FpqcFamily S)

theorem flat (i : 𝒰.cover.I₀) : Flat (𝒰.cover.f i) := by
  exact 𝒰.cover.map_prop i

theorem jointlySurjective :
    ∀ x : S, ∃ i : 𝒰.cover.I₀, x ∈ Set.range (𝒰.cover.f i) := by
  intro x
  exact (Scheme.presieve₀_mem_precoverage_iff (P := @Flat)
    𝒰.cover.toPreZeroHypercover).mp 𝒰.cover.mem₀ |>.1 x

theorem quasiCompactCover :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover := by
  constructor
  intro U hU
  obtain ⟨n, a, V, hV, hcover⟩ := 𝒰.affineLocallyFinite hU
  exact IsCompactOpenCovered.of_finite a V (fun i ↦ (hV i).isCompact) hcover

end FpqcFamily

namespace SchemeDescent

/-- The pseudofunctor whose fiber over `S` is the category of schemes over `S` and whose
morphisms are pullback functors. -/
noncomputable def overPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{u, u + 1}) :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Over X.unop))
    (fun f => (Over.pullback f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk Over.pullbackId)
    (fun f g => Cat.Hom.isoMk (Over.pullbackComp g.unop f.unop))
    (by
      intro b₀ b₁ b₂ b₃ f g h
      have hraw :
          (Over.pullbackComp h.unop (f ≫ g).unop).hom ≫
              Functor.whiskerRight (Over.pullbackComp g.unop f.unop).hom
                (Over.pullback h.unop) ≫
            (Functor.associator (Over.pullback f.unop) (Over.pullback g.unop)
                (Over.pullback h.unop)).hom ≫
              Functor.whiskerLeft (Over.pullback f.unop)
                (Over.pullbackComp h.unop g.unop).inv ≫
            (Over.pullbackComp (g ≫ h).unop f.unop).inv =
            eqToHom (by simp) := by
        ext X
        dsimp [Over.pullbackComp, conjugateIsoEquiv, Over.mapComp]
        ext <;>
          simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            Category.assoc] <;>
          cases (Category.assoc h.unop g.unop f.unop).symm <;> rfl
      exact congr($(hraw).toCatHom₂))
    (by
      intro b₀ b₁ f
      have hraw :
          (Over.pullbackComp f.unop (𝟙 _)).hom ≫
              Functor.whiskerRight (Over.pullbackId (X := b₀.unop)).hom
                (Over.pullback f.unop) ≫
            (Functor.leftUnitor (Over.pullback f.unop)).hom =
            eqToHom (by simp) := by
        ext X
        dsimp [Over.pullbackComp, Over.pullbackId, conjugateIsoEquiv,
          Over.mapComp]
        ext <;>
          simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            Category.assoc] <;>
          cases (Category.comp_id f.unop) <;> rfl
      exact congr($(hraw).toCatHom₂))
    (by
      intro b₀ b₁ f
      have hraw :
          (Over.pullbackComp (𝟙 _) f.unop).hom ≫
              Functor.whiskerLeft (Over.pullback f.unop)
                (Over.pullbackId (X := b₁.unop)).hom ≫
            (Functor.rightUnitor (Over.pullback f.unop)).hom =
            eqToHom (by simp) := by
        ext X
        dsimp [Over.pullbackComp, Over.pullbackId, conjugateIsoEquiv,
          Over.mapComp]
        ext <;>
          simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
            Category.assoc] <;>
          cases (Category.id_comp f.unop) <;> rfl
      exact congr($(hraw).toCatHom₂))

abbrev Data {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) :=
  overPseudofunctor.DescentData f

abbrev Datum {S T : Scheme.{u}} (p : T ⟶ S) : Type _ :=
  Data (fun _ : PUnit => p)

/-- An object downstairs together with its comparison isomorphism to a descent datum upstairs. -/
structure Effective {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (D : Data f) where
  descended : Over S
  comparison : D ≅ (overPseudofunctor.toDescentData f).obj descended

def IsEffective {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) : Prop :=
  ∀ D : Data f, Nonempty (Effective f D)

def CompatibleIso {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} {D : Data f}
    (A B : Effective f D) :=
  { e : A.descended ≅ B.descended //
      A.comparison.hom ≫ (overPseudofunctor.toDescentData f).map e.hom = B.comparison.hom }

private theorem pullbackComp_left_fst_fst {A X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : A ⟶ Z) :
    ((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
        pullback.fst (pullback.snd h g) f ≫ pullback.fst h g =
      pullback.fst h (f ≫ g) := by
  have hc := congrArg (fun k => k.left)
    (conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
      ((Over.mapComp f g).inv) (Over.mk h))
  simpa [Over.pullbackComp] using hc

private theorem pullbackComp_inv_fst_fst {A X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : A ⟶ Z) :
    ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫
        pullback.fst h (f ≫ g) =
      pullback.fst (pullback.snd h g) f ≫ pullback.fst h g := by
  calc
    ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫ pullback.fst h (f ≫ g) =
        ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫
          (((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
            pullback.fst (pullback.snd h g) f ≫ pullback.fst h g) := by
              rw [pullbackComp_left_fst_fst f g h]
    _ = pullback.fst (pullback.snd h g) f ≫ pullback.fst h g := by
      have hi := congrArg (fun k =>
          k.left ≫ pullback.fst (pullback.snd h g) f ≫ pullback.fst h g)
        ((Over.pullbackComp f g).inv_hom_id_app (Over.mk h))
      change (((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫
          ((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
            pullback.fst (pullback.snd h g) f ≫ pullback.fst h g) =
        (pullback.fst (pullback.snd h g) f ≫ pullback.fst h g) at hi
      exact hi

private theorem eqToIso_pullback_fst {A B S : Scheme.{u}} {f g : B ⟶ S}
    (hfg : f = g) (k : A ⟶ S) :
    (eqToIso (congrArg (fun q : B ⟶ S =>
        (Over.pullback q).obj (Over.mk k)) hfg)).hom.left ≫ pullback.fst k g =
      pullback.fst k f := by
  subst g
  simp

private theorem pullbackComp_comparison_fst
    {A D T S : Scheme.{u}} (f₁ f₂ : D ⟶ T) (p : T ⟶ S)
    (hfg : f₁ ≫ p = f₂ ≫ p) (h : A ⟶ S) :
    ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
        (eqToIso (congrArg (fun q : D ⟶ S =>
          (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫
        ((Over.pullbackComp f₂ p).hom.app (Over.mk h)).left ≫
          pullback.fst (pullback.snd h p) f₂ ≫ pullback.fst h p =
      pullback.fst (pullback.snd h p) f₁ ≫ pullback.fst h p := by
  calc
    _ = ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
          (eqToIso (congrArg (fun q : D ⟶ S =>
            (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫
          pullback.fst h (f₂ ≫ p) := by
            simpa only [Category.assoc] using congrArg
              (fun k => ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
                (eqToIso (congrArg (fun q : D ⟶ S =>
                  (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫ k)
              (pullbackComp_left_fst_fst f₂ p h)
    _ = ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
          pullback.fst h (f₁ ≫ p) := by
            simpa only [Category.assoc] using congrArg
              (fun k => ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫ k)
              (eqToIso_pullback_fst hfg h)
    _ = pullback.fst (pullback.snd h p) f₁ ≫ pullback.fst h p :=
      pullbackComp_inv_fst_fst f₁ p h

theorem singleton_effective_of_fpqc {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Scheme.IsFpqcMorphism p) :
    IsEffective (fun _ : PUnit => p) := by
  sorry

theorem family_effective_of_fpqc (𝒰 : FpqcFamily S) :
    IsEffective (fun i => 𝒰.cover.f i) := by
  sorry

noncomputable def singleton_morphisms_descend_uniquely {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Scheme.IsFpqcMorphism p) :
    (overPseudofunctor.toDescentData (fun _ : PUnit => p)).FullyFaithful := by
  sorry

noncomputable def family_morphisms_descend_uniquely (𝒰 : FpqcFamily S) :
    (overPseudofunctor.toDescentData (fun i => 𝒰.cover.f i)).FullyFaithful := by
  sorry

theorem effective_unique_up_to_unique_iso {ι : Type v} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S} {D : Data f}
    (A B : Effective f D)
    (hfullyFaithful :
      (overPseudofunctor.toDescentData f).FullyFaithful) :
    Nonempty (CompatibleIso A B) ∧
      ∀ e₁ e₂ : CompatibleIso A B, e₁ = e₂ := by
  let e : A.descended ≅ B.descended :=
    hfullyFaithful.preimageIso (A.comparison.symm ≪≫ B.comparison)
  refine ⟨⟨e, ?_⟩, ?_⟩
  ·
    have hm := hfullyFaithful.map_preimage (A.comparison.symm ≪≫ B.comparison).hom
    simp only [e, Functor.FullyFaithful.preimageIso]
    rw [hm]
    simp
  · intro e₁ e₂
    apply Subtype.ext
    apply Iso.ext
    apply hfullyFaithful.map_injective
    apply (cancel_epi A.comparison.hom).1
    exact e₁.property.trans e₂.property.symm

end SchemeDescent

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
