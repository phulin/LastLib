import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Dependencies
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# 13.2 Local triviality and effectivity

The indexed overlap objects below keep the order of the transition maps visible.  In particular,
the triple-overlap equation is `g_ik = g_jk * g_ij`, matching the source convention that the
first map transports from `i` to `j`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u v

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

def Chapter13CoverProduct {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i j : ι) : Over S :=
  Over.mk (t i) ⊗ Over.mk (t j)

def Chapter13CoverTriple {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i j k : ι) : Over S :=
  Chapter13CoverProduct T t i j ⊗ Over.mk (t k)

def chapter13CoverProjectionIJ {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i j k : ι) :
    Chapter13CoverTriple T t i j k ⟶ Chapter13CoverProduct T t i j :=
  CartesianMonoidalCategory.fst _ _

def chapter13CoverProjectionJK {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i j k : ι) :
    Chapter13CoverTriple T t i j k ⟶ Chapter13CoverProduct T t j k :=
  (α_ (Over.mk (t i)) (Over.mk (t j)) (Over.mk (t k))).hom ≫
    CartesianMonoidalCategory.snd _ _

def chapter13CoverProjectionIK {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i j k : ι) :
    Chapter13CoverTriple T t i j k ⟶ Chapter13CoverProduct T t i k :=
  (α_ (Over.mk (t i)) (Over.mk (t j)) (Over.mk (t k))).hom ≫
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.snd _ _)

def chapter13CoverDiagonal {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i : ι) :
    Over.mk (t i) ⟶ Chapter13CoverProduct T t i i :=
  CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _)

/-- The factor swap on an ordered double overlap. -/
def chapter13CoverSwap {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) (i j : ι) :
    Chapter13CoverProduct T t i j ⟶ Chapter13CoverProduct T t j i :=
  (β_ (Over.mk (t i)) (Over.mk (t j))).hom

def chapter13GroupSectionOne {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    (A : Over S) : A ⟶ G.X :=
  CartesianMonoidalCategory.toUnit A ≫ MonObj.one (X := G.X)

def chapter13GroupSectionMul {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    {A : Over S} (g h : A ⟶ G.X) : A ⟶ G.X :=
  CartesianMonoidalCategory.lift g h ≫ MonObj.mul (X := G.X)

def chapter13GroupSectionInv {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    {A : Over S} (g : A ⟶ G.X) : A ⟶ G.X :=
  g ≫ GrpObj.inv (X := G.X)

def Chapter13FpqcCoverFamily {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) : Prop :=
  (∀ i, Flat (t i)) ∧
    ∀ U : S.Opens, IsCompact (U : Set S) →
      ∃ J : Finset ι, ∃ V : ∀ j : J, (T (j : ι)).Opens,
        (∀ j : J, IsCompact (V j : Set (T (j : ι)))) ∧
          (U : Set S) = ⋃ j : J, Set.image (t (j : ι)).base (V j : Set (T (j : ι)))

def Chapter13FppfCoverFamily {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) : Prop :=
  (∀ i, Flat (t i) ∧ LocallyOfFinitePresentation (t i)) ∧
    ∀ s : S, ∃ i, ∃ x : T i, (t i).base x = s

/-- Every fppf covering family has the finite-reduction property used for fpqc descent. -/
theorem chapter13_fppfCoverFamily_is_fpqcCoverFamily
    {S : Scheme.{u}} {ι : Type v}
    {T : ι → Scheme.{u}} {t : ∀ i, T i ⟶ S}
    (h : Chapter13FppfCoverFamily T t) :
    Chapter13FpqcCoverFamily T t := by
  sorry

/-- The nonabelian transition functions on all ordered double overlaps. -/
structure Chapter13TorsorCocycle {S : Scheme.{u}} {ι : Type v}
    (G : Chapter13GroupScheme S) (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) where
  transition : ∀ i j, Chapter13CoverProduct T t i j ⟶ G.X
  cocycle : ∀ i j k,
    chapter13CoverProjectionIK T t i j k ≫ transition i k =
      chapter13GroupSectionMul G
        (chapter13CoverProjectionJK T t i j k ≫ transition j k)
        (chapter13CoverProjectionIJ T t i j k ≫ transition i j)

/-- The identity cocycle associated with the trivial torsor. -/
noncomputable def chapter13IdentityTorsorCocycle
    {S : Scheme.{u}} {ι : Type v}
    (G : Chapter13GroupScheme S) (T : ι → Scheme.{u})
    (t : ∀ i, T i ⟶ S) : Chapter13TorsorCocycle G T t where
  transition i j := chapter13GroupSectionOne G (Chapter13CoverProduct T t i j)
  cocycle := by
    intro i j k
    simp only [chapter13GroupSectionOne, chapter13GroupSectionMul]
    have hIK : chapter13CoverProjectionIK T t i j k ≫
        CartesianMonoidalCategory.toUnit (Chapter13CoverProduct T t i k) =
          CartesianMonoidalCategory.toUnit (Chapter13CoverTriple T t i j k) := by
      apply CartesianMonoidalCategory.toUnit_unique
    have hJK : chapter13CoverProjectionJK T t i j k ≫
        CartesianMonoidalCategory.toUnit (Chapter13CoverProduct T t j k) =
          CartesianMonoidalCategory.toUnit (Chapter13CoverTriple T t i j k) := by
      apply CartesianMonoidalCategory.toUnit_unique
    have hIJ : chapter13CoverProjectionIJ T t i j k ≫
        CartesianMonoidalCategory.toUnit (Chapter13CoverProduct T t i j) =
          CartesianMonoidalCategory.toUnit (Chapter13CoverTriple T t i j k) := by
      apply CartesianMonoidalCategory.toUnit_unique
    rw [← Category.assoc (chapter13CoverProjectionIK T t i j k)
      (CartesianMonoidalCategory.toUnit (Chapter13CoverProduct T t i k))
      (MonObj.one (X := G.X))]
    rw [← Category.assoc (chapter13CoverProjectionJK T t i j k)
      (CartesianMonoidalCategory.toUnit (Chapter13CoverProduct T t j k))
      (MonObj.one (X := G.X))]
    rw [← Category.assoc (chapter13CoverProjectionIJ T t i j k)
      (CartesianMonoidalCategory.toUnit (Chapter13CoverProduct T t i j))
      (MonObj.one (X := G.X))]
    rw [hIK, hJK, hIJ]
    simp

theorem chapter13_trivial_torsor_is_classified_by_identity_cocycle
    {S : Scheme.{u}} {ι : Type v}
    (G : Chapter13GroupScheme S) (T : ι → Scheme.{u})
    (t : ∀ i, T i ⟶ S) :
    (chapter13IdentityTorsorCocycle G T t).transition =
      fun i j => chapter13GroupSectionOne G (Chapter13CoverProduct T t i j) :=
  rfl

theorem chapter13_torsorCocycle_normalized
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}} {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t) (i : ι) :
    chapter13CoverDiagonal T t i ≫ D.transition i i =
      chapter13GroupSectionOne G (Over.mk (t i)) := by
  let diag : Over.mk (t i) ⟶ Over.mk (t i) ⊗ Over.mk (t i) :=
    CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _)
  let d : Over.mk (t i) ⟶ (Over.mk (t i) ⊗ Over.mk (t i)) ⊗ Over.mk (t i) :=
    CartesianMonoidalCategory.lift diag (𝟙 _)
  let pIK : (Over.mk (t i) ⊗ Over.mk (t i)) ⊗ Over.mk (t i) ⟶
      Over.mk (t i) ⊗ Over.mk (t i) :=
    (α_ (Over.mk (t i)) (Over.mk (t i)) (Over.mk (t i))).hom ≫
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (Over.mk (t i)) (Over.mk (t i) ⊗ Over.mk (t i)))
        (CartesianMonoidalCategory.snd (Over.mk (t i)) (Over.mk (t i) ⊗ Over.mk (t i)) ≫
          CartesianMonoidalCategory.snd (Over.mk (t i)) (Over.mk (t i)))
  let pJK : (Over.mk (t i) ⊗ Over.mk (t i)) ⊗ Over.mk (t i) ⟶
      Over.mk (t i) ⊗ Over.mk (t i) :=
    (α_ (Over.mk (t i)) (Over.mk (t i)) (Over.mk (t i))).hom ≫
      CartesianMonoidalCategory.snd (Over.mk (t i)) (Over.mk (t i) ⊗ Over.mk (t i))
  let pIJ : (Over.mk (t i) ⊗ Over.mk (t i)) ⊗ Over.mk (t i) ⟶
      Over.mk (t i) ⊗ Over.mk (t i) :=
    CartesianMonoidalCategory.fst (Over.mk (t i) ⊗ Over.mk (t i)) (Over.mk (t i))
  have hIK : d ≫ pIK = diag := by
    dsimp [pIK, d]
    rw [← Category.assoc, CartesianMonoidalCategory.lift_lift_associator_hom]
    rw [CartesianMonoidalCategory.comp_lift]
    simp [diag]
  have hJK : d ≫ pJK = diag := by
    dsimp [pJK, d]
    rw [← Category.assoc, CartesianMonoidalCategory.lift_lift_associator_hom]
    simp [diag]
  have hIJ : d ≫ pIJ = diag := by
    simp [pIJ, d]
  have hc : pIK ≫ D.transition i i =
      CartesianMonoidalCategory.lift (pJK ≫ D.transition i i)
        (pIJ ≫ D.transition i i) ≫ MonObj.mul (X := G.X) := by
    simpa [pIK, pJK, pIJ, chapter13CoverProjectionIK,
      chapter13CoverProjectionJK, chapter13CoverProjectionIJ,
      Chapter13CoverTriple, Chapter13CoverProduct,
      chapter13GroupSectionMul] using D.cocycle i i i
  let tr : (Over.mk (t i) ⊗ Over.mk (t i)) ⟶ G.X := D.transition i i
  have htr : tr = D.transition i i := by rfl
  have hcomp := congrArg (fun f => d ≫ f) hc
  rw [← htr] at hcomp
  have hmul : diag ≫ tr =
      CartesianMonoidalCategory.lift (diag ≫ tr) (diag ≫ tr) ≫
        MonObj.mul (X := G.X) := by
    calc
      diag ≫ tr = d ≫ pIK ≫ tr := by
        rw [← hIK]
        simp
      _ = d ≫ CartesianMonoidalCategory.lift (pJK ≫ tr) (pIJ ≫ tr) ≫
          MonObj.mul := hcomp
      _ = CartesianMonoidalCategory.lift (d ≫ (pJK ≫ tr))
          (d ≫ (pIJ ≫ tr)) ≫ MonObj.mul := by
        rw [← Category.assoc d (CartesianMonoidalCategory.lift _ _)]
        rw [CartesianMonoidalCategory.comp_lift]
      _ = CartesianMonoidalCategory.lift (diag ≫ tr) (diag ≫ tr) ≫
          MonObj.mul := by
        rw [← Category.assoc d pJK tr, hJK,
          ← Category.assoc d pIJ tr, hIJ]
  have hunit : diag ≫ tr =
      CartesianMonoidalCategory.toUnit (Over.mk (t i)) ≫ MonObj.one := by
    have h := (GrpObj.eq_lift_inv_left (diag ≫ tr) (diag ≫ tr)
      (diag ≫ tr)).mpr hmul.symm
    rw [GrpObj.lift_comp_inv_left] at h
    exact h
  rw [htr] at hunit
  change CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _) ≫ D.transition i i =
    CartesianMonoidalCategory.toUnit (Over.mk (t i)) ≫ MonObj.one
  exact hunit

/-- The inverse transition is obtained by swapping the two factors of the overlap. -/
theorem chapter13_torsorCocycle_inverse
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}} {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t) (i j : ι) :
    chapter13CoverSwap T t i j ≫ D.transition j i =
      chapter13GroupSectionInv G (D.transition i j) := by
  sorry

/-- Left translation by a group-valued function on an overlap. -/
def chapter13LeftTranslation {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    {A : Over S} (h : A ⟶ G.X) : A ⊗ G.X ⟶ A ⊗ G.X :=
  CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst A G.X)
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst A G.X ≫ h)
        (CartesianMonoidalCategory.snd A G.X) ≫ MonObj.mul (X := G.X))

noncomputable def chapter13LeftTranslationIso {S : Scheme.{u}}
    (G : Chapter13GroupScheme S) {A : Over S} (h : A ⟶ G.X) :
    A ⊗ G.X ≅ A ⊗ G.X :=
  { hom := chapter13LeftTranslation G h
    inv := chapter13LeftTranslation G (chapter13GroupSectionInv G h)
    hom_inv_id := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [chapter13LeftTranslation, chapter13GroupSectionInv]
      · dsimp [chapter13LeftTranslation, chapter13GroupSectionInv]
        rw [← Category.assoc]
        rw [CartesianMonoidalCategory.comp_lift]
        rw [CartesianMonoidalCategory.lift_snd]
        rw [← Category.assoc]
        rw [CartesianMonoidalCategory.comp_lift]
        simp [Category.assoc]
        apply (GrpObj.lift_inv_left_eq
          (SemiCartesianMonoidalCategory.fst A G.X ≫ h)
          (CartesianMonoidalCategory.lift
            (SemiCartesianMonoidalCategory.fst A G.X ≫ h)
            (SemiCartesianMonoidalCategory.snd A G.X) ≫ MonObj.mul)
          (SemiCartesianMonoidalCategory.snd A G.X)).mpr
        rfl
    inv_hom_id := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [chapter13LeftTranslation, chapter13GroupSectionInv]
      · dsimp [chapter13LeftTranslation, chapter13GroupSectionInv]
        rw [← Category.assoc]
        rw [CartesianMonoidalCategory.comp_lift]
        rw [CartesianMonoidalCategory.lift_snd]
        rw [← Category.assoc]
        rw [CartesianMonoidalCategory.comp_lift]
        have h_assoc (f g k : A ⊗ G.X ⟶ G.X) :
            CartesianMonoidalCategory.lift f
                (CartesianMonoidalCategory.lift g k ≫ MonObj.mul) =
              CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift f g) k ≫
                (α_ G.X G.X G.X).hom ≫ (𝟙 G.X ⊗ₘ MonObj.mul) := by
          apply CartesianMonoidalCategory.hom_ext
          · simp [MonoidalCategory.tensorHom_def]
          · simp [MonoidalCategory.tensorHom_def]
        simp [Category.assoc]
        rw [h_assoc]
        have htail :
            (α_ G.X G.X G.X).hom ≫ (𝟙 G.X ⊗ₘ MonObj.mul) ≫ MonObj.mul =
              (MonObj.mul ▷ G.X) ≫ MonObj.mul := by
          rw [MonObj.mul_assoc]
          simp [MonoidalCategory.tensorHom_def]
        have hq (f g k : A ⊗ G.X ⟶ G.X) :
            CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift f g) k ≫
                (MonObj.mul ▷ G.X) =
              CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.lift f g ≫ MonObj.mul) k := by
          apply CartesianMonoidalCategory.hom_ext
          · simp
          · simp
        rw [Category.assoc]
        rw [Category.assoc (α_ G.X G.X G.X).hom (𝟙 G.X ⊗ₘ MonObj.mul)
          MonObj.mul]
        rw [htail]
        rw [← Category.assoc]
        rw [hq]
        rw [← Category.assoc (SemiCartesianMonoidalCategory.fst A G.X) h
          (GrpObj.inv (X := G.X))]
        simp only [GrpObj.lift_comp_inv_right]
        simp
    }

/-- The right regular action on the second factor of `A ×_S G`. -/
noncomputable def chapter13FiberRegularRightAction {S : Scheme.{u}}
    (G : Chapter13GroupScheme S) (A : Over S) :
    Chapter13RightAction G (A ⊗ G.X) where
  act := (α_ A G.X G.X).hom ≫ (𝟙 A ⊗ₘ MonObj.mul (X := G.X))
  one_act := by
    simp [MonoidalCategory.tensorHom_def, Category.assoc]
    have hmap :
        A ◁ G.X ◁ MonObj.one ≫ A ◁ MonObj.mul =
          A ◁ (G.X ◁ MonObj.one ≫ MonObj.mul) := by
      change ((tensoringLeft (Over S)).obj A).map (G.X ◁ MonObj.one) ≫
          ((tensoringLeft (Over S)).obj A).map MonObj.mul =
        ((tensoringLeft (Over S)).obj A).map (G.X ◁ MonObj.one ≫ MonObj.mul)
      exact (((tensoringLeft (Over S)).obj A).map_comp _ _).symm
    rw [hmap, MonObj.mul_one]
    simp
  mul_act := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [MonoidalCategory.tensorHom_def, Category.assoc]
    · simp [MonoidalCategory.tensorHom_def, Category.assoc]
      have hprefix :
          (α_ A G.X G.X).hom ▷ G.X ≫
              (α_ A (G.X ⊗ G.X) G.X).hom ≫
                CartesianMonoidalCategory.snd A ((G.X ⊗ G.X) ⊗ G.X) ≫
                  (α_ G.X G.X G.X).hom =
            (α_ (A ⊗ G.X) G.X G.X).hom ≫
              (α_ A G.X (G.X ⊗ G.X)).hom ≫
                CartesianMonoidalCategory.snd A (G.X ⊗ (G.X ⊗ G.X)) := by
        apply CartesianMonoidalCategory.hom_ext
        · cat_disch
        · cat_disch
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ G.X ◁ MonObj.mul ≫ MonObj.mul) hprefix

noncomputable def chapter13_leftTranslation_is_equivariant
    {S : Scheme.{u}} (G : Chapter13GroupScheme S) {A : Over S}
    (h : A ⟶ G.X) :
    Chapter13EquivariantIso
      (chapter13FiberRegularRightAction G A)
      (chapter13FiberRegularRightAction G A) := by
  exact
    { iso := chapter13LeftTranslationIso G h
      equivariant := by
        dsimp [chapter13LeftTranslationIso, chapter13FiberRegularRightAction]
        apply CartesianMonoidalCategory.hom_ext
        · simp [chapter13LeftTranslation, MonoidalCategory.tensorHom_def, Category.assoc]
        · simp [chapter13LeftTranslation, MonoidalCategory.tensorHom_def, Category.assoc]
          let f : ((A ⊗ G.X) ⊗ G.X) ⟶ G.X :=
            CartesianMonoidalCategory.fst (A ⊗ G.X) G.X ≫
              CartesianMonoidalCategory.fst A G.X ≫ h
          let g : ((A ⊗ G.X) ⊗ G.X) ⟶ G.X :=
            CartesianMonoidalCategory.fst (A ⊗ G.X) G.X ≫
              CartesianMonoidalCategory.snd A G.X
          let k : ((A ⊗ G.X) ⊗ G.X) ⟶ G.X :=
            CartesianMonoidalCategory.snd (A ⊗ G.X) G.X
          have hleft :
              CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst A G.X)
                  (CartesianMonoidalCategory.lift
                    (CartesianMonoidalCategory.fst A G.X ≫ h)
                    (CartesianMonoidalCategory.snd A G.X) ≫ MonObj.mul) ▷ G.X ≫
                  (α_ A G.X G.X).hom ≫
                    CartesianMonoidalCategory.snd A (G.X ⊗ G.X) =
                CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.lift f g ≫ MonObj.mul) k := by
            apply CartesianMonoidalCategory.hom_ext
            · simp [Category.assoc]
              rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
            · simp [f, g, k, Category.assoc]
          have hproject :
              (α_ A G.X G.X).hom ≫
                  CartesianMonoidalCategory.snd A (G.X ⊗ G.X) =
                CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.fst (A ⊗ G.X) G.X ≫
                    CartesianMonoidalCategory.snd A G.X)
                  (CartesianMonoidalCategory.snd (A ⊗ G.X) G.X) := by
            apply CartesianMonoidalCategory.hom_ext <;>
              simp [Category.assoc]
          have hright :
              (α_ A G.X G.X).hom ≫ A ◁ MonObj.mul ≫
                  CartesianMonoidalCategory.lift
                    (CartesianMonoidalCategory.fst A G.X ≫ h)
                    (CartesianMonoidalCategory.snd A G.X) =
                CartesianMonoidalCategory.lift f
                  (CartesianMonoidalCategory.lift g k ≫ MonObj.mul) := by
            rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
            apply CartesianMonoidalCategory.hom_ext
            · simp [f, g, k, Category.assoc]
            · simp [f, g, k, Category.assoc]
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ MonObj.mul) hproject
          calc
            _ = CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.lift f g ≫ MonObj.mul) k ≫ MonObj.mul := by
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ MonObj.mul) hleft
            _ = CartesianMonoidalCategory.lift f
                  (CartesianMonoidalCategory.lift g k ≫ MonObj.mul) ≫ MonObj.mul :=
              MonObj.lift_lift_assoc f g k
            _ = _ := by
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ MonObj.mul) hright.symm }

noncomputable def chapter13_torsorCocycle_transition_is_equivariant
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t) (i j : ι) :
    Chapter13EquivariantIso
      (chapter13FiberRegularRightAction G (Chapter13CoverProduct T t i j))
      (chapter13FiberRegularRightAction G (Chapter13CoverProduct T t i j)) := by
  exact chapter13_leftTranslation_is_equivariant G (D.transition i j)

def chapter13GaugeTransition {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t)
    (h : ∀ i, Over.mk (t i) ⟶ G.X) (i j : ι) :
    Chapter13CoverProduct T t i j ⟶ G.X :=
  chapter13GroupSectionMul G
    (CartesianMonoidalCategory.snd _ _ ≫ h j)
    (chapter13GroupSectionMul G
      (D.transition i j)
      (chapter13GroupSectionInv G (CartesianMonoidalCategory.fst _ _ ≫ h i)))

noncomputable def chapter13_gaugeTransition_is_cocycle
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t)
    (h : ∀ i, Over.mk (t i) ⟶ G.X) :
    Chapter13TorsorCocycle G T t where
  transition := chapter13GaugeTransition D h
  cocycle := by
    intro i j k
    let pIK := chapter13CoverProjectionIK T t i j k
    let pJK := chapter13CoverProjectionJK T t i j k
    let pIJ := chapter13CoverProjectionIJ T t i j k
    let ik_k : Chapter13CoverProduct T t i k ⟶ Over.mk (t k) :=
      CartesianMonoidalCategory.snd _ _
    let ik_i : Chapter13CoverProduct T t i k ⟶ Over.mk (t i) :=
      CartesianMonoidalCategory.fst _ _
    let jk_k : Chapter13CoverProduct T t j k ⟶ Over.mk (t k) :=
      CartesianMonoidalCategory.snd _ _
    let jk_j : Chapter13CoverProduct T t j k ⟶ Over.mk (t j) :=
      CartesianMonoidalCategory.fst _ _
    let ij_j : Chapter13CoverProduct T t i j ⟶ Over.mk (t j) :=
      CartesianMonoidalCategory.snd _ _
    let ij_i : Chapter13CoverProduct T t i j ⟶ Over.mk (t i) :=
      CartesianMonoidalCategory.fst _ _
    have hmul_comp {A B : Over S} (f : A ⟶ B)
        {g h' : B ⟶ G.X} :
        f ≫ chapter13GroupSectionMul G g h' =
          chapter13GroupSectionMul G (f ≫ g) (f ≫ h') := by
      dsimp [chapter13GroupSectionMul]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    have hinv_comp {A B : Over S} (f : A ⟶ B) (g : B ⟶ G.X) :
        f ≫ chapter13GroupSectionInv G g =
          chapter13GroupSectionInv G (f ≫ g) := by
      rfl
    have hIK_k : pIK ≫ ik_k = pJK ≫ jk_k := by
      dsimp [pIK, pJK, ik_k, jk_k, chapter13CoverProjectionIK,
        chapter13CoverProjectionJK, Chapter13CoverTriple, Chapter13CoverProduct]
      cat_disch
    have hIK_i : pIK ≫ ik_i = pIJ ≫ ij_i := by
      dsimp [pIK, pIJ, ik_i, ij_i, chapter13CoverProjectionIK,
        chapter13CoverProjectionIJ, Chapter13CoverTriple, Chapter13CoverProduct]
      cat_disch
    have hJK_j : pJK ≫ jk_j = pIJ ≫ ij_j := by
      dsimp [pJK, pIJ, jk_j, ij_j, chapter13CoverProjectionJK,
        chapter13CoverProjectionIJ, Chapter13CoverTriple, Chapter13CoverProduct]
      cat_disch
    have hD := D.cocycle i j k
    have hD' : pIK ≫ D.transition i k =
        chapter13GroupSectionMul G (pJK ≫ D.transition j k)
          (pIJ ≫ D.transition i j) := by
      simpa [pIK, pJK, pIJ] using hD
    have hIK_k_h : pIK ≫ (ik_k ≫ h k) = pJK ≫ (jk_k ≫ h k) := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => f ≫ h k) hIK_k
    have hIK_i_h : pIK ≫ (ik_i ≫ h i) = pIJ ≫ (ij_i ≫ h i) := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => f ≫ h i) hIK_i
    have hJK_j_h : pJK ≫ (jk_j ≫ h j) = pIJ ≫ (ij_j ≫ h j) := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => f ≫ h j) hJK_j
    have hassoc {W : Over S} (a b c : W ⟶ G.X) :
        chapter13GroupSectionMul G a (chapter13GroupSectionMul G b c) =
          chapter13GroupSectionMul G
            (chapter13GroupSectionMul G a b) c := by
      simpa [chapter13GroupSectionMul] using (MonObj.lift_lift_assoc a b c).symm
    have hcancel {W : Over S} (a : W ⟶ G.X) :
        chapter13GroupSectionMul G a (chapter13GroupSectionInv G a) =
          chapter13GroupSectionOne G W := by
      dsimp [chapter13GroupSectionMul, chapter13GroupSectionInv,
        chapter13GroupSectionOne]
      exact GrpObj.lift_comp_inv_right a
    have hcancel_left {W : Over S} (a : W ⟶ G.X) :
        chapter13GroupSectionMul G (chapter13GroupSectionInv G a) a =
          chapter13GroupSectionOne G W := by
      dsimp [chapter13GroupSectionMul, chapter13GroupSectionInv,
        chapter13GroupSectionOne]
      exact GrpObj.lift_comp_inv_left a
    have hcancel_middle {W : Over S} (a b : W ⟶ G.X) :
        chapter13GroupSectionMul G
            (chapter13GroupSectionMul G a (chapter13GroupSectionInv G b)) b = a := by
      rw [← hassoc, hcancel_left]
      simp [chapter13GroupSectionMul, chapter13GroupSectionOne]
    change
      pIK ≫ chapter13GroupSectionMul G
          (ik_k ≫ h k)
          (chapter13GroupSectionMul G
            (D.transition i k)
            (chapter13GroupSectionInv G
              (ik_i ≫ h i))) =
        chapter13GroupSectionMul G
          (pJK ≫ chapter13GroupSectionMul G
            (jk_k ≫ h k)
            (chapter13GroupSectionMul G
              (D.transition j k)
              (chapter13GroupSectionInv G
                (jk_j ≫ h j))))
          (pIJ ≫ chapter13GroupSectionMul G
            (ij_j ≫ h j)
            (chapter13GroupSectionMul G
              (D.transition i j)
              (chapter13GroupSectionInv G
                (ij_i ≫ h i))))
    simp_rw [hmul_comp]
    simp_rw [hinv_comp]
    rw [hD', hIK_k_h, hIK_i_h, hJK_j_h]
    simp_rw [hassoc]
    rw [hcancel_middle]

/- A chosen family of local trivializations has a transition function on every
ordered overlap.  The construction is kept as a named interface so later
descent statements can require the transition function to be the one induced
by the trivializations, rather than an unrelated morphism. -/
noncomputable def chapter13LocalTrivializationTransition
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (Q : Chapter13FpqcTorsor G)
    (trivialization : ∀ i,
      Chapter13TorsorLocalTrivialization Q.action (t i)) (i j : ι) :
    Chapter13CoverProduct T t i j ⟶ G.X := by
  sorry

noncomputable def chapter13_localTrivializationTransition_is_equivariant
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (Q : Chapter13FpqcTorsor G)
    (trivialization : ∀ i,
      Chapter13TorsorLocalTrivialization Q.action (t i)) (i j : ι) :
    Chapter13EquivariantIso
      (chapter13FiberRegularRightAction G (Chapter13CoverProduct T t i j))
      (chapter13FiberRegularRightAction G (Chapter13CoverProduct T t i j)) :=
  chapter13_leftTranslation_is_equivariant G
    (chapter13LocalTrivializationTransition Q trivialization i j)

/-- The transition functions induced by local trivializations satisfy the triple cocycle. -/
noncomputable def chapter13LocalTrivializationCocycle
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (Q : Chapter13FpqcTorsor G)
    (trivialization : ∀ i,
      Chapter13TorsorLocalTrivialization Q.action (t i)) :
    Chapter13TorsorCocycle G T t where
  transition := chapter13LocalTrivializationTransition Q trivialization
  cocycle := by sorry

/- Gauge equivalence is the change-of-trivialization relation on nonabelian
cocycles.  Bundling its witness keeps the order `h_j g_ij h_i⁻¹` explicit. -/
structure Chapter13TorsorCocycleGaugeEquivalence
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D E : Chapter13TorsorCocycle G T t) where
  gauge : ∀ i, Over.mk (t i) ⟶ G.X
  intertwines : ∀ i j,
    E.transition i j = chapter13GaugeTransition D gauge i j

def chapter13TorsorCocycleGaugeEquivalent
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D E : Chapter13TorsorCocycle G T t) : Prop :=
  Nonempty (Chapter13TorsorCocycleGaugeEquivalence D E)

/-- Local triviality data for a family of fpqc members. -/
structure Chapter13FpqcTorsorDescentData {S : Scheme.{u}} {ι : Type v}
    (G : Chapter13GroupScheme S) (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) where
  cover : Chapter13FpqcCoverFamily T t
  cocycle : Chapter13TorsorCocycle G T t

/-- The fppf version of the indexed local-triviality datum. -/
structure Chapter13FppfTorsorDescentData {S : Scheme.{u}} {ι : Type v}
    (G : Chapter13GroupScheme S) (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) where
  cover : Chapter13FppfCoverFamily T t
  cocycle : Chapter13TorsorCocycle G T t

/- A cocycle realization records the descended torsor, the chosen local
trivializations, and the fact that their overlap changes are the prescribed
transition functions. -/
structure Chapter13TorsorCocycleRealization
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t) where
  cover : Chapter13FpqcCoverFamily T t
  torsor : Chapter13FpqcTorsor G
  trivialization : ∀ i,
    Chapter13TorsorLocalTrivialization torsor.action (t i)
  transition_compatibility : ∀ i j,
    D.transition i j =
      chapter13LocalTrivializationTransition torsor trivialization i j
  transition_equivariant_compatibility : ∀ i j,
    chapter13_localTrivializationTransition_is_equivariant
        torsor trivialization i j =
      chapter13_torsorCocycle_transition_is_equivariant D i j

theorem chapter13_torsorCocycle_realized_by_torsor
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t)
    (hcover : Chapter13FpqcCoverFamily T t)
    (hG : Chapter13FpqcCover G.X.hom) :
    Nonempty (Chapter13TorsorCocycleRealization D) := by
  sorry

theorem chapter13_gaugeEquivalent_cocycles_give_equivariantly_isomorphic_torsors
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D E : Chapter13TorsorCocycle G T t)
    (RD : Chapter13TorsorCocycleRealization D)
    (RE : Chapter13TorsorCocycleRealization E)
    (h : chapter13TorsorCocycleGaugeEquivalent D E) :
    Nonempty (Chapter13EquivariantIso RD.torsor.action RE.torsor.action) := by
  sorry

theorem chapter13_equivariantly_isomorphic_torsor_realizations_give_gaugeEquivalent_cocycles
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D E : Chapter13TorsorCocycle G T t)
    (RD : Chapter13TorsorCocycleRealization D)
    (RE : Chapter13TorsorCocycleRealization E)
    (h : Nonempty (Chapter13EquivariantIso RD.torsor.action RE.torsor.action)) :
    chapter13TorsorCocycleGaugeEquivalent D E := by
  sorry

theorem chapter13_torsorCocycle_realizations_gauge_iff_equivariantly_isomorphic
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D E : Chapter13TorsorCocycle G T t)
    (RD : Chapter13TorsorCocycleRealization D)
    (RE : Chapter13TorsorCocycleRealization E) :
    chapter13TorsorCocycleGaugeEquivalent D E ↔
      Nonempty (Chapter13EquivariantIso RD.torsor.action RE.torsor.action) := by
  constructor
  · intro h
    exact chapter13_gaugeEquivalent_cocycles_give_equivariantly_isomorphic_torsors
      D E RD RE h
  · intro h
    exact chapter13_equivariantly_isomorphic_torsor_realizations_give_gaugeEquivalent_cocycles
      D E RD RE h

theorem chapter13_fpqc_torsor_descent_effective
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FpqcTorsorDescentData G T t)
    (hG : Chapter13FpqcCover G.X.hom) :
    Nonempty (Chapter13FpqcTorsor G) := by
  sorry

theorem chapter13_fppf_torsor_descent_effective
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FppfTorsorDescentData G T t)
    (hG : Chapter13FppfCover G.X.hom) :
    Nonempty (Chapter13FppfTorsor G) := by
  sorry

theorem chapter13_fpqc_descent_produces_locally_trivial_torsor
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FpqcTorsorDescentData G T t)
    (hG : Chapter13FpqcCover G.X.hom) :
    ∃ Q : Chapter13FpqcTorsor G, ∀ i,
      Nonempty (Chapter13TorsorLocalTrivialization Q.action (t i)) := by
  sorry

theorem chapter13_fppf_descent_produces_locally_trivial_torsor
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FppfTorsorDescentData G T t)
    (hG : Chapter13FppfCover G.X.hom) :
    ∃ Q : Chapter13FppfTorsor G, ∀ i,
      Nonempty (Chapter13TorsorLocalTrivialization Q.action (t i)) := by
  sorry

theorem chapter13_torsor_tautological_trivialization
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G) :
    Nonempty (Chapter13TorsorLocalTrivialization Q.action Q.carrier.hom) := by
  sorry

theorem chapter13_torsor_is_locally_trivial
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G) :
    ∃ (T : Scheme.{u}) (t : T ⟶ S),
      Chapter13FpqcCover t ∧
        Nonempty (Chapter13TorsorLocalTrivialization Q.action t) := by
  sorry

theorem chapter13_fppf_torsor_is_locally_trivial
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FppfTorsor G) :
    ∃ (T : Scheme.{u}) (t : T ⟶ S),
      Chapter13FppfCover t ∧
        Nonempty (Chapter13TorsorLocalTrivialization Q.action t) := by
  sorry

theorem chapter13_fpqcCover_of_fpqc_baseChange
    {S T X : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)
    (ht : Chapter13FpqcCover t)
    (hbase : Chapter13FpqcCover (pullback.snd f t)) :
    Chapter13FpqcCover f := by
  sorry

theorem chapter13_fppfCover_of_fppf_baseChange
    {S T X : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)
    (ht : Chapter13FppfCover t)
    (hbase : Chapter13FppfCover (pullback.snd f t)) :
    Chapter13FppfCover f := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
