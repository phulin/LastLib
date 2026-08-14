import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Dependencies

/-!
# 13.2 Local triviality and effectivity

The indexed overlap objects below keep the order of the transition maps visible.  In particular,
the triple-overlap equation is `g_ik = g_jk * g_ij`, matching the source convention that the
first map transports from `i` to `j`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonObj

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

def chapter13GroupSectionOne {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    (A : Over S) : A ⟶ G.X :=
  CartesianMonoidalCategory.toUnit A ≫ η[G.X]

def chapter13GroupSectionMul {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    {A : Over S} (g h : A ⟶ G.X) : A ⟶ G.X :=
  CartesianMonoidalCategory.lift g h ≫ μ[G.X]

def chapter13GroupSectionInv {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    {A : Over S} (g : A ⟶ G.X) : A ⟶ G.X :=
  g ≫ GrpObj.inv (X := G.X)

def Chapter13FpqcCoverFamily {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) : Prop :=
  (∀ i, Flat (t i) ∧ QuasiCompact (t i)) ∧
    ∀ s : S, ∃ i, ∃ x : T i, (t i).base x = s

def Chapter13FppfCoverFamily {S : Scheme.{u}} {ι : Type v}
    (T : ι → Scheme.{u}) (t : ∀ i, T i ⟶ S) : Prop :=
  (∀ i, Flat (t i) ∧ LocallyOfFinitePresentation (t i)) ∧
    ∀ s : S, ∃ i, ∃ x : T i, (t i).base x = s

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
  cocycle := by sorry

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
  sorry

/-- Left translation by a group-valued function on an overlap. -/
def chapter13LeftTranslation {S : Scheme.{u}} (G : Chapter13GroupScheme S)
    {A : Over S} (h : A ⟶ G.X) : A ⊗ G.X ⟶ A ⊗ G.X :=
  CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst A G.X)
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst A G.X ≫ h)
        (CartesianMonoidalCategory.snd A G.X) ≫ μ[G.X])

noncomputable def chapter13LeftTranslationIso {S : Scheme.{u}}
    (G : Chapter13GroupScheme S) {A : Over S} (h : A ⟶ G.X) :
    A ⊗ G.X ≅ A ⊗ G.X :=
  { hom := chapter13LeftTranslation G h
    inv := chapter13LeftTranslation G (chapter13GroupSectionInv G h)
    hom_inv_id := by sorry
    inv_hom_id := by sorry }

/-- The right regular action on the second factor of `A ×_S G`. -/
noncomputable def chapter13FiberRegularRightAction {S : Scheme.{u}}
    (G : Chapter13GroupScheme S) (A : Over S) :
    Chapter13RightAction G (A ⊗ G.X) where
  act := (α_ A G.X G.X).hom ≫ (𝟙 A ⊗ₘ μ[G.X])
  one_act := by sorry
  mul_act := by sorry

theorem chapter13_leftTranslation_is_equivariant
    {S : Scheme.{u}} (G : Chapter13GroupScheme S) {A : Over S}
    (h : A ⟶ G.X) :
    Chapter13EquivariantIso
      (chapter13FiberRegularRightAction G A)
      (chapter13FiberRegularRightAction G A) := by
  exact
    { iso := chapter13LeftTranslationIso G h
      equivariant := by sorry }

theorem chapter13_torsorCocycle_transition_is_equivariant
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

theorem chapter13_gaugeTransition_is_cocycle
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13TorsorCocycle G T t)
    (h : ∀ i, Over.mk (t i) ⟶ G.X) :
    Chapter13TorsorCocycle G T t where
  transition := chapter13GaugeTransition D h
  cocycle := by sorry

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

theorem chapter13_fpqc_torsor_descent_effective
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FpqcTorsorDescentData G T t) :
    Nonempty (Chapter13FpqcTorsor G) := by
  sorry

theorem chapter13_fppf_torsor_descent_effective
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FppfTorsorDescentData G T t) :
    Nonempty (Chapter13FppfTorsor G) := by
  sorry

theorem chapter13_fpqc_descent_produces_locally_trivial_torsor
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FpqcTorsorDescentData G T t) :
    ∃ Q : Chapter13FpqcTorsor G, ∀ i,
      Nonempty (Chapter13TorsorLocalTrivialization Q.action (t i)) := by
  sorry

theorem chapter13_fppf_descent_produces_locally_trivial_torsor
    {S : Scheme.{u}} {ι : Type v}
    {G : Chapter13GroupScheme S} {T : ι → Scheme.{u}}
    {t : ∀ i, T i ⟶ S}
    (D : Chapter13FppfTorsorDescentData G T t) :
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
