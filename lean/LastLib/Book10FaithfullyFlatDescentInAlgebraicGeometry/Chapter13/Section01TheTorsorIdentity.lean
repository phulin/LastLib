import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Dependencies

/-!
# 13.1 The torsor identity

The displayed isomorphism is kept as a scheme morphism, while the pointwise formulation is stated
in the internal language of `Over S`.  This makes the uniqueness clause available without choosing
geometric points.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry MonObj

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

theorem chapter13_torsorIdentity_iff_unique
    {S : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) :
    Chapter13TorsorIdentity A ↔
      ∀ (T : Over S) (p q : T ⟶ P),
        ∃! g : T ⟶ G.X,
          CartesianMonoidalCategory.lift p g ≫ A.act = q := by
  constructor
  · intro h T p q
    change IsIso (chapter13TorsorComparisonMap A) at h
    let c : (P ⊗ G.X) ⟶ (P ⊗ P) :=
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst P G.X) A.act
    have hc : IsIso c := by
      let : IsIso ((Over.forget S).map c) := by
        change IsIso c.left
        simpa [c, chapter13TorsorComparisonMap] using h
      exact isIso_of_reflects_iso c (Over.forget S)
    let := hc
    let g : T ⟶ G.X :=
      CartesianMonoidalCategory.lift p q ≫ inv c ≫
        CartesianMonoidalCategory.snd P G.X
    refine ⟨g, ?_, ?_⟩
    · have hfg : CartesianMonoidalCategory.lift p g =
      CartesianMonoidalCategory.lift p q ≫ inv c := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [CartesianMonoidalCategory.lift_fst]
          rw [← CartesianMonoidalCategory.lift_fst p q]
          have hcfst : c ≫ CartesianMonoidalCategory.fst P P =
              CartesianMonoidalCategory.fst P G.X := by
            simp [c]
          rw [← hcfst]
          simp [Category.assoc]
        · simp [g, Category.assoc]
      change CartesianMonoidalCategory.lift p g ≫ A.act = q
      rw [hfg]
      have hcsnd : c ≫ CartesianMonoidalCategory.snd P P = A.act := by
        simp [c]
      rw [← hcsnd]
      simp [Category.assoc]
    · intro g' hg'
      have hcomp : CartesianMonoidalCategory.lift p g' ≫ c =
          CartesianMonoidalCategory.lift p q := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [c]
        · simp [c, hg']
      calc
        g' = CartesianMonoidalCategory.lift p g' ≫
            CartesianMonoidalCategory.snd P G.X := by simp
        _ = (CartesianMonoidalCategory.lift p g' ≫ c) ≫ inv c ≫
            CartesianMonoidalCategory.snd P G.X := by simp [Category.assoc]
        _ = CartesianMonoidalCategory.lift p q ≫ inv c ≫
            CartesianMonoidalCategory.snd P G.X := by rw [hcomp]
        _ = g := rfl
  · intro h
    let c : (P ⊗ G.X) ⟶ (P ⊗ P) :=
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst P G.X) A.act
    obtain ⟨g, hg, huniq⟩ :=
      h (P ⊗ P) (CartesianMonoidalCategory.fst P P)
        (CartesianMonoidalCategory.snd P P)
    let d : (P ⊗ P) ⟶ (P ⊗ G.X) :=
      CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst P P) g
    have hdc : d ≫ c = 𝟙 (P ⊗ P) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [d, c]
      · simp [d, c, hg]
    obtain ⟨gC, hgC, huniqC⟩ :=
      h (P ⊗ G.X) (CartesianMonoidalCategory.fst P G.X) A.act
    have hcfst : c ≫ CartesianMonoidalCategory.fst P P =
        CartesianMonoidalCategory.fst P G.X := by
      simp [c]
    have hcg :
        CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst P G.X)
            (c ≫ g) ≫ A.act = A.act := by
      calc
        CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst P G.X)
              (c ≫ g) ≫ A.act =
            (c ≫ CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst P P) g) ≫ A.act := by
                simp [CartesianMonoidalCategory.comp_lift, hcfst]
        _ = c ≫ (CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst P P) g ≫ A.act) := by
                simp only [Category.assoc]
        _ = c ≫ CartesianMonoidalCategory.snd P P := by rw [hg]
        _ = A.act := by simp [c]
    have hsnd :
        CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst P G.X)
            (CartesianMonoidalCategory.snd P G.X) ≫ A.act = A.act := by
      simp
    have hcg_eq : c ≫ g = CartesianMonoidalCategory.snd P G.X :=
      (huniqC _ hcg).trans (huniqC _ hsnd).symm
    have hcd : c ≫ d = 𝟙 (P ⊗ G.X) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [d, c]
      · simpa [d, Category.assoc] using hcg_eq
    let : IsIso c := ⟨⟨d, hcd, hdc⟩⟩
    change IsIso ((Over.forget S).map c)
    exact Functor.map_isIso (Over.forget S) c

theorem chapter13_torsorIdentity_is_stable_under_baseChange
    {S T : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) (t : T ⟶ S)
    (h : Chapter13TorsorIdentity A) :
    Chapter13TorsorIdentity (chapter13BaseChangedRightAction A t) := by
  change IsIso (chapter13TorsorComparisonMap A) at h
  let c : (P ⊗ G.X) ⟶ (P ⊗ P) :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst P G.X) A.act
  have hc : IsIso c := by
    let : IsIso ((Over.forget S).map c) := by
      change IsIso c.left
      simpa [c, chapter13TorsorComparisonMap] using h
    exact isIso_of_reflects_iso c (Over.forget S)
  let F := Over.pullback t
  let c' : (F.obj P ⊗ F.obj G.X) ⟶ (F.obj P ⊗ F.obj P) :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (F.obj P) (F.obj G.X))
      (Functor.LaxMonoidal.μ F P G.X ≫ F.map A.act)
  let : IsIso c := hc
  let : IsIso (Functor.LaxMonoidal.μ F P G.X) := by
    rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory]
    infer_instance
  let : IsIso (Functor.LaxMonoidal.μ F P P) := by
    rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory]
    infer_instance
  have hfactor : c' = Functor.LaxMonoidal.μ F P G.X ≫ F.map c ≫
      inv (Functor.LaxMonoidal.μ F P P) := by
    apply CartesianMonoidalCategory.hom_ext
    · dsimp [c']
      rw [CartesianMonoidalCategory.lift_fst]
      rw [← Functor.Monoidal.μ_fst F P P]
      simp [c, F]
    · dsimp [c']
      rw [CartesianMonoidalCategory.lift_snd]
      rw [← Functor.Monoidal.μ_snd F P P]
      simp [c, F]
  have hsq : c' ≫ Functor.LaxMonoidal.μ F P P =
      Functor.LaxMonoidal.μ F P G.X ≫ F.map c := by
    rw [hfactor]
    simp [Category.assoc]
  let : IsIso (c' ≫ Functor.LaxMonoidal.μ F P P) := by
    rw [hsq]
    infer_instance
  let : IsIso c' := IsIso.of_isIso_comp_right c'
    (Functor.LaxMonoidal.μ F P P)
  have hc' : IsIso ((Over.forget T).map c') := Functor.map_isIso (Over.forget T) c'
  simpa [Chapter13TorsorIdentity, chapter13TorsorComparisonMap, c',
    chapter13BaseChangedRightAction, chapter13BaseChangedGroup, Functor.mapGrp, F,
    ← Functor.Monoidal.μ_of_cartesianMonoidalCategory] using hc'

theorem chapter13_torsorIdentity_of_fpqc_baseChange
    {S T : Scheme.{u}} {G : Chapter13GroupScheme S} {P : Chapter13SchemeOver S}
    (A : Chapter13RightAction G P) (t : T ⟶ S)
    (ht : Chapter13FpqcCover t)
    (h : Chapter13TorsorIdentity (chapter13BaseChangedRightAction A t)) :
    Chapter13TorsorIdentity A := by
  sorry

/- The empty object is the precise boundary example: its comparison map is an isomorphism for
every action datum, but its structural morphism is not a cover over a nonempty base. -/
theorem chapter13_empty_action_satisfies_identity
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (A : Chapter13RightAction G (Over.mk (Scheme.emptyTo S))) :
    Chapter13TorsorIdentity A := by
  change IsIso (chapter13TorsorComparisonMap A)
  let hEmpty : IsEmpty (↑(Limits.pullback (Over.mk (Scheme.emptyTo S)).hom
      (Over.mk (Scheme.emptyTo S)).hom) : Type u) :=
    Scheme.isEmpty_pullback _ _ (by
      let hSource : IsEmpty (Over.mk (Scheme.emptyTo S)).left := by
        change IsEmpty (∅ : Scheme)
        infer_instance
      rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ _
      exact @IsEmpty.false _ hSource x)
  exact @AlgebraicGeometry.isIso_of_isEmpty _ _ (chapter13TorsorComparisonMap A) hEmpty

theorem chapter13_empty_scheme_not_fpqc_cover
    {S : Scheme.{u}} [Nonempty S] :
    ¬ Chapter13FpqcCover (Scheme.emptyTo S) := by
  intro h
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨x, _⟩ := h.2.1.surj s
  exact isEmptyElim x

theorem chapter13_torsor_cover_is_an_independent_clause
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G) :
    Chapter13FpqcCover Q.carrier.hom :=
  Q.cover

noncomputable def chapter13RegularFpqcTorsor
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (hG : Chapter13FpqcCover G.X.hom) : Chapter13FpqcTorsor G := by
  exact
    { carrier := G.X
      action := chapter13RegularRightAction G
      identity := by
        apply (chapter13_torsorIdentity_iff_unique
          (chapter13RegularRightAction G)).2
        intro T p q
        let g : T ⟶ G.X :=
          CartesianMonoidalCategory.lift (p ≫ ι[G.X]) q ≫ μ[G.X]
        refine ⟨g, ?_, ?_⟩
        · change CartesianMonoidalCategory.lift p g ≫ μ[G.X] = q
          dsimp [g]
          exact (GrpObj.eq_lift_inv_left _ p q).mp rfl
        · intro g' hg'
          change CartesianMonoidalCategory.lift p g' ≫ μ[G.X] = q at hg'
          dsimp [g]
          exact (GrpObj.eq_lift_inv_left g' p q).mpr hg'
      cover := hG }

noncomputable def chapter13RegularFppfTorsor
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (hG : Chapter13FppfCover G.X.hom) : Chapter13FppfTorsor G := by
  exact
    { carrier := G.X
      action := chapter13RegularRightAction G
      identity := by
        apply (chapter13_torsorIdentity_iff_unique
          (chapter13RegularRightAction G)).2
        intro T p q
        let g : T ⟶ G.X :=
          CartesianMonoidalCategory.lift (p ≫ ι[G.X]) q ≫ μ[G.X]
        refine ⟨g, ?_, ?_⟩
        · change CartesianMonoidalCategory.lift p g ≫ μ[G.X] = q
          dsimp [g]
          exact (GrpObj.eq_lift_inv_left _ p q).mp rfl
        · intro g' hg'
          change CartesianMonoidalCategory.lift p g' ≫ μ[G.X] = q at hg'
          dsimp [g]
          exact (GrpObj.eq_lift_inv_left g' p q).mpr hg'
      cover := hG }

theorem chapter13_torsor_trivializes_over_its_total_space
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G) :
    Nonempty (Chapter13TorsorLocalTrivialization Q.action Q.carrier.hom) := by
  sorry

/-! ### Finite locally free group schemes -/

theorem chapter13_fpqc_torsor_finite_locally_free
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Chapter13FiniteLocallyFree Q.carrier.hom ∧
      Chapter13SameFiniteLocallyFreeRank Q.carrier.hom G.X.hom := by
  sorry

theorem chapter13_fppf_torsor_finite_locally_free
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FppfTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Chapter13FiniteLocallyFree Q.carrier.hom ∧
      Chapter13SameFiniteLocallyFreeRank Q.carrier.hom G.X.hom := by
  sorry

theorem chapter13_fpqc_iff_fppf_for_finite_locally_free_group
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Nonempty (Chapter13FpqcTorsor G) ↔ Nonempty (Chapter13FppfTorsor G) := by
  sorry

theorem chapter13_fpqc_torsor_is_fppf_for_finite_locally_free_group
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FpqcTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Chapter13FppfCover Q.carrier.hom := by
  sorry

theorem chapter13_fppf_torsor_is_fpqc_for_finite_locally_free_group
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (Q : Chapter13FppfTorsor G)
    (hG : Chapter13FiniteLocallyFreeOfPositiveRank G.X.hom) :
    Chapter13FpqcCover Q.carrier.hom := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
