import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Section02ElementaryPermanenceProperties

/-!
## 3.3 Separatedness, finite type, and properness

The predicates below keep the distinctions between quasi-compactness, locally finite type, and
locally finite presentation explicit.  This matters for quasi-projective morphisms, since an open
immersion need not be quasi-compact.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

variable {X Y S : Scheme.{u}}

/-- The finite-type package for a morphism. -/
def chapter03FiniteType (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- The finite-presentation package for a morphism. -/
def chapter03FinitelyPresented (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFinitePresentation f

/-- Finite type is the conjunction of quasi-compactness and locally finite type. -/
theorem chapter03_finiteType_iff (f : X ⟶ S) :
    chapter03FiniteType f ↔ QuasiCompact f ∧ LocallyOfFiniteType f :=
  Iff.rfl

/-- Finite presentation is the conjunction of quasi-compactness and locally finite presentation. -/
theorem chapter03_finitelyPresented_iff (f : X ⟶ S) :
    chapter03FinitelyPresented f ↔ QuasiCompact f ∧ LocallyOfFinitePresentation f :=
  Iff.rfl

/-- Relative projective bundles are separated. -/
theorem chapter03_relativeProjectiveBundle_isSeparated
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    IsSeparated P.projection := by
  sorry

/-- Relative projective bundles are quasi-compact. -/
theorem chapter03_relativeProjectiveBundle_quasiCompact
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    QuasiCompact P.projection := by
  sorry

/-- Relative projective bundles are locally of finite type. -/
theorem chapter03_relativeProjectiveBundle_locallyOfFiniteType
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    LocallyOfFiniteType P.projection := by
  sorry

/-- Relative projective bundles are proper. -/
theorem chapter03_relativeProjectiveBundle_isProper
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    IsProper P.projection := by
  sorry

/-- Over a locally noetherian base, relative projective bundles are locally of finite
presentation. -/
theorem chapter03_relativeProjectiveBundle_locallyOfFinitePresentation
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation P.projection := by
  sorry

/-- A finite-rank relative projective bundle is finitely presented over its base. -/
theorem chapter03_relativeProjectiveBundle_finitelyPresented
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    chapter03FinitelyPresented P.projection := by
  sorry

/-- Every projective morphism is separated. -/
theorem chapter03_projective_isSeparated (f : X ⟶ S)
    (hf : chapter03Projective f) : IsSeparated f := by
  sorry

/-- Every projective morphism is quasi-compact. -/
theorem chapter03_projective_quasiCompact (f : X ⟶ S)
    (hf : chapter03Projective f) : QuasiCompact f := by
  sorry

/-- Every projective morphism is locally of finite type. -/
theorem chapter03_projective_locallyOfFiniteType (f : X ⟶ S)
    (hf : chapter03Projective f) : LocallyOfFiniteType f := by
  sorry

/-- Every projective morphism is proper. -/
theorem chapter03_projective_isProper (f : X ⟶ S)
    (hf : chapter03Projective f) : IsProper f := by
  sorry

/-- Projective morphisms have finite type. -/
theorem chapter03_projective_finiteType (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03FiniteType f := by
  sorry

/-- A quasi-projective morphism is separated. -/
theorem chapter03_quasiProjective_isSeparated (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) : IsSeparated f := by
  sorry

/-- A quasi-projective morphism is locally of finite type. -/
theorem chapter03_quasiProjective_locallyOfFiniteType (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) : LocallyOfFiniteType f := by
  sorry

/-
SOURCE_ISSUE: The source sentence says that every quasi-projective morphism is “finite type”.
With the definition here, an immersion into a finite-type projective bundle is only guaranteed to
be locally of finite type: an arbitrary open immersion need not be quasi-compact.  The minimal
correction is to add `QuasiCompact f` (or to say “locally of finite type”).
-/

/-- A quasi-compact quasi-projective morphism has finite type. -/
theorem chapter03_quasiProjective_finiteType (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) (hq : QuasiCompact f) :
    chapter03FiniteType f := by
  sorry

/-- A projective presentation with a finitely presented closed immersion is finitely presented. -/
theorem chapter03_finitelyPresented_of_projectivePresentation
    (f : X ⟶ S) (P : Chapter03ProjectivePresentation f)
    [LocallyOfFinitePresentation P.embedding]
    [LocallyOfFinitePresentation P.ambient.projection] :
    chapter03FinitelyPresented f := by
  sorry

/-- A quasi-projective presentation with a finitely presented immersion is finitely presented. -/
theorem chapter03_finitelyPresented_of_quasiProjectivePresentation
    (f : X ⟶ S) (P : Chapter03QuasiProjectivePresentation f)
    [LocallyOfFinitePresentation P.immersion]
    [LocallyOfFinitePresentation P.ambient.projection] (hq : QuasiCompact f) :
    chapter03FinitelyPresented f := by
  sorry

/-- Projective morphisms are finitely presented over a locally noetherian base. -/
theorem chapter03_projective_finitelyPresented_of_locallyNoetherian
    (f : X ⟶ S) (hf : chapter03Projective f) [IsLocallyNoetherian S] :
    chapter03FinitelyPresented f := by
  sorry

/-- Quasi-projective morphisms are finitely presented when the morphism is quasi-compact and the
base is locally noetherian. -/
theorem chapter03_quasiProjective_finitelyPresented_of_locallyNoetherian
    (f : X ⟶ S) (hf : chapter03QuasiProjective f) (hq : QuasiCompact f)
    [IsLocallyNoetherian S] :
    chapter03FinitelyPresented f := by
  sorry

/-- A closed immersion into a proper scheme is proper. -/
theorem chapter03_closedImmersion_comp_proper_isProper
    (i : X ⟶ Y) (g : Y ⟶ S) [IsClosedImmersion i] [IsProper g] :
    IsProper (i ≫ g) := by
  sorry

/-- The existence part of the valuative criterion for a relative projective bundle. -/
theorem chapter03_relativeProjectiveBundle_valuativeCriterion_existence
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ValuativeCriterion.Existence P.projection := by
  sorry

/-- The uniqueness part of the valuative criterion for a relative projective bundle. -/
theorem chapter03_relativeProjectiveBundle_valuativeCriterion_uniqueness
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ValuativeCriterion.Uniqueness P.projection := by
  sorry

/-- The relative projective bundle satisfies the full valuative criterion. -/
theorem chapter03_relativeProjectiveBundle_valuativeCriterion
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ValuativeCriterion P.projection := by
  sorry

/-- A projective-bundle point is represented by a tuple with at least one unit coefficient. -/
def chapter03PrimitiveTuple (V : Type u) [CommRing V] (r : ℕ) : Type u :=
  {a : Fin (r + 1) → V // ∃ i, IsUnit (a i)}

/-- Primitive tuples give normalized representatives of one-dimensional quotients over a
valuation ring. -/
def chapter03ScalarMultiple {K : Type u} (r : ℕ) [Field K]
    (x y : Fin (r + 1) → K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ ∀ i, y i = c * x i

/-- Primitive tuples give normalized representatives of one-dimensional quotients over a
valuation ring, up to the scalar used to normalize the original tuple. -/
theorem chapter03_primitiveTuple_normalization
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (r : ℕ) :
    ∀ x : Fin (r + 1) → K,
      (∃ i, x i ≠ 0) →
        ∃ a : chapter03PrimitiveTuple V r,
          chapter03ScalarMultiple r x (fun i => algebraMap V K (a.1 i)) := by
  sorry

/-- Two primitive representatives of one projective point differ by a unit of the valuation ring. -/
theorem chapter03_primitiveTuple_unique_up_to_unit
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (r : ℕ)
    (a b : chapter03PrimitiveTuple V r)
    (h : chapter03ScalarMultiple r
      (fun i => algebraMap V K (a.1 i))
      (fun i => algebraMap V K (b.1 i))) :
    ∃ u : V, IsUnit u ∧ ∀ i, b.1 i = u * a.1 i := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
