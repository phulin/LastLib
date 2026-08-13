import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Dependencies

/-!
## 3.1 Definitions that survive change of base

The shared relative projective-bundle and projective/quasi-projective interfaces are supplied by
`Dependencies.lean`; this section records the source-order definitions and elementary bridges.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

noncomputable section

universe u

variable {X Y S T : Scheme.{u}}

/-- The presentation form of projectivity. -/
theorem chapter03_projective_iff_exists_presentation (f : X ⟶ S) :
    chapter03Projective f ↔ Nonempty (Chapter03ProjectivePresentation f) :=
  Iff.rfl

/-- The presentation form of quasi-projectivity. -/
theorem chapter03_quasiProjective_iff_exists_presentation (f : X ⟶ S) :
    chapter03QuasiProjective f ↔ Nonempty (Chapter03QuasiProjectivePresentation f) :=
  Iff.rfl

/-- Constructor for the projective predicate from its presentation data. -/
theorem chapter03_projective_of_presentation (f : X ⟶ S)
    (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) (i : X ⟶ P.carrier)
    (hi : IsClosedImmersion i) (overBase : i ≫ P.projection = f) :
    chapter03Projective f := by
  sorry

/-- Constructor for the quasi-projective predicate from its presentation data. -/
theorem chapter03_quasiProjective_of_presentation (f : X ⟶ S)
    (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) (i : X ⟶ P.carrier)
    (hi : IsImmersion i) (overBase : i ≫ P.projection = f) :
    chapter03QuasiProjective f := by
  sorry

/-- Eliminator for a projective presentation. -/
theorem chapter03_projective_elim (f : X ⟶ S) {Q : Prop}
    (hf : chapter03Projective f)
    (hQ : ∀ _P : Chapter03ProjectivePresentation f, Q) : Q :=
  Nonempty.elim hf hQ

/-- Eliminator for a quasi-projective presentation. -/
theorem chapter03_quasiProjective_elim (f : X ⟶ S) {Q : Prop}
    (hf : chapter03QuasiProjective f)
    (hQ : ∀ _P : Chapter03QuasiProjectivePresentation f, Q) : Q :=
  Nonempty.elim hf hQ

/-- Local projectivity on an open cover of the target. -/
def chapter03LocallyProjective (f : X ⟶ S) : Prop :=
  ∃ (𝒰 : S.OpenCover.{u}), ∀ i : 𝒰.I₀,
    chapter03Projective (f ∣_ (𝒰.f i).opensRange)

/-- Local quasi-projectivity on an open cover of the target. -/
def chapter03LocallyQuasiProjective (f : X ⟶ S) : Prop :=
  ∃ (𝒰 : S.OpenCover.{u}), ∀ i : 𝒰.I₀,
    chapter03QuasiProjective (f ∣_ (𝒰.f i).opensRange)

/-- The free module used for the standard relative projective space. -/
noncomputable def chapter03TrivialModule (S : Scheme.{u}) (r : ℕ) : S.Modules :=
  SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin (r + 1)))

/-- The standard free module is finite locally free. -/
theorem chapter03_trivialModule_finiteLocallyFree (S : Scheme.{u}) (r : ℕ) :
    chapter03FiniteLocallyFree (chapter03TrivialModule S r) := by
  sorry

/-- The chosen relative projective space of rank `r`. -/
noncomputable def chapter03ProjectiveSpaceBundle (S : Scheme.{u}) (r : ℕ) :
    Chapter03RelativeProjectiveBundle S (chapter03TrivialModule S r) :=
  { module :=
    chapter02FreeQuasiCoherentModule S (Chapter02ProjectiveSpaceIndex r)
    module_carrier := rfl
    finiteLocallyFree := chapter03_trivialModule_finiteLocallyFree S r
    canonical :=
      { finiteLocallyFree := chapter03_trivialModule_finiteLocallyFree S r
        data :=
          (chapter02ProjectiveSpaceData S (Chapter02ProjectiveSpaceIndex r)).bundle
        proper := by sorry
        finite_presentation := by sorry } }

/-- The relative projective space `ℙ^r_S`, as supplied by the preceding projective-bundle API. -/
noncomputable def chapter03ProjectiveSpace (S : Scheme.{u}) (r : ℕ) : Scheme.{u} :=
  (chapter03ProjectiveSpaceBundle S r).carrier

/-- The structure morphism `ℙ^r_S ⟶ S`. -/
noncomputable def chapter03ProjectiveSpaceProjection (S : Scheme.{u}) (r : ℕ) :
    chapter03ProjectiveSpace S r ⟶ S :=
  (chapter03ProjectiveSpaceBundle S r).projection

/-- The affine `r`-space over `S`. -/
def chapter03AffineSpace (S : Scheme.{u}) (r : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) S

/-- The canonical projection `𝔸^r_S ⟶ S`. -/
def chapter03AffineSpaceProjection (S : Scheme.{u}) (r : ℕ) :
    chapter03AffineSpace S r ⟶ S :=
  CategoryTheory.CanonicallyOverClass.Simps.over
    (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin r)) S) S

/-- The standard open immersion `𝔸^r_S = D_+(x₀) ↪ ℙ^r_S`. -/
theorem chapter03_affineSpace_is_standard_open (S : Scheme.{u}) (r : ℕ) :
    ∃ i : chapter03AffineSpace S r ⟶ chapter03ProjectiveSpace S r,
      IsOpenImmersion i ∧
        i ≫ chapter03ProjectiveSpaceProjection S r = chapter03AffineSpaceProjection S r := by
  sorry

/-- Affine space is quasi-projective over its base. -/
theorem chapter03_affineSpace_quasiProjective (S : Scheme.{u}) (r : ℕ) :
    chapter03QuasiProjective (chapter03AffineSpaceProjection S r) := by
  sorry

/-- Every closed immersion is projective. -/
theorem chapter03_closedImmersion_projective (i : X ⟶ S) [IsClosedImmersion i] :
    chapter03Projective i := by
  sorry

/-- An open subscheme of a projective `S`-scheme is quasi-projective over `S`. -/
theorem chapter03_openImmersion_quasiProjective (j : X ⟶ Y) (f : Y ⟶ S)
    [IsOpenImmersion j] (hf : chapter03Projective f) :
    chapter03QuasiProjective (j ≫ f) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
