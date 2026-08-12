import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Dependencies

/-!
## 3.1 Definitions that survive change of base

The first structure below is the one deliberately provisional interface in this draft.  The
preceding projective-bundle chapter should replace it by the canonical relative `Proj` together
with its universal quotient and base-change comparison.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

variable {X Y S T : Scheme.{u}}

/-- A finite locally free sheaf of modules on a scheme.

This is the sheaf-theoretic form of a finite-rank projective bundle. -/
def chapter03FiniteLocallyFree (E : S.Modules) : Prop :=
  SheafOfModules.IsLocallyFree E ∧ SheafOfModules.IsFiniteType E

/--
`LOCAL_DEPENDENCY_GUESS`: the preceding chapter is expected to provide the relative projective
bundle attached to a finite locally free module.  Only its scheme and structure morphism are
needed for the definitions in this chapter; the universal quotient is intentionally not asserted
here until that earlier API is available.
-/
structure Chapter03RelativeProjectiveBundle (S : Scheme.{u}) (E : S.Modules) where
  carrier : Scheme.{u}
  projection : carrier ⟶ S

/--
`LOCAL_DEPENDENCY_GUESS`: existence of the relative projective bundle of a finite locally free
module.  This declaration is a placeholder for the canonical construction from the preceding
chapter, not an additional primitive assumption in the intended final API.
-/
theorem chapter03_relativeProjectiveBundle_exists
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E) :
    Nonempty (Chapter03RelativeProjectiveBundle S E) := by
  sorry

/-- A chosen relative projective bundle, pending replacement by the canonical preceding-chapter
construction. -/
noncomputable def chapter03RelativeProjectiveBundle
    (S : Scheme.{u}) (E : S.Modules) (hE : chapter03FiniteLocallyFree E) :
    Chapter03RelativeProjectiveBundle S E :=
  Classical.choice (chapter03_relativeProjectiveBundle_exists S E hE)

/-- A global projective presentation of a morphism. -/
structure Chapter03ProjectivePresentation (f : X ⟶ S) where
  module : S.Modules
  finiteLocallyFree : chapter03FiniteLocallyFree module
  ambient : Chapter03RelativeProjectiveBundle S module
  embedding : X ⟶ ambient.carrier
  isClosedImmersion : IsClosedImmersion embedding
  overBase : embedding ≫ ambient.projection = f

/-- A global quasi-projective presentation of a morphism. -/
structure Chapter03QuasiProjectivePresentation (f : X ⟶ S) where
  module : S.Modules
  finiteLocallyFree : chapter03FiniteLocallyFree module
  ambient : Chapter03RelativeProjectiveBundle S module
  immersion : X ⟶ ambient.carrier
  isImmersion : IsImmersion immersion
  overBase : immersion ≫ ambient.projection = f

/-- A morphism is projective when it admits a closed immersion into a relative projective bundle. -/
def chapter03Projective (f : X ⟶ S) : Prop :=
  Nonempty (Chapter03ProjectivePresentation f)

/-- A morphism is quasi-projective when it admits a locally closed immersion into a relative
projective bundle. -/
def chapter03QuasiProjective (f : X ⟶ S) : Prop :=
  Nonempty (Chapter03QuasiProjectivePresentation f)

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
    chapter03Projective f :=
  ⟨⟨E, hE, P, i, hi, overBase⟩⟩

/-- Constructor for the quasi-projective predicate from its presentation data. -/
theorem chapter03_quasiProjective_of_presentation (f : X ⟶ S)
    (E : S.Modules) (hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) (i : X ⟶ P.carrier)
    (hi : IsImmersion i) (overBase : i ≫ P.projection = f) :
    chapter03QuasiProjective f :=
  ⟨⟨E, hE, P, i, hi, overBase⟩⟩

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
  chapter03RelativeProjectiveBundle S (chapter03TrivialModule S r)
    (chapter03_trivialModule_finiteLocallyFree S r)

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
