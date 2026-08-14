import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter02
open scoped AlgebraicGeometry BigOperators

/-! ## 3.4. Flat base change and its limits -/

def Chapter03FlatBaseChange {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  Flat f

def chapter03BlowupBaseChange
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (f : Y ⟶ X) : Scheme.{u} :=
  pullback B.projection f

def chapter03BlowupBaseChangeToBlowup
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (f : Y ⟶ X) :
    chapter03BlowupBaseChange B f ⟶ B.carrier :=
  pullback.fst B.projection f

def chapter03BlowupBaseChangeToSource
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (f : Y ⟶ X) :
    chapter03BlowupBaseChange B f ⟶ Y :=
  pullback.snd B.projection f

structure Chapter03BlowupBaseChangeWitness
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (f : Y ⟶ X) where
  pulledBack : Chapter03Blowup (I.comap f)
  iso : pulledBack.carrier ≅ chapter03BlowupBaseChange B f
  over : iso.hom ≫ chapter03BlowupBaseChangeToSource B f = pulledBack.projection
  /-- The comparison is also over the original target, not only over the base-change source. -/
  over_original :
    iso.hom ≫ chapter03BlowupBaseChangeToBlowup B f ≫ B.projection =
      pulledBack.projection ≫ f

/- The ring-level statement is recorded separately because it is the input for the relative-Proj
base-change comparison.  The affine Rees comparison itself remains a local dependency guess in
the pinned relative-section API. -/
structure Chapter03ReesFlatBaseChangeData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) where
  flat : Module.Flat R S
  ideal_power_map : ∀ n : ℕ,
    Ideal.map (algebraMap R S) (I ^ n) =
      chapter02LocalizedIdeal (S := S) I ^ n
  /- The degreewise tensor comparison of Rees algebras is expressed by the canonical comparison
  supplied by Chapter 2, rather than by an unrelated proposition. -/
  rees_tensor_base_change :
    Chapter02AllPowersBaseChangeComparison (S := S) I

theorem chapter03_rees_ideal_power_map
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) :
    Ideal.map (algebraMap R S) (I ^ n) =
      chapter02LocalizedIdeal (S := S) I ^ n := by
  exact Ideal.map_pow (algebraMap R S) I n

/- LOCAL_DEPENDENCY_GUESS (3.4): flatness makes the Rees tensor comparison an isomorphism. -/
theorem chapter03_rees_flat_base_change_data
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S] :
    Nonempty (Chapter03ReesFlatBaseChangeData (S := S) I) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS (3.4): relative `Proj` commutes with the preceding flat Rees
base-change comparison. -/
theorem chapter03_blowup_commutes_with_flat_base_change
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (f : Y ⟶ X) (hf : Flat f) :
    Nonempty (Chapter03BlowupBaseChangeWitness B f) := by
  sorry

theorem chapter03_flat_base_change_over_source
    {X Y : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (f : Y ⟶ X) (_hf : Flat f)
    (W : Chapter03BlowupBaseChangeWitness B f) :
    W.iso.hom ≫ chapter03BlowupBaseChangeToSource B f = W.pulledBack.projection :=
  W.over

/-! ### Why arbitrary base change is not a theorem -/

/- The following predicate names the actual comparison that must be supplied before a non-flat
base change can be identified with the blowup of the extended ideal. -/
abbrev Chapter03PowerBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) : Prop :=
  Chapter02PowerBaseChangeComparison (S := S) I n

abbrev Chapter03AllPowersBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  Chapter02AllPowersBaseChangeComparison (S := S) I

abbrev Chapter03ArbitraryBaseChangeMayHavePowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  Chapter02ArbitraryBaseChangeMayHavePowerTorsion (S := S) I

theorem chapter03_flat_base_change_has_power_comparisons
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S] :
    Chapter03AllPowersBaseChangeComparison (S := S) I := by
  sorry

def chapter03FiberAssociatedGradedRing
    {R : Type u} [CommRing R] (I : Ideal R) :=
  chapter02AssociatedGraded I

theorem chapter03_fiber_associated_graded_ring_def
    {R : Type u} [CommRing R] (I : Ideal R) :
    chapter03FiberAssociatedGradedRing I = chapter02AssociatedGraded I :=
  rfl

/-! ### Regular centers and exceptional projective bundles -/

structure Chapter03RegularClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) : Prop where
  closed : IsClosedImmersion i
  regularSequence :
    ∀ z : Z, ∃ rs : List (X.presheaf.stalk (i z)),
      RingTheory.Sequence.IsRegular (X.presheaf.stalk (i z)) rs ∧
        RingHom.ker (i.stalkMap z).hom = Ideal.ofList rs

def Chapter03RegularClosedCenter
    {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  Chapter03RegularClosedImmersion I.subschemeι

def Chapter03IntegralRegularClosedCenter
    {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  IsIntegral I.subscheme ∧ Chapter03RegularClosedCenter I

abbrev chapter03AffineConormalModule
    {R : Type u} [CommRing R] (J : Ideal R) :=
  J.Cotangent

def chapter03AffineNormalModule
    {R : Type u} [CommRing R] (J : Ideal R) :=
  Module.Dual (R ⧸ J) (chapter03AffineConormalModule J)

theorem chapter03_affine_normal_is_dual_conormal
    {R : Type u} [CommRing R] (J : Ideal R) :
    chapter03AffineNormalModule J =
      Module.Dual (R ⧸ J) (chapter03AffineConormalModule J) :=
  rfl

/- A local conormal comparison must retain its scalar action.  The source section module is
supplied explicitly because the pinned sheaf API exposes sections as additive groups, while the
cotangent target already carries its canonical quotient-module structure. -/
structure Chapter03AffineModuleEquivalence
    (R M N : Type u) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R N] where
  [sourceModule : Module R M]
  equivalence : M ≃ₗ[R] N

structure Chapter03RegularCenterExceptionalData
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) where
  regularCenter : Chapter03RegularClosedCenter I.ideal
  conormal : I.ideal.subscheme.Modules
  normal : I.ideal.subscheme.Modules
  conormal_is_I_mod_I_squared :
    ∀ U : X.affineOpens,
      Chapter03AffineModuleEquivalence
        (Γ(X, U.1) ⧸ (I.ideal.ideal U))
        (Γ(conormal, I.ideal.subschemeι ⁻¹ᵁ U.1))
        (I.ideal.ideal U).Cotangent
  conormal_target_restriction :
    ∀ {U V : X.affineOpens} (_h : V.1 ≤ U.1),
      (I.ideal.ideal U).Cotangent →+
        (I.ideal.ideal V).Cotangent
  conormal_restriction_natural :
    ∀ {U V : X.affineOpens} (h : V.1 ≤ U.1)
      (hpre : I.ideal.subschemeι ⁻¹ᵁ V.1 ≤ I.ideal.subschemeι ⁻¹ᵁ U.1)
      (x : Γ(conormal, I.ideal.subschemeι ⁻¹ᵁ U.1)),
      (conormal_is_I_mod_I_squared V).equivalence
          ((Scheme.Modules.presheaf conormal).map (homOfLE hpre).op x) =
        (conormal_target_restriction h)
          ((conormal_is_I_mod_I_squared U).equivalence x)
  normal_is_dual_conormal :
    ∀ U : X.affineOpens,
      Chapter03AffineModuleEquivalence
        (Γ(X, U.1) ⧸ (I.ideal.ideal U))
        (Γ(normal, I.ideal.subschemeι ⁻¹ᵁ U.1))
        (Module.Dual (Γ(X, U.1) ⧸ (I.ideal.ideal U))
          (I.ideal.ideal U).Cotangent)
  normal_target_restriction :
    ∀ {U V : X.affineOpens} (_h : V.1 ≤ U.1),
      Module.Dual (Γ(X, U.1) ⧸ (I.ideal.ideal U))
          (I.ideal.ideal U).Cotangent →+
        Module.Dual (Γ(X, V.1) ⧸ (I.ideal.ideal V))
          (I.ideal.ideal V).Cotangent
  normal_restriction_natural :
    ∀ {U V : X.affineOpens} (h : V.1 ≤ U.1)
      (hpre : I.ideal.subschemeι ⁻¹ᵁ V.1 ≤ I.ideal.subschemeι ⁻¹ᵁ U.1)
      (x : Γ(normal, I.ideal.subschemeι ⁻¹ᵁ U.1)),
      (normal_is_dual_conormal V).equivalence
          ((Scheme.Modules.presheaf normal).map (homOfLE hpre).op x) =
        (normal_target_restriction h)
          ((normal_is_dual_conormal U).equivalence x)
  projectivized_conormal : Chapter04ProjectiveBundle I.ideal.subscheme
  projectivized_conormal_module : projectivized_conormal.E ≅ conormal
  exceptional_iso :
    chapter03BlowupExceptionalSubscheme B ≅ projectivized_conormal.space
  exceptional_iso_over_center :
    exceptional_iso.hom ≫ projectivized_conormal.projection =
      chapter03BlowupExceptionalToCenter B

/- LOCAL_DEPENDENCY_GUESS (3.4): the exceptional divisor of a blowup along a regular closed
center is the projective bundle of the conormal module, equivalently of the dual normal module
under the quotient convention. -/
theorem chapter03_regular_center_exceptional_is_projective_bundle
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I)
    (hreg : Chapter03RegularClosedCenter I.ideal) :
    Nonempty (Chapter03RegularCenterExceptionalData B) := by
  sorry

/-! ### Singular centers and the normal cone -/

abbrev Chapter03AffineAssociatedGradedRing
    {R : Type u} [CommRing R] (J : Ideal R) :=
  chapter02AssociatedGraded J

structure Chapter03AssociatedGradedAlgebraData
    {R : Type u} [CommRing R] (J : Ideal R) where
  graded : Chapter02GradedAlgebra ℤ (Chapter03AffineAssociatedGradedRing J)
  component_is_canonical :
    ∀ n (x : Chapter03AffineAssociatedGradedRing J),
      x ∈ graded.component n ↔
        ∃ y : chapter02AssociatedGradedPiece J n,
          DirectSum.of (fun n : ℕ => chapter02AssociatedGradedPiece J n) n y = x

noncomputable def chapter03ProjectivizedNormalCone
    {R : Type u} [CommRing R] {J : Ideal R}
    (D : Chapter03AssociatedGradedAlgebraData J) : Scheme.{u} :=
  letI : GradedAlgebra D.graded.component := D.graded.graded
  AlgebraicGeometry.«Proj» D.graded.component

structure Chapter03AffineNormalConeDescription
    {R : Type u} [CommRing R] (J : Ideal R) where
  associatedGraded : Chapter03AssociatedGradedAlgebraData J
  projectivizedNormalCone : Scheme.{u}
  projectivizedNormalCone_is_Proj_associatedGraded :
    projectivizedNormalCone = chapter03ProjectivizedNormalCone associatedGraded

def chapter03BlowupExceptionalRestriction
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (U : X.affineOpens) : Scheme.{u} :=
  pullback (chapter03BlowupExceptionalInclusion B)
    ((B.projection ⁻¹ᵁ U.1).ι)

def chapter03BlowupExceptionalRestrictionToCenter
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) (U : X.affineOpens) :
    chapter03BlowupExceptionalRestriction B U ⟶ I.ideal.subscheme :=
  pullback.fst (chapter03BlowupExceptionalInclusion B)
      ((B.projection ⁻¹ᵁ U.1).ι) ≫ chapter03BlowupExceptionalToCenter B

structure Chapter03SingularCenterNormalConeData
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) where
  local_description :
    ∀ U : X.affineOpens,
      Chapter03AffineNormalConeDescription (I.ideal.ideal U)
  local_to_center :
    ∀ U : X.affineOpens,
      (local_description U).projectivizedNormalCone ⟶ I.ideal.subscheme
  exceptional_is_projectivized_normal_cone :
    ∀ U : X.affineOpens,
      ∃ e : chapter03BlowupExceptionalRestriction B U ≅
          (local_description U).projectivizedNormalCone,
        e.hom ≫ local_to_center U =
          chapter03BlowupExceptionalRestrictionToCenter B U

/- LOCAL_DEPENDENCY_GUESS (3.4): for a singular center the exceptional locus is locally
`Proj gr_I(O_X)` and no reducedness or irreducibility is implied. -/
theorem chapter03_singular_center_exceptional_is_projectivized_normal_cone
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I)
    (hsingular : ¬ Chapter03RegularClosedCenter I.ideal) :
    Nonempty (Chapter03SingularCenterNormalConeData B) := by
  sorry

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03
