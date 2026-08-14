import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter03.Section03TheUniversalProperty

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
  /- LOCAL_DEPENDENCY_GUESS (3.4): the degreewise tensor comparison of Rees algebras is an
  isomorphism under the flatness hypothesis. -/
  rees_tensor_base_change : Prop

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
    Nonempty (Chapter03ReesFlatBaseChangeData I) := by
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
    (B : Chapter03Blowup I) (f : Y ⟶ X) (hf : Flat f)
    (W : Chapter03BlowupBaseChangeWitness B f) :
    W.iso.hom ≫ chapter03BlowupBaseChangeToSource B f = W.pulledBack.projection :=
  W.over

/-! ### Why arbitrary base change is not a theorem -/

/- The following predicate names the actual comparison that must be supplied before a non-flat
base change can be identified with the blowup of the extended ideal. -/
def Chapter03PowerBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ) : Prop :=
  Nonempty
    (S ⊗[R] (I ^ n : Submodule R R) ≃ₗ[S]
      (chapter02LocalizedIdeal (S := S) I ^ n : Submodule S S))

def Chapter03AllPowersBaseChangeComparison
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  ∀ n : ℕ, Chapter03PowerBaseChangeComparison I n

def Chapter03ArbitraryBaseChangeMayHavePowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) : Prop :=
  ¬ Chapter03AllPowersBaseChangeComparison I

theorem chapter03_flat_base_change_has_power_comparisons
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S] :
    Chapter03AllPowersBaseChangeComparison I := by
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
    {Z X : Scheme.{u}} (i : Z ⟶ X) (r : ℕ) : Prop where
  closed : IsClosedImmersion i
  regularSequence :
    ∀ z : Z, ∃ rs : List (X.presheaf.stalk (i z)),
      rs.length = r ∧
        RingTheory.Sequence.IsRegular (X.presheaf.stalk (i z)) rs ∧
          RingHom.ker (i.stalkMap z).hom = Ideal.ofList rs

def Chapter03RegularClosedCenter
    {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∃ r : ℕ, Chapter03RegularClosedImmersion I.subschemeι r

def Chapter03IntegralRegularClosedCenter
    {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  IsIntegral I.subscheme ∧ Chapter03RegularClosedCenter I

def chapter03AffineConormalModule
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

structure Chapter03RegularCenterExceptionalData
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) where
  regularCenter : Chapter03RegularClosedCenter I.ideal
  conormal : I.ideal.subscheme.Modules
  normal : I.ideal.subscheme.Modules
  conormal_is_I_mod_I_squared : Prop
  normal_is_dual_conormal : Prop
  projectivized_conormal : Chapter04ProjectiveBundle I.ideal.subscheme
  projectivized_conormal_module : projectivized_conormal.E = conormal
  exceptional_iso :
    chapter03BlowupExceptionalSubscheme B ≅ projectivized_conormal.space
  exceptional_iso_over_center :
    exceptional_iso.hom ≫ projectivized_conormal.projection =
      chapter03BlowupExceptionalToCenter B
  projectivization_uses_quotient_convention : Prop
  projectivized_dual_normal_identification : Prop

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
  components : ℕ → Submodule ℤ (Chapter03AffineAssociatedGradedRing J)
  graded : GradedAlgebra components

noncomputable def chapter03ProjectivizedNormalCone
    {R : Type u} [CommRing R] {J : Ideal R}
    (D : Chapter03AssociatedGradedAlgebraData J) : Scheme.{u} :=
  letI : GradedAlgebra D.components := D.graded
  AlgebraicGeometry.«Proj» D.components

structure Chapter03AffineNormalConeDescription
    {R : Type u} [CommRing R] (J : Ideal R) where
  associatedGraded : Chapter03AssociatedGradedAlgebraData J
  projectivizedNormalCone : Scheme.{u}
  projectivizedNormalCone_is_Proj_associatedGraded :
    projectivizedNormalCone = chapter03ProjectivizedNormalCone associatedGraded

structure Chapter03SingularCenterNormalConeData
    {X : Scheme.{u}} {I : Chapter03CoherentIdeal X}
    (B : Chapter03Blowup I) where
  local_description :
    ∀ U : X.affineOpens,
      Chapter03AffineNormalConeDescription (I.ideal.ideal U)
  exceptional_is_projectivized_normal_cone : Prop
  exceptional_may_be_nonreduced : Prop
  exceptional_may_be_reducible : Prop

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
