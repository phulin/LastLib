import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Section03RepresentabilityWithFixedPolynomial

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

/-! ## 12.4. The finite-length Hilbert scheme -/

/-- The notation `Hilb^d(X/S)` specialized to the constant polynomial. -/
abbrev chapter12FiniteLengthHilbertScheme
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D) (d : ℕ) : Scheme :=
  chapter12HilbertScheme D H (chapter12ConstantPolynomial d)

abbrev chapter12FiniteLengthHilbertSchemeMap
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D) (d : ℕ) :
    chapter12FiniteLengthHilbertScheme D H d ⟶ D.base :=
  chapter12HilbertSchemeMap D H (chapter12ConstantPolynomial d)

theorem chapter12FiniteLengthHilbertScheme_is_projective
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D) (d : ℕ) :
    chapter12IsProjectiveMorphism (chapter12FiniteLengthHilbertSchemeMap D H d) := by
  exact chapter12HilbertScheme_is_projective D H (chapter12ConstantPolynomial d)

theorem chapter12FiniteLengthUniversalFamily_is_finite_locally_free
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (L : Chapter12FiberLengthTheory)
    (K : Chapter12HilbertLengthCompatibility D H L) (d : ℕ) :
    Chapter12FiniteLocallyFreeRank L
      (chapter12FamilyProjection D
        (Over.mk (chapter12FiniteLengthHilbertSchemeMap D H d))
        (chapter12UniversalFamily D H (chapter12ConstantPolynomial d)).closed.ideal) d := by
  sorry

/- The following interface packages the uniqueness-of-representers argument
  used to remove dependence on a chosen projective embedding. -/
structure Chapter12RepresentingOverIso
    {S : Scheme}
    {R R' : Scheme} (f : R ⟶ S) (f' : R' ⟶ S) where
  iso : R ≅ R'
  over : iso.hom ≫ f' = f

@[ext]
theorem chapter12RepresentingOverIso_ext
    {S R R' : Scheme} {f : R ⟶ S} {f' : R' ⟶ S}
    (e e' : Chapter12RepresentingOverIso f f')
    (h : e.iso = e'.iso) : e = e' := by
  cases e
  cases e'
  simp_all

def chapter12RepresentingOverIsoHom
    {S : Scheme} {R R' : Scheme} {f : R ⟶ S} {f' : R' ⟶ S}
    (e : Chapter12RepresentingOverIso f f') :
    Over.mk f ⟶ Over.mk f' :=
  Over.homMk e.iso.hom e.over

/-- Representing objects for the same Hilbert functor are uniquely isomorphic over `S`. -/
theorem chapter12_finite_hilbert_embedding_independent
    (D : Chapter12ProjectiveFamilySetup)
    (H H' : Chapter12HilbertPolynomialTheory D)
    (d : ℕ)
    (same_functor : Nonempty
      ((chapter12HilbertFunctor D H (chapter12ConstantPolynomial d)) ≅
        (chapter12HilbertFunctor D H' (chapter12ConstantPolynomial d)))) :
    Nonempty (Chapter12RepresentingOverIso
      (chapter12FiniteLengthHilbertSchemeMap D H d)
      (chapter12HilbertSchemeMap D H' (chapter12ConstantPolynomial d))) := by
  sorry

def chapter12RepresentingCompatibility
    {D : Chapter12ProjectiveFamilySetup}
    {H : Chapter12HilbertPolynomialTheory D}
    {P : Chapter12NumericalPolynomial}
    (R R' : Chapter12HilbertRepresentingScheme D H P)
    (e : Chapter12RepresentingOverIso R.structureMap R'.structureMap) : Prop :=
  ∀ T : Chapter12SchemeOver D.base,
    ∀ f : T ⟶ Over.mk R.structureMap,
      R.representingEquivalence T f =
        R'.representingEquivalence T
          (f ≫ chapter12RepresentingOverIsoHom e)

theorem chapter12_representing_over_iso_unique
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial)
    (R R' : Chapter12HilbertRepresentingScheme D H P)
    (e e' : Chapter12RepresentingOverIso R.structureMap R'.structureMap)
    (he : chapter12RepresentingCompatibility R R' e)
    (he' : chapter12RepresentingCompatibility R R' e') :
    e.iso = e'.iso := by
  sorry

/-- A projective completion of a quasi-projective morphism. -/
structure Chapter12QuasiProjectiveCompletion {X S : Scheme} (f : X ⟶ S) where
  completion : Scheme
  completionMap : completion ⟶ S
  openImmersion : X ⟶ completion
  open_is_open : IsOpenImmersion openImmersion
  over : openImmersion ≫ completionMap = f
  completion_projective : chapter12IsProjectiveMorphism completionMap

attribute [instance] Chapter12QuasiProjectiveCompletion.open_is_open

/-- The open locus in the finite-length Hilbert scheme of a projective completion. -/
structure Chapter12FiniteLengthOpenLocus
    {X S : Scheme} (f : X ⟶ S)
    (C : Chapter12QuasiProjectiveCompletion f)
    (d : ℕ) where
  ambientHilbertScheme : Scheme
  ambientMap : ambientHilbertScheme ⟶ S
  openLocus : Scheme
  inclusion : openLocus ⟶ ambientHilbertScheme
  openLocusMap : openLocus ⟶ S
  openLocus_over : inclusion ≫ ambientMap = openLocusMap
  inclusion_is_open : IsOpenImmersion inclusion
  universal_family_finite : Prop
  boundary_intersection_image_closed : Prop
  universal_family_lies_in_X : Prop
  represents_finite_length_families_in_X : Prop
  quasi_projective_over_base : chapter12IsQuasiProjectiveMorphism openLocusMap
  arbitrary_base_change : Prop

attribute [instance] Chapter12FiniteLengthOpenLocus.inclusion_is_open

theorem chapter12_quasi_projective_finite_length_open_locus_exists
    {X S : Scheme} (f : X ⟶ S)
    (C : Chapter12QuasiProjectiveCompletion f) (d : ℕ) :
    Nonempty (Chapter12FiniteLengthOpenLocus f C d) := by
  sorry

noncomputable def chapter12QuasiProjectiveFiniteLengthOpenLocus
    {X S : Scheme} (f : X ⟶ S)
    (C : Chapter12QuasiProjectiveCompletion f) (d : ℕ) :
    Chapter12FiniteLengthOpenLocus f C d :=
  Classical.choice (chapter12_quasi_projective_finite_length_open_locus_exists f C d)

theorem chapter12_quasi_projective_finite_length_locus_is_open
    {X S : Scheme} (f : X ⟶ S)
    (C : Chapter12QuasiProjectiveCompletion f) (d : ℕ) :
    IsOpenImmersion
      (chapter12QuasiProjectiveFiniteLengthOpenLocus f C d).inclusion := by
  exact (chapter12QuasiProjectiveFiniteLengthOpenLocus f C d).inclusion_is_open

theorem chapter12_quasi_projective_finite_length_locus_base_change
    {X S : Scheme} (f : X ⟶ S)
    (C : Chapter12QuasiProjectiveCompletion f) (d : ℕ) :
    (chapter12QuasiProjectiveFiniteLengthOpenLocus f C d).arbitrary_base_change := by
  sorry

/-- The reduced-geometric-fiber locus inside a finite-length Hilbert scheme. -/
def chapter12GeometricFiber (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
    (t : Chapter12GeometricPoint T.left) : Scheme :=
  pullback (chapter12FamilyProjection D T Z.ideal) t.point

def chapter12GeometricFiberIsReduced
    (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
    (t : Chapter12GeometricPoint T.left) : Prop :=
  IsReduced (chapter12GeometricFiber D Z t)

def chapter12HasReducedGeometricFibers
    (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T) : Prop :=
  ∀ t : Chapter12GeometricPoint T.left, chapter12GeometricFiberIsReduced D Z t

/-- A configuration-space quotient for a smooth family. -/
structure Chapter12UnorderedConfigurationSpace
    (D : Chapter12ProjectiveFamilySetup) (d r : ℕ) where
  ordered : Scheme
  unordered : Scheme
  orderedMap : ordered ⟶ D.base
  unorderedMap : unordered ⟶ D.base
  quotient : ordered ⟶ unordered
  quotient_over_base : quotient ≫ unorderedMap = orderedMap
  free_locus : Prop
  finite_etale_quotient : Prop
  classifies_unordered_reduced_families : Prop
  relative_dimension : chapter12HasRelativeDimension unorderedMap r

/-- The open reduced locus and its identification with unordered configurations. -/
structure Chapter12ReducedHilbertLocus
    (D : Chapter12ProjectiveFamilySetup) (H : Chapter12HilbertPolynomialTheory D)
    (d r : ℕ) where
  carrier : Scheme
  inclusion : carrier ⟶ chapter12FiniteLengthHilbertScheme D H d
  inclusion_is_open : IsOpenImmersion inclusion
  reduced_fiber_condition : Prop
  configuration : Chapter12UnorderedConfigurationSpace D d r
  configuration_iso : carrier ≅ configuration.unordered
  iso_over_base : configuration_iso.hom ≫ configuration.unorderedMap =
    inclusion ≫ chapter12FiniteLengthHilbertSchemeMap D H d

attribute [instance] Chapter12ReducedHilbertLocus.inclusion_is_open

theorem chapter12_reduced_locus_is_unordered_configuration
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (d r : ℕ) (smooth : Smooth D.structureMap)
    (relative_dimension : chapter12HasRelativeDimension D.structureMap r) :
    Nonempty (Chapter12ReducedHilbertLocus D H d r) := by
  sorry

/-- The collision/tangent-direction comparison for two points on the affine plane. -/
structure Chapter12AffinePlaneHilbertCollision (k : Type*) [Field k] where
  affinePlane : Scheme
  affinePlane_is_A2 : Prop
  hilbertTwo : Scheme
  cycleTwo : Scheme
  hilbertToCycle : hilbertTwo ⟶ cycleTwo
  collisionLocus : Scheme
  tangentDirection : Prop
  cycle_forgets_tangent_direction : Prop
  hilbertToCycle_not_isomorphism : ¬ IsIso hilbertToCycle

theorem chapter12_affine_plane_hilbert_two_collision
    (k : Type*) [Field k] :
    Nonempty (Chapter12AffinePlaneHilbertCollision k) := by
  sorry

noncomputable def chapter12AffinePlaneHilbertTwoCollision
    (k : Type*) [Field k] : Chapter12AffinePlaneHilbertCollision k :=
  Classical.choice (chapter12_affine_plane_hilbert_two_collision k)

theorem chapter12_affine_plane_hilbert_two_not_cycle_space
    (k : Type*) [Field k] :
    ¬ IsIso (chapter12AffinePlaneHilbertTwoCollision k).hilbertToCycle := by
  exact (chapter12AffinePlaneHilbertTwoCollision k).hilbertToCycle_not_isomorphism

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
