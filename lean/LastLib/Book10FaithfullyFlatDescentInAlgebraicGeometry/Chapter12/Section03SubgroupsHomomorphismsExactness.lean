import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Section01GroupLawsDescend

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-!
### 12.3 Subgroups, homomorphisms, and exactness
-/

/-- A closed subgroup object in the slice. -/
structure Chapter12ClosedSubgroup {S : Scheme.{u}}
    (G : Chapter12CommutativeGroupScheme S) where
  subgroup : Chapter12CommutativeGroupScheme S
  inclusion : subgroup ⟶ G
  closed : IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme inclusion)

/-- The closed-subgroup package with its finite-locally-free property recorded. -/
structure Chapter12FiniteLocallyFreeClosedSubgroup {S : Scheme.{u}}
    (G : Chapter12CommutativeGroupScheme S) where
  subgroup : Chapter12CommutativeGroupScheme S
  inclusion : subgroup ⟶ G
  closed : IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme inclusion)
  finiteLocallyFree : Chapter12FiniteLocallyFree subgroup.X.hom

@[ext]
theorem chapter12ClosedSubgroup.ext {S : Scheme.{u}}
    {G : Chapter12CommutativeGroupScheme S}
    {K L : Chapter12ClosedSubgroup G}
    (h : K.subgroup = L.subgroup) : K = L := by
  cases K
  cases L
  cases h
  rfl

/-! Homomorphisms descend uniquely once their underlying morphism has descended. -/

theorem chapter12_homomorphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D₁ D₂ : Chapter12GroupSchemeDescentDatum p)
    {G H : Chapter12GroupScheme S}
    (eG : Chapter12GroupScheme.baseChange p G ≅ D₁.upstairs)
    (eH : Chapter12GroupScheme.baseChange p H ≅ D₂.upstairs)
    (fT : D₁.upstairs ⟶ D₂.upstairs)
    (hfT : chapter12DescentHomCompatible D₁ D₂ fT) :
    ∃ f : G ⟶ H,
      Chapter12GroupScheme.baseChangeHom p f = eG.hom ≫ fT ≫ eH.inv := by
  sorry

theorem chapter12_faithfullyFlatLocallyOfFinitePresentation_homomorphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D₁ D₂ : Chapter12GroupSchemeDescentDatum p)
    {G H : Chapter12GroupScheme S}
    (eG : Chapter12GroupScheme.baseChange p G ≅ D₁.upstairs)
    (eH : Chapter12GroupScheme.baseChange p H ≅ D₂.upstairs)
    (fT : D₁.upstairs ⟶ D₂.upstairs)
    (hfT : chapter12DescentHomCompatible D₁ D₂ fT)
    (hfflfp : Chapter12FaithfullyFlatLocallyOfFinitePresentation
      (Chapter12GroupScheme.homScheme fT)) :
    ∃ f : G ⟶ H,
      Chapter12FaithfullyFlatLocallyOfFinitePresentation
        (Chapter12GroupScheme.homScheme f) ∧
      Chapter12GroupScheme.baseChangeHom p f = eG.hom ≫ fT ≫ eH.inv := by
  sorry

theorem chapter12_homomorphism_descends_unique
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    {G H : Chapter12GroupScheme S} (f g : G ⟶ H)
    (h : Chapter12GroupScheme.baseChangeHom p f =
      Chapter12GroupScheme.baseChangeHom p g) :
    f = g := by
  exact chapter12_group_hom_ext_of_faithfullyFlat p ⟨hp.2.1, hp.2.2⟩ f g h

theorem chapter12_closed_subgroup_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D_G D_K : Chapter12CommutativeGroupSchemeDescentDatum p)
    {G : Chapter12CommutativeGroupScheme S}
    (eG : Chapter12CommutativeGroupScheme.baseChange p G ≅ D_G.upstairs)
    (iT : D_K.upstairs ⟶ D_G.upstairs)
    (hiT : chapter12CommutativeDescentHomCompatible D_K D_G iT)
    (hclosed : IsClosedImmersion
      (Chapter12CommutativeGroupScheme.homScheme iT)) :
    ∃ (K : Chapter12CommutativeGroupScheme S) (i : K ⟶ G)
      (eK : Chapter12CommutativeGroupScheme.baseChange p K ≅ D_K.upstairs),
      IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme i) ∧
        Chapter12CommutativeGroupScheme.baseChangeHom p i = eK.hom ≫ iT ≫ eG.inv := by
  sorry

theorem chapter12_finiteLocallyFree_closed_subgroup_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D_G D_K : Chapter12CommutativeGroupSchemeDescentDatum p)
    {G : Chapter12CommutativeGroupScheme S}
    (eG : Chapter12CommutativeGroupScheme.baseChange p G ≅ D_G.upstairs)
    (iT : D_K.upstairs ⟶ D_G.upstairs)
    (hiT : chapter12CommutativeDescentHomCompatible D_K D_G iT)
    (hclosed : IsClosedImmersion
      (Chapter12CommutativeGroupScheme.homScheme iT))
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D_K.upstairs.X.hom) :
    ∃ (K : Chapter12CommutativeGroupScheme S) (i : K ⟶ G)
      (eK : Chapter12CommutativeGroupScheme.baseChange p K ≅ D_K.upstairs),
      IsClosedImmersion (Chapter12CommutativeGroupScheme.homScheme i) ∧
        Chapter12FiniteLocallyFree K.X.hom ∧
        Chapter12CommutativeGroupScheme.baseChangeHom p i = eK.hom ≫ iT ≫ eG.inv := by
  sorry

/-! ### Exact sequences -/

/--
An exact sequence of commutative group schemes.  The first map is identified with the kernel by a
pullback square, and the second map is required to be fppf; this is the fppf-sheaf exactness
convention used in the source.
-/
structure Chapter12ExactSequence
    {S : Scheme.{u}}
    (G' G G'' : Chapter12CommutativeGroupScheme S) where
  inclusion : G' ⟶ G
  projection : G ⟶ G''
  kernel : Chapter12CommutativeGroupScheme S
  kernelMap : kernel ⟶ G
  kernelIso : G' ≅ kernel
  kernelIso_inclusion : kernelIso.hom ≫ kernelMap = inclusion
  kernelIsPullback :
    IsPullback
      (Chapter12CommutativeGroupScheme.homScheme kernelMap)
      kernel.X.hom
      (Chapter12CommutativeGroupScheme.homScheme projection)
      (η[G''.X].left)
  projectionFppf : Chapter12Fppf (Chapter12CommutativeGroupScheme.homScheme projection)

@[simp]
theorem Chapter12ExactSequence.kernelMap_comp_projection
    {S : Scheme.{u}}
    {G' G G'' : Chapter12CommutativeGroupScheme S}
    (E : Chapter12ExactSequence G' G G'') :
    E.kernelMap ≫ E.projection =
      E.kernelIso.inv ≫ E.inclusion ≫ E.projection := by
  rw [← E.kernelIso_inclusion]
  simp

theorem chapter12_kernel_is_stable_under_base_change
    {S T : Scheme.{u}} (p : T ⟶ S)
    {G' G G'' : Chapter12CommutativeGroupScheme S}
    (E : Chapter12ExactSequence G' G G'') :
    IsPullback
      (Chapter12CommutativeGroupScheme.homScheme
        (Chapter12CommutativeGroupScheme.baseChangeHom p E.kernelMap))
      (Chapter12CommutativeGroupScheme.baseChange p E.kernel).X.hom
      (Chapter12CommutativeGroupScheme.homScheme
        (Chapter12CommutativeGroupScheme.baseChangeHom p E.projection))
      (η[(Chapter12CommutativeGroupScheme.baseChange p E.kernel).X].left) := by
  sorry

/-- An exact sequence whose three terms are finite locally free. -/
structure Chapter12FiniteLocallyFreeExactSequence
    {S : Scheme.{u}}
    (G' G G'' : Chapter12CommutativeGroupScheme S) where
  exact : Chapter12ExactSequence G' G G''
  finiteLocallyFree_left : Chapter12FiniteLocallyFree G'.X.hom
  finiteLocallyFree_middle : Chapter12FiniteLocallyFree G.X.hom
  finiteLocallyFree_right : Chapter12FiniteLocallyFree G''.X.hom

theorem chapter12_exact_sequence_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D' D D'' : Chapter12CommutativeGroupSchemeDescentDatum p)
    (E_T : Chapter12ExactSequence D'.upstairs D.upstairs D''.upstairs)
    (hfinite' : Chapter12FiniteLocallyFree D'.upstairs.X.hom)
    (hfinite : Chapter12FiniteLocallyFree D.upstairs.X.hom)
    (hfinite'' : Chapter12FiniteLocallyFree D''.upstairs.X.hom)
    (hi : chapter12CommutativeDescentHomCompatible D' D E_T.inclusion)
    (hq : chapter12CommutativeDescentHomCompatible D D'' E_T.projection) :
    ∃ (G' G G'' : Chapter12CommutativeGroupScheme S)
      (E : Chapter12FiniteLocallyFreeExactSequence G' G G''),
      (Nonempty (Chapter12CommutativeGroupScheme.baseChange p G' ≅ D'.upstairs)) ∧
      (Nonempty (Chapter12CommutativeGroupScheme.baseChange p G ≅ D.upstairs)) ∧
      (Nonempty (Chapter12CommutativeGroupScheme.baseChange p G'' ≅ D''.upstairs)) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
