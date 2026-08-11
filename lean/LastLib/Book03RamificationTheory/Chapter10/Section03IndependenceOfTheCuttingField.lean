import LastLib.Book03RamificationTheory.Chapter10.Section02ArtinAndSwanConductors

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

open MeasureTheory

/-! ## 10.3. Independence of the cutting field -/

universe u v w

variable {E : Type u} {V : Type w}
variable [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem herbrand_upper_groups_project
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall) (v : ℝ) :
    (Fbig.upper.group v).map C.projection = Fsmall.upper.group v :=
  C.upper_map v

theorem herbrand_projection_surjective
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall) :
    Function.Surjective C.projection := C.surjective

def KernelActsTriviallyOn
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Group Gsmall]
    (q : Gbig →* Gsmall) (ρ : Representation E Gbig V) : Prop :=
  ∀ g : Gbig, g ∈ q.ker → ρ g = LinearMap.id

theorem kernel_acts_trivially_of_factorization
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Group Gsmall]
    (q : Gbig →* Gsmall) (ρbig : Representation E Gbig V)
    (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp q) :
    KernelActsTriviallyOn q ρbig := by
  sorry

theorem fixedSpaceCodim_upper_projection
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection) (v : ℝ) :
    fixedSpaceCodim ρbig (Fbig.upper.group v) =
      fixedSpaceCodim ρsmall (Fsmall.upper.group v) := by
  sorry

theorem upperFixedSpaceFunction_projection_eq
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection) :
    upperFixedSpaceFunction Fbig ρbig = upperFixedSpaceFunction Fsmall ρsmall := by
  sorry

theorem upperDepthArea_projection_eq
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection) :
    upperDepthArea Fbig ρbig = upperDepthArea Fsmall ρsmall := by
  sorry

theorem swanConductor_independent_of_cutting_field
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection)
    (hbig : Fbig.residue_separable) (hsmall : Fsmall.residue_separable) :
    swanConductor Fbig hbig ρbig = swanConductor Fsmall hsmall ρsmall := by
  sorry

theorem artinConductor_independent_of_cutting_field
    {Gbig : Type u} {Gsmall : Type v}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection)
    (hbig : Fbig.residue_separable) (hsmall : Fsmall.residue_separable) :
    artinConductor Fbig hbig ρbig = artinConductor Fsmall hsmall ρsmall := by
  sorry

/-- The conductor computed from one chosen finite cutting quotient. -/
def conductorViaCuttingField
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type*} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q) : ℚ :=
  artinConductor R.ramification R.ramification.residue_separable R.action

def swanViaCuttingField
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type*} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q) : ℚ :=
  swanConductor R.ramification R.ramification.residue_separable R.action

theorem conductorViaCuttingField_independent
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig Qsmall : Type*}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection) :
    conductorViaCuttingField ρ Rbig = conductorViaCuttingField ρ Rsmall := by
  sorry

theorem swanViaCuttingField_independent
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig Qsmall : Type*}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection) :
    swanViaCuttingField ρ Rbig = swanViaCuttingField ρ Rsmall := by
  sorry

/-- An absolute-Galois conductor is evaluated through any chosen finite
cutting quotient; the preceding theorem supplies well-definedness. -/
def absoluteGaloisConductorVia
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type*} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q) : ℚ :=
  conductorViaCuttingField ρ R

def absoluteGaloisSwanVia
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type*} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q) : ℚ :=
  swanViaCuttingField ρ R

theorem absoluteGaloisConductorVia_well_defined
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig Qsmall : Type*}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection) :
    absoluteGaloisConductorVia ρ Rbig = absoluteGaloisConductorVia ρ Rsmall := by
  sorry

theorem absoluteGaloisSwanVia_well_defined
    {G : Type v} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig Qsmall : Type*}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection) :
    absoluteGaloisSwanVia ρ Rbig = absoluteGaloisSwanVia ρ Rsmall := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter10
