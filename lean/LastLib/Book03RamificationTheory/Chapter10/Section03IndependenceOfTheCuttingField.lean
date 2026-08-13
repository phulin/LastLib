import LastLib.Book03RamificationTheory.Chapter10.Section02ArtinAndSwanConductors

namespace LastLib.Book03RamificationTheory.Chapter10

noncomputable section

open MeasureTheory

/-! ## 10.3. Independence of the cutting field -/

universe uE uV uBig uSmall uG uQ uQbig uQsmall

variable {E : Type uE} {V : Type uV}
variable [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem herbrand_upper_groups_project
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall) (v : ℝ) :
    (Fbig.upper.group v).map C.projection = Fsmall.upper.group v :=
  C.upper_map v

theorem herbrand_projection_surjective
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall) :
    Function.Surjective C.projection := C.surjective

def KernelActsTriviallyOn
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Group Gsmall]
    (q : Gbig →* Gsmall) (ρ : Representation E Gbig V) : Prop :=
  ∀ g : Gbig, g ∈ q.ker → ρ g = LinearMap.id

omit [FiniteDimensional E V] in
theorem kernel_acts_trivially_of_factorization
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Group Gsmall]
    (q : Gbig →* Gsmall) (ρbig : Representation E Gbig V)
    (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp q) :
    KernelActsTriviallyOn q ρbig := by
  intro g hg
  rw [hfactor]
  have hgq : q g = 1 := hg
  change ρsmall (q g) = LinearMap.id
  rw [hgq]
  simpa only [Module.End.one_eq_id] using ρsmall.map_one

theorem fixedSpaceCodim_upper_projection
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection) (v : ℝ) :
    fixedSpaceCodim ρbig (Fbig.upper.group v) =
      fixedSpaceCodim ρsmall (Fsmall.upper.group v) := by
  rw [hfactor]
  unfold fixedSpaceCodim
  rw [fixedSpace.comp_eq_map, C.upper_map_eq v]

theorem upperFixedSpaceFunction_projection_eq
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection) :
    upperFixedSpaceFunction Fbig ρbig = upperFixedSpaceFunction Fsmall ρsmall := by
  funext v
  simp only [upperFixedSpaceFunction]
  exact congrArg (fun n : ℕ => (n : ℝ))
    (fixedSpaceCodim_upper_projection C ρbig ρsmall hfactor v)

theorem upperDepthArea_projection_eq
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection) :
    upperDepthArea Fbig ρbig = upperDepthArea Fsmall ρsmall := by
  apply upperDepthArea_congr_ae
  exact Filter.Eventually.of_forall
    (fun v => congrFun (upperFixedSpaceFunction_projection_eq C ρbig ρsmall hfactor) v)

theorem swanConductor_independent_of_cutting_field
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection)
    (hbig : Fbig.residue_separable) (hsmall : Fsmall.residue_separable) :
    swanConductor Fbig hbig ρbig = swanConductor Fsmall hsmall ρsmall := by
  apply Rat.cast_injective (α := ℝ)
  rw [swanConductor_eq_upperDepthArea Fbig hbig ρbig,
    swanConductor_eq_upperDepthArea Fsmall hsmall ρsmall,
    upperDepthArea_projection_eq C ρbig ρsmall hfactor]

theorem artinConductor_independent_of_cutting_field
    {Gbig : Type uBig} {Gsmall : Type uSmall}
    [Group Gbig] [Fintype Gbig] [Group Gsmall] [Fintype Gsmall]
    {Fbig : RamificationFiltration Gbig}
    {Fsmall : RamificationFiltration Gsmall}
    (C : HerbrandQuotientData Fbig Fsmall)
    (ρbig : Representation E Gbig V) (ρsmall : Representation E Gsmall V)
    (hfactor : ρbig = ρsmall.comp C.projection)
    (hbig : Fbig.residue_separable) (hsmall : Fsmall.residue_separable) :
    artinConductor Fbig hbig ρbig = artinConductor Fsmall hsmall ρsmall := by
  rw [artinConductor_eq_tame_add_swan Fbig hbig ρbig,
    artinConductor_eq_tame_add_swan Fsmall hsmall ρsmall]
  congr 1
  · change (fixedSpaceCodim ρbig (Fbig.lower.group 0) : ℚ) =
      (fixedSpaceCodim ρsmall (Fsmall.lower.group 0) : ℚ)
    have h := fixedSpaceCodim_upper_projection C ρbig ρsmall hfactor 0
    simpa only [UpperRamificationFiltration.group_zero_eq_lower_zero] using
      congrArg (fun n : ℕ => (n : ℚ)) h
  · apply swanConductor_independent_of_cutting_field C ρbig ρsmall hfactor hbig hsmall

/-- The conductor computed from one chosen finite cutting quotient. -/
def conductorViaCuttingField
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type uQ} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q)
    (hseparable : R.ramification.residue_separable) : ℚ :=
  artinConductor R.ramification hseparable R.action

def swanViaCuttingField
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type uQ} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q)
    (hseparable : R.ramification.residue_separable) : ℚ :=
  swanConductor R.ramification hseparable R.action

theorem conductorViaCuttingField_independent
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig : Type uQbig} {Qsmall : Type uQsmall}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection)
    (hbig : Rbig.ramification.residue_separable)
    (hsmall : Rsmall.ramification.residue_separable) :
    conductorViaCuttingField ρ Rbig hbig = conductorViaCuttingField ρ Rsmall hsmall := by
  exact artinConductor_independent_of_cutting_field C Rbig.action Rsmall.action hfactor hbig hsmall

theorem swanViaCuttingField_independent
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig : Type uQbig} {Qsmall : Type uQsmall}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection)
    (hbig : Rbig.ramification.residue_separable)
    (hsmall : Rsmall.ramification.residue_separable) :
    swanViaCuttingField ρ Rbig hbig = swanViaCuttingField ρ Rsmall hsmall := by
  exact swanConductor_independent_of_cutting_field C Rbig.action Rsmall.action hfactor hbig hsmall

/-- An absolute-Galois conductor is evaluated through any chosen finite
cutting quotient; the preceding theorem supplies well-definedness. -/
def absoluteGaloisConductorVia
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type uQ} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q)
    (hseparable : R.ramification.residue_separable) : ℚ :=
  conductorViaCuttingField ρ R hseparable

def absoluteGaloisSwanVia
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Q : Type uQ} [Group Q] [Fintype Q]
    (R : FiniteQuotientRealization ρ Q)
    (hseparable : R.ramification.residue_separable) : ℚ :=
  swanViaCuttingField ρ R hseparable

theorem absoluteGaloisConductorVia_well_defined
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig : Type uQbig} {Qsmall : Type uQsmall}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection)
    (hbig : Rbig.ramification.residue_separable)
    (hsmall : Rsmall.ramification.residue_separable) :
    absoluteGaloisConductorVia ρ Rbig hbig =
      absoluteGaloisConductorVia ρ Rsmall hsmall := by
  exact conductorViaCuttingField_independent ρ Rbig Rsmall C hfactor hbig hsmall

theorem absoluteGaloisSwanVia_well_defined
    {G : Type uG} [Group G]
    (ρ : FiniteImageRepresentation E G V)
    {Qbig : Type uQbig} {Qsmall : Type uQsmall}
    [Group Qbig] [Fintype Qbig] [Group Qsmall] [Fintype Qsmall]
    (Rbig : FiniteQuotientRealization ρ Qbig)
    (Rsmall : FiniteQuotientRealization ρ Qsmall)
    (C : HerbrandQuotientData Rbig.ramification Rsmall.ramification)
    (hfactor : Rbig.action = Rsmall.action.comp C.projection)
    (hbig : Rbig.ramification.residue_separable)
    (hsmall : Rsmall.ramification.residue_separable) :
    absoluteGaloisSwanVia ρ Rbig hbig = absoluteGaloisSwanVia ρ Rsmall hsmall := by
  exact swanViaCuttingField_independent ρ Rbig Rsmall C hfactor hbig hsmall

end
end LastLib.Book03RamificationTheory.Chapter10
