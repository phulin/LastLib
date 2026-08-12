import LastLib.Book04AdelesAndIdeles.Chapter10.Section03CompatibilityWithPrincipalIdeles

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators
open Chapter10GlobalNormData

/-! ## 10.4. Local conditions versus a global norm -/

namespace Chapter10GlobalNormData

variable {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
  [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]

/-- The local norm map at a base place. -/
def localNormAtPlace
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) :
    (∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL)) →* Kloc v where
  toFun y := by
    exact ∏ w : {w : ιL // d.below w = v},
      d.chapter10LocalNormAt v w (y w)
  map_one' := by
    sorry
  map_mul' := by
    sorry

@[simp]
theorem localNormAtPlace_apply
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK)
    (y : ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL)) :
    d.localNormAtPlace v y =
      ∏ w : {w : ιL // d.below w = v},
        d.chapter10LocalNormAt v w (y w) := by
  rfl

/-- The local norm image at a place. -/
def localNormImageAtPlace
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) : Set (Kloc v) :=
  Set.range (d.localNormAtPlace v)

theorem mem_localNormImageAtPlace_iff
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) (x : Kloc v) :
    x ∈ d.localNormImageAtPlace v ↔
      ∃ y : ∀ w : {w : ιL // d.below w = v}, Lloc (w : ιL),
        d.localNormAtPlace v y = x := Iff.rfl

end Chapter10GlobalNormData

/-- Componentwise local normicity for an element of the base restricted
product. -/
def chapter10ComponentwiseLocalNormicity
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : kIdeles d) : Prop :=
  ∀ v, x v ∈ d.localNormImageAtPlace v

theorem chapter10_mem_componentwise_local_normicity_iff
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (x : kIdeles d) :
    chapter10ComponentwiseLocalNormicity d x ↔
      ∀ v, x v ∈ d.localNormImageAtPlace v := Iff.rfl

theorem chapter10_adelic_norm_image_imp_componentwise_local_norm
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (x : kIdeles d) (y : lIdeles d) (hy : d.adelicNormHom y = x) :
    chapter10ComponentwiseLocalNormicity d x := by
  sorry

/-- The finite-exception hypothesis needed for assembling local preimages.
At almost every place it asks for a unit preimage in one factor, exactly as
in the proof of the source statement. -/
def chapter10UnitPreimageOutsideFiniteSet
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∀ u : Kloc v, u ∈ d.unitK v →
    ∃ w : {w : ιL // d.below w = v}, ∃ y : Lloc (w : ιL),
      y ∈ d.unitL (w : ιL) ∧ d.chapter10LocalNormAt v w y = u

theorem chapter10_adelic_norm_image_componentwise_iff
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (hunit : chapter10UnitPreimageOutsideFiniteSet d) (x : kIdeles d) :
    x ∈ Set.range d.adelicNormHom ↔
      chapter10ComponentwiseLocalNormicity d x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact chapter10_adelic_norm_image_imp_componentwise_local_norm d _ y rfl
  · sorry

/-- The intersection `G ∩ N(I)` expressed through the principal embedding. -/
def chapter10AdelicNormIntersectionSet
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) : Set G :=
  {b | principal b ∈ Set.range N}

theorem chapter10_mem_adelic_norm_intersection_iff
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) (b : G) :
    b ∈ chapter10AdelicNormIntersectionSet principal N ↔
      ∃ y : J, N y = principal b := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩

theorem chapter10_global_norm_implies_local_norm
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (pK : G_K →* kIdeles d) (pL : G_L →* lIdeles d)
    (globalNorm : G_L →* G_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm
      d.adelicNormHom)
    (b : G_K) (hb : ∃ a : G_L, globalNorm a = b) :
    chapter10ComponentwiseLocalNormicity d (pK b) := by
  rcases hb with ⟨a, rfl⟩
  exact chapter10_adelic_norm_image_imp_componentwise_local_norm d
    (pK (globalNorm a)) (pL a) (DFunLike.congr_fun hcompat a)

theorem chapter10_global_norm_intersection_is_everywhere_local_norm
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (pK : G_K →* kIdeles d)
    (hunit : chapter10UnitPreimageOutsideFiniteSet d) :
    chapter10AdelicNormIntersectionSet pK d.adelicNormHom =
      {b | chapter10ComponentwiseLocalNormicity d (pK b)} := by
  ext b
  rw [chapter10_mem_adelic_norm_intersection_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact chapter10_adelic_norm_image_imp_componentwise_local_norm d
      (pK b) y hy
  · intro hb
    have : pK b ∈ Set.range d.adelicNormHom := by
      exact (chapter10_adelic_norm_image_componentwise_iff d hunit (pK b)).2 hb
    exact this

/-! The local--global obstruction is a quotient, not an automatic theorem. -/

def chapter10GlobalFieldNormSubgroup
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    (globalNorm : G_L →* G_K) : Subgroup G_K :=
  Subgroup.map globalNorm ⊤

def chapter10AdelicNormImageSubgroup
    {I J : Type*} [CommGroup I] [CommGroup J]
    (N : J →* I) : Subgroup I :=
  Subgroup.map N ⊤

def chapter10AdelicNormIntersectionSubgroup
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) : Subgroup G :=
  (chapter10AdelicNormImageSubgroup N).comap principal

theorem chapter10_global_norm_subgroup_le_intersection
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm ideleNorm) :
    chapter10GlobalFieldNormSubgroup globalNorm ≤
      chapter10AdelicNormIntersectionSubgroup pK ideleNorm := by
  sorry

/-- The obstruction quotient
`(G_K ∩ N(I_L))/N(G_L)`. -/
def chapter10LocalGlobalNormObstruction
    {G_K G_L : Type*} [CommGroup G_K] [CommGroup G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (_pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (_hle : chapter10GlobalFieldNormSubgroup globalNorm ≤
      chapter10AdelicNormIntersectionSubgroup pK ideleNorm) : Type _ :=
  chapter10AdelicNormIntersectionSubgroup pK ideleNorm ⧸
    (chapter10GlobalFieldNormSubgroup globalNorm).subgroupOf
      (chapter10AdelicNormIntersectionSubgroup pK ideleNorm)

/- The source explicitly warns that no vanishing of this quotient follows from
finite/separable/Galois hypotheses alone; the warning is preserved in the API
by defining the obstruction without postulating it to be trivial. -/

/-- The image in the idele class group permits an arbitrary principal factor. -/
def chapter10ClassNormImage
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm ideleNorm) :
    Set (chapter10IdeleClassGroup pK) :=
  Set.range (chapter10IdeleClassNorm pK pL globalNorm ideleNorm hcompat)

def chapter10PrincipalTimesAdelicNormSet
    {G I J : Type*} [Group G] [CommGroup I] [CommGroup J]
    (principal : G →* I) (N : J →* I) : Set I :=
  {x | ∃ g : G, ∃ y : J, principal g * N y = x}

theorem chapter10_class_norm_image_is_principal_times_adelic_norm
    {G_K G_L : Type*} [Group G_K] [Group G_L]
    {I_K I_L : Type*} [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (globalNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL globalNorm ideleNorm) :
    chapter10ClassNormImage pK pL globalNorm ideleNorm hcompat =
      QuotientGroup.mk' (chapter10PrincipalSubgroup pK) ''
        chapter10PrincipalTimesAdelicNormSet pK ideleNorm := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter10
