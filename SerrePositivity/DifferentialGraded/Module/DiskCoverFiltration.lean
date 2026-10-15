module
public import SerrePositivity.DifferentialGraded.Module.DiskFiltration
public import SerrePositivity.DifferentialGraded.Module.DiskCover
public import SerrePositivity.DifferentialGraded.Module.GradedCoproduct

/-! # 初期自由disk被覆全体の二段sphere filtration -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDiskCoverUpperFamily (M : ModuleCategory A D) :
    ModuleDiskCoverIndex A D M → ModuleCategory A D :=
  fun t => freeSphere A D t.1 (t.2.1 + 1)

def moduleDiskCoverLowerFamily (M : ModuleCategory A D) :
    ModuleDiskCoverIndex A D M → ModuleCategory A D :=
  fun t => freeSphere A D t.1 t.2.1

/-- 初期被覆の部分加群は上次数自由sphereの余積。 -/
def moduleDiskCoverBoundary (M : ModuleCategory A D) :
    (∐ moduleDiskCoverUpperFamily A D M) ⟶ moduleDiskCover A D M :=
  Limits.Sigma.map (fun t : ModuleDiskCoverIndex A D M => freeCellBoundary A D t.1 t.2.1)

/-- 初期被覆の商は下次数自由sphereの余積。 -/
def moduleDiskCoverQuotient (M : ModuleCategory A D) :
    moduleDiskCover A D M ⟶ (∐ moduleDiskCoverLowerFamily A D M) :=
  Limits.Sigma.map (fun t : ModuleDiskCoverIndex A D M => freeDiskToSphere A D t.1 t.2.1)

def moduleDiskCoverGradedSplit (M : ModuleCategory A D) :
    ModuleGradedSplit A D (moduleDiskCoverBoundary A D M) (moduleDiskCoverQuotient A D M) :=
  moduleCoproductGradedSplit A D
    (fun t : ModuleDiskCoverIndex A D M => freeCellBoundary A D t.1 t.2.1)
    (fun t : ModuleDiskCoverIndex A D M => freeDiskToSphere A D t.1 t.2.1)
    (fun t => freeDiskGradedSplit A D t.1 t.2.1)

lemma moduleDiskCoverBoundary_mono (M : ModuleCategory A D) :
    Mono (moduleDiskCoverBoundary A D M) := (moduleDiskCoverGradedSplit A D M).mono

lemma moduleDiskCoverQuotient_epi (M : ModuleCategory A D) :
    Epi (moduleDiskCoverQuotient A D M) := (moduleDiskCoverGradedSplit A D M).epi

def moduleDiskCoverSphereCokernel (M : ModuleCategory A D) :
    IsColimit (CokernelCofork.ofπ (moduleDiskCoverQuotient A D M)
      (moduleDiskCoverGradedSplit A D M).inclusion_projection) :=
  moduleGradedSplitCokernel A D (moduleDiskCoverGradedSplit A D M)

end SerrePositivity.DifferentialGraded
