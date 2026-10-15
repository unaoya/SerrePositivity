module
public import SerrePositivity.DifferentialGraded.Module.CellLifting
public import SerrePositivity.DifferentialGraded.Module.Colimits

/-! # 自由diskの余積による任意dg加群の次数ごと全射な被覆

各対象・整数次数・斉次要素について自由diskを一つ取り、その生成元を指定要素へ送る。
添字はu-smallで、全作用と余積は主加群圏の既存構成を再利用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 被覆の生成元：対象・次数・その評価での斉次要素。 -/
def ModuleDiskCoverIndex (M : ModuleCategory A D) :=
  Σ x : D, Σ n : ℤ, ((moduleEvaluation A D x).obj M).X n

instance moduleDiskCoverIndexSmall (M : ModuleCategory A D) :
    Small.{u} (ModuleDiskCoverIndex A D M) := by
  unfold ModuleDiskCoverIndex
  infer_instance

def moduleDiskCoverFamily (M : ModuleCategory A D) :
    ModuleDiskCoverIndex A D M → ModuleCategory A D :=
  fun j => freeDisk A D j.1 j.2.1

/-- 自由diskのu-small余積。 -/
def moduleDiskCover (M : ModuleCategory A D) : ModuleCategory A D := ∐ moduleDiskCoverFamily A D M

def moduleDiskCoverι (M : ModuleCategory A D) (j : ModuleDiskCoverIndex A D M) :
    moduleDiskCoverFamily A D M j ⟶ moduleDiskCover A D M :=
  Sigma.ι (moduleDiskCoverFamily A D M) j

/-- 全斉次生成元を指定された像へ送る被覆射。 -/
def moduleDiskCoverπ (M : ModuleCategory A D) : moduleDiskCover A D M ⟶ M :=
  Sigma.desc (fun j : ModuleDiskCoverIndex A D M =>
    (freeDiskHomEquiv A D j.1 j.2.1 M).symm j.2.2)

@[reassoc]
lemma moduleDiskCoverι_π (M : ModuleCategory A D) (j : ModuleDiskCoverIndex A D M) :
    moduleDiskCoverι A D M j ≫ moduleDiskCoverπ A D M =
      (freeDiskHomEquiv A D j.1 j.2.1 M).symm j.2.2 :=
  Sigma.ι_comp_desc _ _

/-- 被覆射は全対象・全整数次数で全射。 -/
lemma moduleDiskCoverπ_degreewiseSurjective (M : ModuleCategory A D) :
    moduleDegreewiseSurjective A D (moduleDiskCoverπ A D M) := by
  intro x n y
  let j : ModuleDiskCoverIndex A D M := ⟨x, n, y⟩
  refine ⟨freeDiskHomEquiv A D x n (moduleDiskCover A D M) (moduleDiskCoverι A D M j), ?_⟩
  have h := congrArg (freeDiskHomEquiv A D x n M) (moduleDiskCoverι_π A D M j)
  rw [freeDiskHomEquiv_naturality] at h
  exact h.trans ((freeDiskHomEquiv A D x n M).apply_symm_apply y)

end SerrePositivity.DifferentialGraded
