module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeFrame
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleFrameInput
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-!
# 元の半自由 probe 上の選択済み frame と同じテンソル frame の共通族

概要：M10 の二つの frame 族を同じ augmentation の底で比較する。
方針：N01 の実分解と既存の共通 Reedy cofibrant 置換をそのまま使う。
規約：HA §1.3.4、全 probe・全標的に自然な実 Hom 射を保持する。
使われ方：選択済みモデル frame と元の dg Hom の比較の二つの脚。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A]

/-- 概要：N01 の同じ選択済み source frame を元の半自由全族で評価する。
方針：元の probe 包含を前合成する。
規約：HA §1.3.4、全関手。使われ方：標準側の同じ Hom。 -/
def strictRawModuleProbeStandardFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X) := by
  let := strictRawModuleModelCategory A X
  exact strictRawModuleProbeFunctor A X ⋙ (strictRawModuleSourceFrameFamily A X).obj

/-- 概要：同じ二つの全 augmentation の共通 Reedy cofibrant 族。
方針：既存の共通置換へ N01 の実分解と同じ二族を渡す。
規約：HA §1.3.4、底を変えない。使われ方：同じ Hom 比較の共通標的。 -/
def strictRawModuleProbeCommonFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X) := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.commonObj (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)

/-- 概要：同じ共通 frame から同じ選択済み frame への全自然射。
方針：既存の共通置換の左射を保持する。
規約：HA §1.3.4、元の射。使われ方：標準 Hom からの同じ比較。 -/
def strictRawModuleProbeCommonToStandard (X : (operad A).Algebra) :
    strictRawModuleProbeCommonFrame A X ⟶ strictRawModuleProbeStandardFrame A X := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.left (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)

/-- 概要：同じ共通 frame から同じ正規化テンソル frame への全自然射。
方針：既存の共通置換の右射を保持する。
規約：HA §1.3.4、元の射。使われ方：dg Hom 側からの同じ比較。 -/
def strictRawModuleProbeCommonToTensor (X : (operad A).Algebra) :
    strictRawModuleProbeCommonFrame A X ⟶ strictRawModuleProbeTensorFrame A X := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.right (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)

/-- 概要：二つの実 frame 比較は同じ元の probe への augmentation の上にある。
方針：共通置換の元の over 等式を回収する。
規約：HA §1.3.4、全自然変換の等式。使われ方：同じ底の比較の照合。 -/
lemma strictRawModuleProbeCommon_over (X : (operad A).Algebra) :
    let := strictRawModuleModelCategory A X
    strictRawModuleProbeCommonToStandard A X ≫
        Functor.whiskerLeft (strictRawModuleProbeFunctor A X)
          (strictRawModuleSourceFrameFamily A X).augmentation =
      strictRawModuleProbeCommonToTensor A X ≫ strictRawModuleProbeTensorAugmentation A X := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.over (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)

/-- 概要：元の選択済み frame の Hom を二変数の全関手にする。
方針：既存の cosimplicial Hom 二関手を後合成する。
規約：HA §1.3.4、全 probe 射と全標的射。使われ方：局所化側の実 Hom。 -/
def strictRawModuleProbeStandardHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u} :=
  (strictRawModuleProbeStandardFrame A X).op ⋙ cosimplicialHomBifunctor

/-- 概要：同じテンソル frame の Hom を二変数の全関手にする。
方針：既存の cosimplicial Hom 二関手を後合成する。
規約：HA §1.3.4、全単体。使われ方：元の dg Hom に同定する同じ Hom。 -/
def strictRawModuleProbeTensorHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u} :=
  (strictRawModuleProbeTensorFrame A X).op ⋙ cosimplicialHomBifunctor

/-- 概要：同じ共通 frame の Hom を二変数の全関手にする。
方針：既存の cosimplicial Hom 二関手を後合成する。
規約：HA §1.3.4、全単体。使われ方：二つの同じ比較の共通標的。 -/
def strictRawModuleProbeCommonHom (X : (operad A).Algebra) :
    (strictRawModuleProbeCategory A X)ᵒᵖ ⥤ strictRawModuleCategory A X ⥤ SSet.{u} :=
  (strictRawModuleProbeCommonFrame A X).op ⋙ cosimplicialHomBifunctor

/-- 概要：元の標準 Hom から同じ共通 Hom への二変数自然変換。
方針：共通 frame の同じ左射で前合成する。
規約：HA §1.3.4、元の比較射。使われ方：標準 Hom と dg Hom の比較の左脚。 -/
def strictRawModuleProbeHomFromStandard (X : (operad A).Algebra) :
    strictRawModuleProbeStandardHom A X ⟶ strictRawModuleProbeCommonHom A X := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.homLeft (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)

/-- 概要：同じテンソル Hom から同じ共通 Hom への二変数自然変換。
方針：共通 frame の同じ右射で前合成する。
規約：HA §1.3.4、元の比較射。使われ方：標準 Hom と dg Hom の比較の右脚。 -/
def strictRawModuleProbeHomFromTensor (X : (operad A).Algebra) :
    strictRawModuleProbeTensorHom A X ⟶ strictRawModuleProbeCommonHom A X := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.homRight (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)

/-- 概要：同じ共通 frame 族の各値は実 Reedy cofibrant。
方針：元の共通置換の条件を同じ族の型で保持する。
規約：HA §1.3.4、実モデル。使われ方：同じ共通 Hom の Kan 条件。 -/
lemma strictRawModuleProbeCommonFrame_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((strictRawModuleProbeCommonFrame A X).obj P)) := by
  let := strictRawModuleModelCategory A X
  exact FrameOverFunctor.commonObj_cofibrant (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X) P

/-- 概要：同じ共通 frame の全作用素は実モデルの元の弱同値。
方針：元の共通置換の定数性を同じ族の型で保持する。
規約：HA §1.3.4、全作用素。使われ方：同じ共通 Hom の Kan 条件。 -/
lemma strictRawModuleProbeCommonFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) {n m : SimplexCategory} (f : n ⟶ m) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeCommonFrame A X).obj P).map f) := by
  let := strictRawModuleModelCategory A X
  let F := FrameOverFunctor.commonObj (strictRawModuleCofibrantFactorization A X)
    (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
    (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)
  have he : strictRawModuleProbeCommonFrame A X = F := rfl
  have ht := congrArg
    (fun G : strictRawModuleProbeCategory A X ⥤
        (SimplexCategory ⥤ strictRawModuleCategory A X) =>
      weakEquivalences (strictRawModuleCategory A X) ((G.obj P).map f)) he
  exact ht.mpr
    (FrameOverFunctor.commonObj_homotopicallyConstant (strictRawModuleCofibrantFactorization A X)
      (strictRawModuleSourceFrameFamily A X) (strictRawModuleProbeFunctor A X)
      (strictRawModuleProbeTensorFrame A X) (strictRawModuleProbeTensorAugmentation A X)
      (strictRawModuleProbeTensorAugmentation_weak A X) P f)

end SerrePositivity.EInfinity.BarrattEccles
