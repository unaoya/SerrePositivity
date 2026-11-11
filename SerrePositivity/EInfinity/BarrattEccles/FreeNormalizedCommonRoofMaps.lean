module
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedCommonFrameProperties
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedHomEquivalence
public import SerrePositivity.EInfinity.BarrattEccles.SourceFrameRoofComparison
public import SerrePositivity.EInfinity.FrameHom.FrameRoofComparisonInvariance
/-! 概要：元の正規化・共通 frame の全単体を同じ代数屋根へ送る。
方針：元の augmentation と全要素の評価を既存の二列 roof に代入する。
規約：全作用素・同じ自由 probe と標的代数を保持する。
使われ方：元の標準自由 Hom span と全 pinched 族の比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)

/-- 概要：元の標準自由 Hom から同じ共通 Hom への全要素圏写像。
方針：元の左 frame 比較に沿う前合成を使う。
規約：元の全要素を保持。使われ方：標準弱 span の左脚。 -/
def freeNormalizedCommonLeftIndex :
    ULiftHom.{u + 1} (((((sourceFrameHom A).obj
      (op ((freeProbeFunctor A).obj X))).obj B).Elements)ᵒᵖ) ⥤
    ULiftHom.{u + 1} (((((freeNormalizedHomMiddle A).obj (op X)).obj B).Elements)ᵒᵖ) := by
  let := modelCategory A
  exact FrameHom.frameSpanSourceIndexMap ((freeNormalizedCommonFrame A).obj X)
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj
      ((freeProbeFunctor A).obj X)) ((freeNormalizedCommonFrameLeft A).app X)

/-- 概要：元の正規化 Hom から同じ共通 Hom への全要素圏写像。
方針：元の右 frame 比較に沿う前合成を使う。
規約：元の全要素を保持。使われ方：標準弱 span の右脚。 -/
def freeNormalizedCommonRightIndex :
    ULiftHom.{u + 1} (((((freeNormalizedProbeHom A).obj (op X)).obj B).Elements)ᵒᵖ) ⥤
    ULiftHom.{u + 1} (((((freeNormalizedHomMiddle A).obj (op X)).obj B).Elements)ᵒᵖ) :=
  FrameHom.frameSpanSourceIndexMap ((freeNormalizedCommonFrame A).obj X)
    ((freeNormalizedProbeFrame A).obj X) ((freeNormalizedCommonFrameRight A).app X)

/-- 概要：元の共通 Hom の全族を同じ reduced 代数 hammock へ送る。
方針：元の共通 augmentation と全評価を二列 roof にする。
規約：元の全単体を保持。使われ方：標準 Hom span の比較対象。 -/
def freeNormalizedCommonReducedRoof :
    nerve (ULiftHom.{u + 1} (((((freeNormalizedHomMiddle A).obj (op X)).obj B).Elements)ᵒᵖ)) ⟶
      algebraReducedHammock A ((freeProbeFunctor A).obj X) B := by
  let := modelCategory A
  exact FrameHom.frameLeftRoofColimitMap (weakEquivalences (operad A).Algebra)
    ((freeNormalizedCommonFrame A).obj X) ((freeNormalizedCommonFrameAugmentation A).app X)
    (freeNormalizedCommonFrameAugmentation_weak A X)
    (fun f => freeNormalizedCommonFrame_map_weak A X f) ≫
      (algebraHammockReductionIso A ((freeProbeFunctor A).obj X) B).hom

/-- 概要：元の正規化自由 Hom の全族を同じ reduced 代数 hammock へ送る。
方針：元の正規化 augmentation と全評価を二列 roof にする。
規約：元の全単体を保持。使われ方：元の標準単位の弱同値検出。 -/
def freeNormalizedTensorReducedRoof :
    nerve (ULiftHom.{u + 1} (((((freeNormalizedProbeHom A).obj (op X)).obj B).Elements)ᵒᵖ)) ⟶
      algebraReducedHammock A ((freeProbeFunctor A).obj X) B := by
  let := modelCategory A
  exact FrameHom.frameLeftRoofColimitMap (weakEquivalences (operad A).Algebra)
    ((freeNormalizedProbeFrame A).obj X) ((freeNormalizedProbeAugmentation A).app X)
    (freeNormalizedProbeAugmentation_weak A X)
    (fun f => freeNormalizedProbeFrame_homotopicallyConstant A X f) ≫
      (algebraHammockReductionIso A ((freeProbeFunctor A).obj X) B).hom

end SerrePositivity.EInfinity.BarrattEccles
