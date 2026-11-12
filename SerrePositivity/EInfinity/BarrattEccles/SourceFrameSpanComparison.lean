module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceTargetComparison
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpans
public import SerrePositivity.EInfinity.FrameHom.FrameSpanTargetHomotopy

/-!
# 元の終域への frame Hom と同じ Map^h の三本矢比較

概要：右脚を恒等射にした元の frame 比較を、既存の選択と照合する。
方針：同じ cofibrant frame と元の fibrant 置換射の自然変換を使う。
規約：元の全単体と既存の比較射を保持する。
使われ方：Map^h と hammock の比較の両端点自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

def sourceFrameSpecialHammockNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (algebraSpecialHammock A X Y) := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap _ _ q.obj q.augmentation
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q) (𝟙 Y)
    ((trivialCofibrations (operad A).Algebra).id_mem Y)

def sourceFrameMappingSpaceIndexMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) :=
  nerveMap (ULiftHom.down.{0, u, u + 1} ⋙
    (((sourceFrameHomComparison A).app (op X)).app Y).mapElements.op ⋙ ULiftHom.up)

def sourceFrameSpecialHammockHomotopy (X Y : (operad A).Algebra) :
    SSet.Homotopy (sourceFrameSpecialHammockNerveMap A X Y)
      (sourceFrameMappingSpaceIndexMap A X Y ≫ mappingSpaceSpecialHammockNerveMap A X Y) := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X
  let j := (fibrantTargetComparison (mappingFibrantFactorization A)).app Y
  exact FrameHom.frameSpanTargetHomotopy _ _ q.obj q.augmentation
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q) (𝟙 Y)
    ((trivialCofibrations (operad A).Algebra).id_mem Y) j
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantTargetComparison_trivialCofibration (mappingFibrantFactorization A) Y)
    j (Category.id_comp j)

end SerrePositivity.EInfinity.BarrattEccles
