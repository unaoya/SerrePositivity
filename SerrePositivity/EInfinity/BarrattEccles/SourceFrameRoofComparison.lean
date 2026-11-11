module

public import SerrePositivity.EInfinity.BarrattEccles.SourceFrameReducedComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ResolutionLeftRoof

/-!
# 同じ元の source frame 比較の二列による回収

概要：元の reduced 比較は二列 roof の正規化から厳密に回収できる。
方針：同じ元の frame と恒等右脚挿入の正方形を代入する。
規約：既存の比較射と全単体を変更しない。
使われ方：source frame の両端点自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite Hammock
open SerrePositivity.Reedy
variable (A : Type u) [CommRing A]

def sourceFrameLeftRoofNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      algebraHammockGraph A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X) Y

lemma sourceFrameLeftRoofNerveMap_normalization (X Y : (operad A).Algebra) :
    sourceFrameLeftRoofNerveMap A X Y ≫
        algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y ≫
          (algebraHammockReductionIso A X Y).hom =
      sourceFrameReducedHammockNerveMap A X Y := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X
  have h := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap_normalization q Y
  change sourceFrameLeftRoofNerveMap A X Y ≫
      graphNormalization (weakEquivalences (operad A).Algebra) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word =
    sourceFrameSpecialHammockNerveMap A X Y ≫
      algebraSpecialThreeArrowInclusionNerveMap A X Y ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor ≫
        graphNormalization (weakEquivalences (operad A).Algebra) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow at h
  change sourceFrameLeftRoofNerveMap A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences (operad A).Algebra) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word ≫
        (reducedColimitIso (weakEquivalences (operad A).Algebra) X Y).hom = _
  rw [reducedColimitIso_hom_fac, h]
  change _ = sourceFrameSpecialHammockNerveMap A X Y ≫
    algebraSpecialThreeArrowInclusionNerveMap A X Y ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences (operad A).Algebra) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫
        (reducedColimitIso (weakEquivalences (operad A).Algebra) X Y).hom
  rw [reducedColimitIso_hom_fac]

end SerrePositivity.EInfinity.BarrattEccles
