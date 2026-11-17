module

public import SerrePositivity.EInfinity.BarrattEccles.SourceFrameRoofComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoofPostcompose
public import SerrePositivity.EInfinity.Hammock.ReducedPointActions

/-!
# 元の source frame 比較の終域自然性

概要：元の終域射の作用を同じ reduced 比較が保つ。
方針：元の二列 roof の全単体の正方形と同じ要素圏の augmentation を使う。
規約：元の frame・終域射・比較を保持する。
使われ方：既存 Map^h の高次比較の終域自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra Opposite Hammock SerrePositivity.SimplicialModel
open SerrePositivity.Reedy
variable (A : Type u) [CommRing A] (X : (operad A).Algebra) {Y Z : (operad A).Algebra}

def sourceFramePostcomposeIndexMap (g : Y ⟶ Z) :
    nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (ULiftHom.{u + 1} (((((sourceFrameHom A).obj (op X)).obj Z).Elements)ᵒᵖ)) :=
  nerveMap (ULiftHom.down.{0, u, u + 1} ⋙
    (((sourceFrameHom A).obj (op X)).map g).mapElements.op ⋙ ULiftHom.up)

def algebraReducedHammockPostcompose (g : Y ⟶ Z) :
    algebraReducedHammock A X Y ⟶ algebraReducedHammock A X Z := by
  let := modelCategory A
  exact reducedPostcomposeMap (weakEquivalences (operad A).Algebra) X g

lemma sourceFrameReducedHammockNerveMap_postcompose (g : Y ⟶ Z) :
    sourceFramePostcomposeIndexMap A X g ≫ sourceFrameReducedHammockNerveMap A X Z =
      sourceFrameReducedHammockNerveMap A X Y ≫ algebraReducedHammockPostcompose A X g := by
  let := modelCategory A
  let q := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap_postcompose
    (weakEquivalences (operad A).Algebra) q.obj q.augmentation q.augmentation_weakEquivalence
      (fun a => q.homotopicallyConstant a) g
  change sourceFramePostcomposeIndexMap A X g ≫
      (sourceFrameLeftRoofNerveMap A X Z ≫ algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Z) =
    (sourceFrameLeftRoofNerveMap A X Y ≫ algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences (operad A).Algebra) g) at h
  have h' := congrArg (fun k => k ≫ (algebraHammockReductionIso A X Z).hom) h
  rw [← sourceFrameLeftRoofNerveMap_normalization, ← sourceFrameLeftRoofNerveMap_normalization]
  dsimp only [algebraReducedHammockPostcompose, reducedPostcomposeMap]
  simpa only [algebraHammockReductionIso, Category.assoc, Iso.hom_inv_id_assoc] using h'

lemma sourceFramePostcomposeIndexMap_augmentation (g : Y ⟶ Z) :
    sourceFramePostcomposeIndexMap A X g ≫ sourceFrameIndexAugmentation A X Z =
      sourceFrameIndexAugmentation A X Y ≫ SSet.uliftFunctor.{u + 1, u}.map
        (((sourceFrameHom A).obj (op X)).map g) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality _

lemma sourceFrameReducedHammockComparison_postcompose (g : Y ⟶ Z) :
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        (((sourceFrameHom A).obj (op X)).map g)) ≫
      sourceFrameReducedHammockComparison A X Z =
    sourceFrameReducedHammockComparison A X Y ≫
      AnodyneHomotopy.anodyneQ.map (algebraReducedHammockPostcompose A X g) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := sourceFrameIndexAugmentation_localized_isIso A X Y
  have h := congrArg Q.map (sourceFramePostcomposeIndexMap_augmentation A X g)
  simp only [Functor.map_comp] at h
  apply (cancel_epi (Q.map (sourceFrameIndexAugmentation A X Y))).mp
  rw [← Category.assoc, ← h, Category.assoc, sourceFrameReducedHammockComparison_fac,
    ← Q.map_comp, sourceFrameReducedHammockNerveMap_postcompose, Q.map_comp,
    ← sourceFrameReducedHammockComparison_fac, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
