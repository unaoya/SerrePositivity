module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofAugmentationImage
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductReference
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockActions

/-!
# 元の指定次数 roof の全代数への像と同じ弱基準射の hammock 部分

概要：元の四列比較を包含で送り、保存済みの基準射の実 hammock 写像へ戻す。
方針：元の前合成作用との可換性と augmentation roof の厳密な像を接続する。
規約：全パラメータ・元の包含・元の D_n→X の前合成を保持する。
使われ方：基準射側 hR の全 Kan Hom と同じ pinched Hom への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma cofibrantAlgebraHammockColimitInclusionMap_precompose (Z : CofibrantAlgebra A)
    {U V : CofibrantAlgebra A}
    (f : (show (cofibrantAlgebraRelativeCategory A).category from U) ⟶
      (show (cofibrantAlgebraRelativeCategory A).category from V)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (cofibrantAlgebraRelativeCategory A).weakEquivalences f)
      (show (cofibrantAlgebraRelativeCategory A).category from Z) ≫
      cofibrantAlgebraHammockColimitInclusionMap A U Z =
    cofibrantAlgebraHammockColimitInclusionMap A V Z ≫
      algebraReducedHammockPrecompose A Z.obj ((cofibrantAlgebraDKInclusion A).map f) := by
  let := modelCategory A
  have hp := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_precompose (cofibrantAlgebraRelativeCategory A).weakEquivalences
    (show (cofibrantAlgebraRelativeCategory A).category from Z) f
  have hi := cofibrantAlgebraHammockInclusionMap_precompose A
    (show (cofibrantAlgebraRelativeCategory A).category from Z) f
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso _ _ _).hom ≫ _) =
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso _ _ _).hom ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (fun g => g ≫ cofibrantAlgebraHammockInclusionMap A
      (show (cofibrantAlgebraRelativeCategory A).category from U)
      (show (cofibrantAlgebraRelativeCategory A).category from Z)) hp.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg
      (fun g => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (cofibrantAlgebraRelativeCategory A).weakEquivalences
        (show (cofibrantAlgebraRelativeCategory A).category from V)
        (show (cofibrantAlgebraRelativeCategory A).category from Z)).hom ≫ g) hi).trans
      (Category.assoc _ _ _).symm)))

variable (X Y : CofibrantAlgebra A) (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaDegreeHammockMap_transport :
    (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
      cofibrantSourceRoofProductDegreeHammockMap A X Y b =
    cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
      sourceFrameReducedHammockNerveMap A X.obj Y.obj ≫
        cofibrantSourceRoofDegreePrecompose A X Y b := by
  have h : (cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
      cofibrantSourceRoofProductFirstNerve A X Y b =
    cofibrantSourceRoofProductCommaFirstNerve A X Y b := by
    rw [Iso.inv_comp_eq]
    exact (cofibrantSourceRoofProductCommaIso_first A X Y b).symm
  simp only [cofibrantSourceRoofProductDegreeHammockMap, cofibrantSourceRoofProductHammockMap,
    Category.assoc]
  rw [← Category.assoc, ← Category.assoc, h, Category.assoc]

lemma cofibrantSourceRoofProductCommaEvaluationRoofMap_image_Q :
    AnodyneHomotopy.anodyneQ.map (cofibrantSourceRoofProductCommaEvaluationRoofMap A X Y b ≫
      cofibrantAlgebraHammockColimitInclusionMap A (cofibrantSourceRoofDegreeAlgebra A X Y b) Y) =
    AnodyneHomotopy.anodyneQ.map ((cofibrantSourceRoofProductCommaIso A X Y b).inv ≫
      cofibrantSourceRoofProductDegreeHammockMap A X Y b) := by
  have hp := cofibrantAlgebraHammockColimitInclusionMap_precompose A Y
    (U := cofibrantSourceRoofDegreeAlgebra A X Y b) (V := X)
    ((cofibrantDKSourceFrameAugmentation A X).app (cofibrantSourceRoofDegree A X Y b))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (cofibrantAlgebraRelativeCategory A).weakEquivalences
        ((cofibrantDKSourceFrameAugmentation A X).app (cofibrantSourceRoofDegree A X Y b)))
      (show (cofibrantAlgebraRelativeCategory A).category from Y) ≫
      cofibrantAlgebraHammockColimitInclusionMap A (cofibrantSourceRoofDegreeAlgebra A X Y b) Y =
    cofibrantAlgebraHammockColimitInclusionMap A X Y ≫
      cofibrantSourceRoofDegreePrecompose A X Y b at hp
  have hpQ := congrArg AnodyneHomotopy.anodyneQ.map hp
  have haQ := congrArg AnodyneHomotopy.anodyneQ.map
    (cofibrantSourceRoofProductCommaAugmentationRoofMap_image A X Y b)
  have hrQ := congrArg AnodyneHomotopy.anodyneQ.map
    (cofibrantSourceRoofProductCommaDegreeHammockMap_transport A X Y b)
  simp only [Functor.map_comp] at hpQ haQ hrQ ⊢
  rw [cofibrantSourceRoofProductCommaEvaluationRoofMap_sourceComparison, Category.assoc, hpQ,
    reassoc_of% haQ]
  simpa only [Category.assoc] using hrQ.symm

end SerrePositivity.EInfinity.BarrattEccles
