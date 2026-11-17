module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSourceProjection
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductCornerProjection

/-!
# 実 comma corner の右 slice は元の代数射の全 Over 図式

概要：実 corner の始点からの全錐を、元の D_m→Y の Over 図式に同定する。
方針：保存済みの始域射影と同じ frame 屋根比較の第一射影を接続する。
規約：対象宇宙の異なる nerve 射は全単体で照合する。
使われ方：幾何的右脚と元の RightLeg の自然変換の円柱の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceFrameRoofMap_normalizedOver :
    cofibrantSourceFrameRoofMap A X Y ≫ pullback.fst _ _ ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A))).hom =
    (sourceFrameElementsDKNerveIso A X Y).hom ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofRightSliceMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) := by
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofMap_normalizedOver (cofibrantDKSourceFrame A X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
  exact (Category.assoc _ _ _).trans (congrArg
    (fun g => (sourceFrameElementsDKNerveIso A X Y).hom ≫ g) h)

def cofibrantSourceRoofProductCommaRightOver : cofibrantSourceRoofProductComma A X Y b ⥤
    Over (show (cofibrantAlgebraRelativeCategory A).category from Y) :=
  CostructuredArrow.proj _ _ ⋙ sourceFrameElementsToDK A X Y ⋙
    CostructuredArrow.toOver (cofibrantDKSourceFrame A X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)

lemma cofibrantSourceRoofProductCommaRightOver_nerve :
    cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
      (sourceFrameElementsDKNerveIso A X Y).hom ≫
        nerveMap (CostructuredArrow.toOver (cofibrantDKSourceFrame A X)
          (show (cofibrantAlgebraRelativeCategory A).category from Y)) =
    nerveMap (cofibrantSourceRoofProductCommaRightOver A X Y b) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

lemma cofibrantSourceRoofProductCommaRightSlice :
    cofibrantSourceRoofProductCommaCornerMap A X Y b ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerSourceSliceMap (cofibrantDKSourceFrame A X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) b =
    nerveMap (cofibrantSourceRoofProductCommaRightOver A X Y b) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso
        (show (cofibrantAlgebraRelativeCategory A).category from Y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from Y)))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A))).hom := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerSourceSliceMap_eq_source,
    cofibrantSourceRoofProductCommaCornerMap_source, Category.assoc,
    cofibrantSourceFrameRoofMap_normalizedOver]
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.frameRoofRightSliceMap]
  have h := cofibrantSourceRoofProductCommaRightOver_nerve A X Y b
  simpa only [Category.assoc] using congrArg
    (fun g => g ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso
      (show (cofibrantAlgebraRelativeCategory A).category from Y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (show (cofibrantAlgebraRelativeCategory A).category from Y)))
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A)) ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (cofibrantAlgebraRelativeCategory A))).hom) h

end SerrePositivity.EInfinity.BarrattEccles
