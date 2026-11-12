module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeValuePath
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeComposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：元の cospan 錐の指定可換性と四つの native 余極限写像の値比較を同時に結ぶ。
方針：左右合成の指定比較を、元の二三角形からの指定円柱の像で結ぶ。
規約：四辺・二三角形・全円柱を保持。使われ方：元の Kan 極限錐との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：元の二三角形の可換 path を保持する native な四射の値の可換同型。
方針：左右合成の元の比較を指定 path で結ぶ。
規約：元の全円柱からの同型。使われ方：native な二射影の同時比較。 -/
def coherentCospanConeNativeValuePathIso :
    FunctorIso
      (coherentTotalMapNativeValue F X (coherentTransformationTotalMap F X C.toLeft) ≫
        coherentTotalMapNativeValue X Z (coherentTransformationTotalMap X Z C.fromLeft))
      (coherentTotalMapNativeValue F Y (coherentTransformationTotalMap F Y C.toRight) ≫
        coherentTotalMapNativeValue Y Z (coherentTransformationTotalMap Y Z C.fromRight)) :=
  coherentTotalMapNativeCompositeIso F X Z
    (coherentTransformationTotalMap F X C.toLeft) (coherentTransformationTotalMap X Z C.fromLeft) ≪≫
      (coherentCospanConeValuePathIso F X Y Z C).ulift ≪≫
        (coherentTotalMapNativeCompositeIso F Y Z
          (coherentTransformationTotalMap F Y C.toRight)
          (coherentTransformationTotalMap Y Z C.fromRight)).symm

/-- 概要：native な可換同型は元の四射の値比較と元の指定可換 path に同時に整合。
方針：右合成の指定比較の往復を消去。
規約：指定同型の等式。使われ方：二射影・可換 path を同時に保つ錐比較。 -/
lemma coherentCospanConeNativeValuePathIso_comparison :
    coherentTotalMapNativeCompositeIso F X Z
        (coherentTransformationTotalMap F X C.toLeft)
        (coherentTransformationTotalMap X Z C.fromLeft) ≪≫
      (coherentCospanConeValuePathIso F X Y Z C).ulift =
    coherentCospanConeNativeValuePathIso F X Y Z C ≪≫
      coherentTotalMapNativeCompositeIso F Y Z
        (coherentTransformationTotalMap F Y C.toRight)
        (coherentTransformationTotalMap Y Z C.fromRight) := by
  simp [coherentCospanConeNativeValuePathIso, Iso.trans_assoc]

end SerrePositivity.InfinityCategories.F2
