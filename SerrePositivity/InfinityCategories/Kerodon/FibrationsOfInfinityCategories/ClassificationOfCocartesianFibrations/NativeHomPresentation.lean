module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FibrationBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackNativeFunctor

/-!
概要：底変換した fibration の豊穣 Hom と、同じ native core 関手の値の厳密な一致。
方針：元の底変換対象と Hom の定義を、固定した小さい端点で正規化する。
規約：元の全相対 Hom を変更しない。
使われ方：標準単体の表示変更で巨大な比較の展開を避ける。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の底変換対象の豊穣 Hom は、同じ底上の native Hom の core そのもの。 -/
lemma cocartesianBaseChangeHom_nativePresentation {B D : SSet.{u}} [Quasicategory B]
    (k : D ⟶ B) (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B) :
    SimplicialCategory.sHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched k).obj p)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFibrationBaseChangeCoreEnriched k).obj q) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op (Over.mk k)) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
