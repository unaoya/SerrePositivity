module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FibrationBaseChange
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeFunctor

/-!
概要：底変換した fibration の豊穣 Hom と、同じ native core 関手の値の厳密な一致。
方針：元の底変換対象と Hom の定義を、固定した小さい端点で正規化する。
規約：元の全相対 Hom を変更しない。
使われ方：標準単体の表示変更で巨大な比較の展開を避ける。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の底変換対象の豊穣 Hom は、同じ底上の native Hom の core そのもの。 -/
lemma cocartesianBaseChangeHom_nativePresentation {B D : SSet.{u}} [Quasicategory B]
    (k : D ⟶ B) (p q : CocartesianFibrationCategory B) :
    SimplicialCategory.sHom ((cocartesianFibrationBaseChangeCoreEnriched k).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched k).obj q) =
    (cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom).obj (Opposite.op (Over.mk k)) := rfl

end SerrePositivity.InfinityCategories
