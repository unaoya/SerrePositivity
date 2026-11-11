module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.IntervalEndpointTransport
/-!
概要：同じ二段の端点等式による輸送を一段の輸送へまとめる。
方針：端点等式を消去し、元の全写像空間の恒等射へ帰着する。
規約：pinched 模型と区間模型の元の代表を変更しない。
使われ方：正本矢印の端点輸送と全区間座標の一致を照合する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
lemma dgGluingPinchedEndpointIso_trans {X : SSet.{u}} {x y x' y' x'' y'' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (hx' : x' = x'') (hy' : y' = y'') :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso hx hy).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso hx' hy').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (hx.trans hx') (hy.trans hy')).hom := by
  subst x'
  subst y'
  subst x''
  subst y''
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
