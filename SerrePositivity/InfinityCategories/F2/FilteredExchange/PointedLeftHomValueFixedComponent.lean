module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedLeftHomValueAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoDisplayCurryComponent

/-!
概要：元の左全作用の固定射成分を、同じ全対角比較の同じ係数制限へ戻す。
方針：端点表示変更と curry の同じ一点評価を順に除去する。
規約：全指定同型を保持。使われ方：元の実長辺 prism の指定普遍比較との値照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom K L))
local notation "v" => ULift.up (SSet.opObjEquiv.symm (functorVertex f))

/-- 元の左全作用の固定射成分は、同じ全対角比較で元の射だけを固定した制限。 -/
lemma pointedLeftHomValueActionIso_app_heq_fixed :
    HEq ((pointedLeftHomValueActionIso K L).app v)
      ((pointedLeftHomDiagonalValueIso K L (fst A H) (snd A H)).precomp
        (lift (𝟙 A) (SSet.const v))) := by
  unfold pointedLeftHomValueActionIso
  exact functorIsoOfEq_curry_app_heq_precomp
    (pointedLeftHomDiagonalValueIso K L (fst A H) (snd A H)) _ _ v

end SerrePositivity.InfinityCategories.F2
