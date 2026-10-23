module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomMorphismIntervalCancellation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedLeftHomValueFixedComponent

/-!
概要：元の固定射の左値比較を、元の全対角比較の同じ係数制限へ一致させる。
方針：元の頂点表示変更を除き、同じ curry の固定射成分の照合を適用する。
規約：元の指定比較を保持。使われ方：元の長辺比較の値との一致。
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

/-- 元の固定射の左値比較は、元の全対角比較の元の固定射だけによる制限。 -/
lemma pointedHomMorphismLeftValueComparison_heq_diagonal :
    HEq (pointedHomMorphismLeftValueComparison f)
      ((pointedLeftHomDiagonalValueIso K L (fst A H) (snd A H)).precomp
        (lift (𝟙 A) (SSet.const v))) := by
  exact (vertexIsoOfEq_heq _ _ _).trans (pointedLeftHomValueActionIso_app_heq_fixed f)

end SerrePositivity.InfinityCategories.F2
