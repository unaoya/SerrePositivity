module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanLeftHomInterval
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedLeftIntervalComparison

/-!
概要：標準頂点上の元の左区間族を F1 の元の反転 Kan 合成輸送の区間へ戻す。
方針：宇宙持ち上げと反転の交換同型だけで係数を揃える。
規約：元の実区間と指定された係数交換同型を保持する。
使われ方：元の反転精密化の作用を F1 の全係数 pointed 輸送へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の左区間族は係数の交換同型の後で F1 の実反転 Kan 区間族に一致する。 -/
lemma coherentKanLeftHomInterval_reverse (K L : KanObject.{u}) :
    (uliftOppositeIso (SimplicialCategory.sHom K L)).inv ≫
        coherentKanLeftHomInterval K L =
      intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
        (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) := by
  simpa only [coherentKanLeftHomInterval, Category.assoc] using
    (pointedReverseKanHomIntervalMap_eq_left K L).symm

end SerrePositivity.InfinityCategories.F2
