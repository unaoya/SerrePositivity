module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPair
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedValueRightInverse

/-!
概要：既存の pointed 値比較の輸送自然性を、動く Kan 射の全族へ拡張する。
方針：同じ coherent 合成四角形の比較を、既存の単位・余単位で共役する。
規約：値比較の選択を保持。使われ方：元の二三角形の値の全パラメータ比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の値比較は、同じパラメータで動く点と Kan 射の評価を区間輸送へ比較する。 -/
def pointedValueFamilyTransportIso {K L : KanObject.{u}} {P : SSet.{u + 1}}
    (x : P ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K))
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) :
    FunctorIso
      (pointedRightFamilyEvaluation
        (x ≫ (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom) y)
      (diagonalFiberTransport pointedSpaceProjection x (y ≫ coherentKanRightHomInterval K L) ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom) := by
  let a := (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom
  let b := (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom
  let v := pointedRightFamilyEvaluation (x ≫ a) y
  have e := (pointedRightFamilyTransportIso (x ≫ a) y).postcomp b
  have hl : FunctorIso ((v ≫ pointedRightFiberComparison L) ≫ b) v := by
    simpa only [pointedValueRightComparison_standard, Category.assoc, Category.comp_id] using
      (pointedValueRightComparison_counitIso (spaceInfinityVertex L)).precomp v
  have hs : FunctorIso ((x ≫ a) ≫ pointedRightFiberComparison K) x := by
    simpa only [pointedValueRightComparison_standard, Category.assoc, Category.comp_id] using
      (pointedValueRightComparison_unitIso (spaceInfinityVertex K)).precomp x
  let T := parametrizedFiberTransportFamily pointedSpaceProjection
    (spaceInfinityVertex K) (spaceInfinityVertex L)
  have hr := ((functorIsoLiftRight hs (y ≫ coherentKanRightHomInterval K L)).postcomp
    T.endpoint).postcomp b
  exact hl.symm ≪≫ e ≪≫ hr

end SerrePositivity.InfinityCategories.F2
