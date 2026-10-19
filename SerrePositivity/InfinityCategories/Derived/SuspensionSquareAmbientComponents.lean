module
public import SerrePositivity.InfinityCategories.Derived.CofiberSquareComparisonData
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareHomEvaluation
public import SerrePositivity.InfinityCategories.Stable.ArrowIdentityComposition

/-! # 周囲の suspension 四角形比較の始点・終点成分

概要：前合成・後合成を合成した四角形比較は始点で a、終点で標準 cone 写像に一致する。
方針：各因子の端点成分を Arrow として計算し、恒等成分と中央四角形の輸送を打ち消す。
規約：全複体の dg nerve の h での等式。使われ方：D7 の Semifree への成分の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 周囲の suspension 四角形比較の始点成分は元の鎖写像。 -/
lemma suspensionComplexSquareHom_source_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (suspensionComplexSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge a).toTruncated) := by
  exact (suspensionComplexSquareData X).comparisonHom_source_arrow
    (suspensionComplexSquareData Y) a (semifreeSuspensionComplexMap a)
    (suspensionComplexSquareData_middle a)

/-- 周囲の suspension 四角形比較の終点成分は標準 cone 写像。 -/
lemma suspensionComplexSquareHom_target_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (suspensionComplexSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (complexEdge (semifreeSuspensionComplexMap a)).toTruncated) := by
  exact (suspensionComplexSquareData X).comparisonHom_target_arrow
    (suspensionComplexSquareData Y) a (semifreeSuspensionComplexMap a)
    (suspensionComplexSquareData_middle a)

end SerrePositivity.InfinityCategories
