module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberSquareComparisonData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareHomEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition

/-! # 周囲の suspension 四角形比較の始点・終点成分

概要：前合成・後合成を合成した四角形比較は始点で a、終点で標準 cone 写像に一致する。
方針：各因子の端点成分を Arrow として計算し、恒等成分と中央四角形の輸送を打ち消す。
規約：全複体の dg nerve の h での等式。使われ方：D7 の Semifree への成分の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 周囲の suspension 四角形比較の始点成分は元の鎖写像。 -/
lemma suspensionComplexSquareHom_source_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge a).toTruncated) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData X).comparisonHom_source_arrow
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData Y) a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData_middle a)

/-- 周囲の suspension 四角形比較の終点成分は標準 cone 写像。 -/
lemma suspensionComplexSquareHom_target_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHom a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)).toTruncated) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData X).comparisonHom_target_arrow
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData Y) a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData_middle a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
