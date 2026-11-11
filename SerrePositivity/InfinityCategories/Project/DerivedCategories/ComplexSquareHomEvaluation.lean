module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareEdgeEvaluation

/-! # 四角形比較の h の射の成分

概要：前合成・後合成の四角形の射を、端点を含む Arrow の等式で評価する。
方針：一次単体の成分計算を h の辺の類へ移す。
規約：source/target の表示の輸送も等式に含む。使われ方：D7 の比較射の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {V A B C D E : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D)

/-- 後合成の h の射の終点成分は q。 -/
lemma postcomposeHom_target_arrow (q : D ⟶ E) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
      (SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSquareEdge q))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge q).toTruncated) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact s.postcomposeSquareEdge_target q

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (postcomposeHom_target_arrow)


/-- 後合成の h の射の始点成分は恒等射。 -/
lemma postcomposeHom_source_arrow (q : D ⟶ E) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSquareEdge q))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square))))) := by
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))
          ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square))))) :=
      SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
        ((s.postcomposeSquareEdge_source q).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _))
    _ = _ := congrArg Arrow.mk (SSet.Truncated.HomotopyCategory.homMk_id _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (postcomposeHom_source_arrow)


/-- 前合成の h の射の始点成分は p。 -/
lemma precomposeHom_source_arrow (p : V ⟶ A) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk (s.precomposeSquareEdge p))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge p).toTruncated) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact s.precomposeSquareEdge_source p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeHom_source_arrow)


/-- 前合成の h の射の終点成分は恒等射。 -/
lemma precomposeHom_target_arrow (p : V ⟶ A) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
      (SSet.Truncated.HomotopyCategory.homMk (s.precomposeSquareEdge p))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square).app (Opposite.op ⦋0⦌) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanTargetVertex))) := by
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square).app (Opposite.op ⦋0⦌) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanTargetVertex))) :=
      SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
        ((s.precomposeSquareEdge_target p).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _))
    _ = _ := congrArg Arrow.mk (SSet.Truncated.HomotopyCategory.homMk_id _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeHom_target_arrow)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
