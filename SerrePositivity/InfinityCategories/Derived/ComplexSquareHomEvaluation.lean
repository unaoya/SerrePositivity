module
public import SerrePositivity.InfinityCategories.Derived.ComplexSquareEdgeEvaluation

/-! # 四角形比較の h の射の成分

概要：前合成・後合成の四角形の射を、端点を含む Arrow の等式で評価する。
方針：一次単体の成分計算を h の辺の類へ移す。
規約：source/target の表示の輸送も等式に含む。使われ方：D7 の比較射の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.ComplexSquareData
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {V A B C D E : Complex S}
variable (s : ComplexSquareData A B C D)

/-- 後合成の h の射の終点成分は q。 -/
lemma postcomposeHom_target_arrow (q : D ⟶ E) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSquareEdge q))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge q).toTruncated) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact s.postcomposeSquareEdge_target q

/-- 後合成の h の射の始点成分は恒等射。 -/
lemma postcomposeHom_source_arrow (q : D ⟶ E) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk (s.postcomposeSquareEdge q))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk
        ((spanSourceEvaluation (dgNerve S (Complex S))).app (Opposite.op ⦋0⦌)
          (functorVertex (pushoutSpan s.square))))) := by
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (dgNerve S (Complex S)))
          ((spanSourceEvaluation (dgNerve S (Complex S))).app (Opposite.op ⦋0⦌)
            (functorVertex (pushoutSpan s.square))))) :=
      SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
        ((s.postcomposeSquareEdge_source q).trans (pinchedConstant_one _))
    _ = _ := congrArg Arrow.mk (SSet.Truncated.HomotopyCategory.homMk_id _)

/-- 前合成の h の射の始点成分は p。 -/
lemma precomposeHom_source_arrow (p : V ⟶ A) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (SSet.Truncated.HomotopyCategory.homMk (s.precomposeSquareEdge p))) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge p).toTruncated) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact s.precomposeSquareEdge_source p

/-- 前合成の h の射の終点成分は恒等射。 -/
lemma precomposeHom_target_arrow (p : V ⟶ A) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (SSet.Truncated.HomotopyCategory.homMk (s.precomposeSquareEdge p))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk
        ((pullbackCospan s.square).app (Opposite.op ⦋0⦌) cospanTargetVertex))) := by
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (dgNerve S (Complex S)))
          ((pullbackCospan s.square).app (Opposite.op ⦋0⦌) cospanTargetVertex))) :=
      SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
        ((s.precomposeSquareEdge_target p).trans (pinchedConstant_one _))
    _ = _ := congrArg Arrow.mk (SSet.Truncated.HomotopyCategory.homMk_id _)

end SerrePositivity.InfinityCategories.ComplexSquareData
