module
public import SerrePositivity.KST.Fibration.ContractibleRestrictionComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：所有する固定部分比較の、指定部分上の成分を実恒等辺として回収する。
方針：固定制限の一次単体を同じ指定点で評価し、評価と前合成の自然性を使う。
規約：実辺の等号を保持し、可逆性やホモトピー類だけへ弱めない。
使われ方：K-6 c4 の全長 Hom 比較の指定境界の単位条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 概要：固定部分比較の指定部分上の成分は同じ元の点の実恒等辺。
方針：元の固定制限式を指定点で評価する。
規約：所有する比較構造体の射影を使い、新しい比較を選ばない。
使われ方：元の直接端上の全比較から指定単位二単体を構成する。 -/
theorem FixedRestrictionFunctorEdge.component_at
    {A B Z : SSet.{u}} [Quasicategory Z] {i : A ⟶ B} {f g : B ⟶ Z}
    (E : FixedRestrictionFunctorEdge i f g) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge E.edge)
      (i.app (Opposite.op ⦋0⦌) a)).edge =
      (Truncated.Edge.id (X := (truncation 2).obj Z)
        (f.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) a))).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge]
  have hn := congrArg (fun h => h.app (Opposite.op ⦋1⦌) E.edge.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre (X := Z) i a)
  have hr := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a).app (Opposite.op ⦋1⦌)) E.restriction
  have hi := congrArg Truncated.Edge.edge
    (Truncated.Edge.map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f))
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a).app (Opposite.op ⦋1⦌)
    (Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f))).edge =
    (Truncated.Edge.id (X := (truncation 2).obj Z)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f)))).edge at hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hi
  exact hn.symm.trans (hr.trans hi)

end SerrePositivity.KST.Fibration
