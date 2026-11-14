module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftEndpoint

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：可縮な延長空間の実際の辺の評価を、同じ二頂点の指定比較同型の評価へ移す。
方針：始域のホモトピー圏での一意性を使い、評価関手で同じ類を写す。
規約：標的の辺の一意性は仮定しない。使われ方：指定修正辺と根辺の正準比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 可縮な始域の同じ二頂点の実際の辺は、評価後も指定比較と同じ類を持つ。 -/
lemma contractibleEdgeEvaluation_hom {X Y : SSet.{u}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X)
    (F : X ⟶ Y) {x y : X _⦋0⦌} (s : X.Edge x y) :
    SSet.Truncated.HomotopyCategory.homMk (s.map F).toTruncated =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F).hom := by
  have := hX.kanComplex
  have hs : SSet.Truncated.HomotopyCategory.homMk s.toTruncated = (hX.vertexIso x y).hom :=
    (hX.isTerminalVertex y).isTerminalHo.hom_ext _ _
  exact congrArg (hoFunctor.map F).toFunctor.map hs

/-- 実際の辺の既知の評価は、正準比較同型の評価の同じ射でもある。 -/
lemma contractibleEdgeEvaluation_hom_arrow {X Y : SSet.{u}} (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X)
    (F : X ⟶ Y) {x y : X _⦋0⦌} (s : X.Edge x y)
    {a b : hoFunctor.obj Y} (g : a ⟶ b)
    (hg : Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (s.map F).toTruncated) = Arrow.mk g) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hX.vertexIso x y) F).hom = Arrow.mk g :=
  (congrArg Arrow.mk (contractibleEdgeEvaluation_hom hX F s)).symm.trans hg

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
