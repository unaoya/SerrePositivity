module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorTriangleTwoFaces
/-! # 関手辺から実ホモトピーを経た同じ辺の回収

概要：関手辺を実ホモトピーへ戻しても、その辺の代表を厳密に回収する。
方針：Yoneda と curry・uncurry の逆則を使う。
規約：辺の類だけの一致へ弱めず、元一単体そのものを保持する。
使われ方：実六片の単位辺を、その全正方形を持つ閉路として扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
lemma dgGluingFunctorEdge_homotopy_recovery {K Z : SSet.{u}} {f g : K ⟶ Z}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e) = e := by
  apply Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = e.edge
  rw [curry_uncurry]
  exact (SSet.yonedaEquiv (X := (ihom K).obj Z)).apply_symm_apply
    (show ((ihom K).obj Z) _⦋1⦌ from e.edge)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
