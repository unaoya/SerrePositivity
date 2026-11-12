module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSimplexFaces
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeSpecifiedEdgeExtension

/-!
概要：元の標準単体図式へ、その終点から出る指定辺を付け加える。
方針：既存単体を余錐と読み、余錐圏の標準輸送を次の標準単体へ移す。
規約：既存単体と指定辺を全射の厳密な等式で保持する。
使われ方：引き戻しの交互列の有限部分図式を再帰的に延長する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：正次元の標準単体を、その最終頂点を頂点とする余錐として読む。
方針：右端に零単体を join する表示を使う。
規約：元の全単体図式を保持する。
使われ方：次の指定辺への輸送の出発余錐。 -/
def simplexTerminalCocone {X : SSet.{u}} (n : ℕ) (f : (Δ[n + 1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ f) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ f, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl]⟩

/-- 概要：既存の全単体とその終点から出る指定辺を含む一つ大きい全単体。
方針：余錐圏の輸送辺の uncurry を標準単体の join 同型で読む。
規約：元の単体の次元は一以上。
使われ方：可算交互列の高次の整合を延長する。 -/
def simplexSpecifiedEdgeExtension {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) {y : X _⦋0⦌}
    (e : X.Edge (simplexTerminalCocone n f).vertex y) : (Δ[n + 2] : SSet.{u}) ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSpecifiedEdgeExtension (simplexTerminalCocone n f) e

/-- 概要：最後の頂点を除く面への制限は元の指定単体図式そのもの。
方針：join 表示で右端の辺の始点へ制限し、輸送の始点を回収する。
規約：全射の厳密な等式。
使われ方：有限段階から可算全図式を貼るための整合条件。 -/
lemma simplexSpecifiedEdgeExtension_front {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) {y : X _⦋0⦌}
    (e : X.Edge (simplexTerminalCocone n f).vertex y) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫
      simplexSpecifiedEdgeExtension n f e = f := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom).mp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
      (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).inv ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSpecifiedEdgeExtension (simplexTerminalCocone n f) e)) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.joinStdSimplexIso_rightEdge_zero, Category.assoc,
    Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSpecifiedEdgeExtension_zero]
  rfl

/-- 概要：延長単体の最後の辺は元の指定辺そのもの。
方針：右因子の全辺への制限と join 表示の逆関係を使う。
規約：一単体のホモトピー類に弱めない。
使われ方：交互列で選んだ比較辺を元のまま保持する。 -/
lemma simplexSpecifiedEdgeExtension_lastEdge {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (f : (Δ[n + 1] : SSet.{u}) ⟶ X) {y : X _⦋0⦌}
    (e : X.Edge (simplexTerminalCocone n f).vertex y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫
      simplexSpecifiedEdgeExtension n f e = SSet.yonedaEquiv.symm e.edge := by
  simp only [simplexSpecifiedEdgeExtension, Category.assoc, Iso.hom_inv_id_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSpecifiedEdgeExtension_inr _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
