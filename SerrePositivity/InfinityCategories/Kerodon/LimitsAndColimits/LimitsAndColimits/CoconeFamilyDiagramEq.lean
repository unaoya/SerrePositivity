module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily

/-!
概要：等しい図式の間で余錐と固定図式上の余錐の同型を輸送する。
方針：余錐の射は保ち、図式の固定条件だけを等式で移す。
規約：図式の表示変更は余錐全体の raw な値を変えない。
使われ方：底で等しい図式の標準余錐と普遍 comma 余錐を同じ族で比較する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：等しい図式上の余錐へ同じ射のまま輸送する。
方針：左包含への制限の等式を合成する。
規約：余錐の射の値は変えない。
使われ方：底の図式の結合順序を揃える。 -/
def coconeOfDiagramEq {K D : SSet.{u}} {p q : K ⟶ D}
    (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q := ⟨c.val, c.property.trans h⟩

/-- 概要：等しい図式上への輸送は固定図式の余錐の同型も移す。
方針：図式の等式を消去し、同じ余錐の族として読む。
規約：同型の両端を同じ輸送で移す。
使われ方：底の標準余錐の比較同型の型を元の図式の像に合わせる。 -/
def coconeFamilyIsoOfDiagramEq {K D : SSet.{u}} {p q : K ⟶ D}
    (h : p = q) {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p d)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv q (coconeOfDiagramEq h c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv q (coconeOfDiagramEq h d)) := by
  subst q
  exact e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
