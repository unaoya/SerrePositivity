module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeCriterion
public import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport

/-!
概要：余錐全体の関手同型による標準 U 余極限の輸送。
方針：全余錐の相対制限の始点境界充填を可逆な頂点に沿って移す。
規約：固定図式が異なる余錐でも、余錐全体の同型で比較する。
使われ方：comma の比較円柱を元の Kan 条件へ戻す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐全体の関手同型は inner fibration 上の標準相対余極限を保つ。
方針：標準条件を全余錐の相対始点境界充填に移し、同型で輸送して戻す。
規約：U は inner fibration、同型は余錐の raw な射全体を比較する。
使われ方：局所比較円柱による相対 Kan 条件の移送。 -/
lemma kanIsRelativeColimitCone_of_functorIso {A D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {p q : A ⟶ D} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U d := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_of_lifting U d
  exact _root_.SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryLifting.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction A U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_of_isRelativeColimitCone U c hc) e

/-- 概要：同型な全余錐の標準 U 余極限性は同値。
方針：関手同型とその逆に保存を適用する。
規約：図式と余錐の頂点を別々に選び直さない。
使われ方：元の局所余錐と comma fiber の制限との同値判定。 -/
lemma kanIsRelativeColimitCone_iff_of_functorIso {A D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {p q : A ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U d :=
  ⟨fun h ↦ kanIsRelativeColimitCone_of_functorIso U h e,
    fun h ↦ kanIsRelativeColimitCone_of_functorIso U h e.symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.1.5" (partial := component) "仮定：内ファイブレーションと関手準圏で同値な二つの余錐（HTT の (3) と一致）。結論：二つの余錐の相対余極限性が同値（結論 (3) が一致。他の安定性はこの宣言に含まれない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso
attribute [cite HTT "4.3.1.9" (partial := stronger-hyp) "仮定：点ごとに余デカルトで頂点の底の像が退化する余錐間の変換（Lean が強い：変換が関手準圏の同型を与える場合に適用）。結論：同じ二余錐の相対余極限性が同値（一致する場合）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_iff_of_functorIso
