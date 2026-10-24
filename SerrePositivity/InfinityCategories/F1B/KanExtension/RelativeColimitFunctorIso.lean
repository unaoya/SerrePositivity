module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeCriterion
public import SerrePositivity.InfinityCategories.Stable.InitialBoundaryTransport

/-!
概要：余錐全体の関手同型による標準 U 余極限の輸送。
方針：全余錐の相対制限の始点境界充填を可逆な頂点に沿って移す。
規約：固定図式が異なる余錐でも、余錐全体の同型で比較する。
使われ方：comma の比較円柱を元の Kan 条件へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：余錐全体の関手同型は inner fibration 上の標準相対余極限を保つ。
方針：標準条件を全余錐の相対始点境界充填に移し、同型で輸送して戻す。
規約：U は inner fibration、同型は余錐の raw な射全体を比較する。
使われ方：局所比較円柱による相対 Kan 条件の移送。 -/
lemma kanIsRelativeColimitCone_of_functorIso {A D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {p q : A ⟶ D} {c : JoinCocone p} {d : JoinCocone q}
    (hc : IsRelativeColimitCone U c) (e : FunctorIso c.val d.val) :
    IsRelativeColimitCone U d := by
  apply kanIsRelativeColimitCone_of_lifting U d
  exact InitialBoundaryLifting.of_vertexIso (kanRelativeCoconeRestriction A U)
    (kanRelativeCoconeLifting_of_isRelativeColimitCone U c hc) e

/-- 概要：同型な全余錐の標準 U 余極限性は同値。
方針：関手同型とその逆に保存を適用する。
規約：図式と余錐の頂点を別々に選び直さない。
使われ方：元の局所余錐と comma fiber の制限との同値判定。 -/
lemma kanIsRelativeColimitCone_iff_of_functorIso {A D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {p q : A ⟶ D} (c : JoinCocone p) (d : JoinCocone q) (e : FunctorIso c.val d.val) :
    IsRelativeColimitCone U c ↔ IsRelativeColimitCone U d :=
  ⟨fun h ↦ kanIsRelativeColimitCone_of_functorIso U h e,
    fun h ↦ kanIsRelativeColimitCone_of_functorIso U h e.symm⟩

end SerrePositivity.InfinityCategories.F1B
