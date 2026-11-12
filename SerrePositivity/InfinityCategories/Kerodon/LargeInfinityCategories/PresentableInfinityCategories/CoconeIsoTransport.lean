module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialRestrictionBaseEvaluation

/-!
概要：全余錐の値を保つ図式表示の変更に、全 coslice 内の頂点同型を移す。
方針：図式の等号を除き、全部分型の値の等号から同じ余錐を回収する。
規約：余錐の頂点や脚だけの比較には弱めない。
使われ方：compact comma の回収時の固定図式の正規化。

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

/-- 概要：全余錐値を保つ図式の等号移送は全 coslice 同型を保つ。
方針：同じ図式で全部分型の外延性を使う。
規約：全 join 射の値の等号を要求する。
使われ方：第一成分の全余錐同型の正規化。 -/
def coconeVertexIso_transport_values {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (h : F = G)
    {a b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋0⦌} {c d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder G) _⦋0⦌}
    (ha : a.val = c.val) (hb : b.val = d.val) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c d := by
  subst G
  have hac : a = c := Subtype.ext ha
  have hbd : b = d := Subtype.ext hb
  subst c
  subst d
  exact e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
