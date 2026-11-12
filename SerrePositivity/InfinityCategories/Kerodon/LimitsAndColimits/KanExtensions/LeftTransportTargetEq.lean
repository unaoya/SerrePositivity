module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomotopyInvariant

/-!
概要：局所余錐の輸送の標的の表示を等式で変える。
方針：標的の等式と同じ代表のホモトピーの外延性で輸送する。
規約：局所余錐全体の raw な値は変えない。
使われ方：普遍 comma 候補を元の関手と同一視して固定図式上で比較する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標的を等しい図式へ移しても局所輸送は同じ円柱で表せる。
方針：等式を消去し、同じ raw なホモトピーの外延性を使う。
規約：指定単位の代表は等しいことを要求する。
使われ方：候補の標的を元の関手へ厳密に読み替える。 -/
def kanLeftTransportTargetEq {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F G : C ⟶ D} (hF : F = G)
    {α : SSet.Homotopy F₀ (δ ≫ F)} {β : SSet.Homotopy F₀ (δ ≫ G)}
    (h : α.h = β.h) {c : C _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F α c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ G β c := by
  subst G
  have he : α = β := SSet.RelativeMorphism.Homotopy.ext h
  subst β
  exact t

/-- 概要：標的の表示を変えた局所輸送の余錐は元の余錐に等しい。
方針：等式の消去とホモトピーの外延性で同じ輸送へ戻す。
規約：元の局所図式は固定されている。
使われ方：固定図式上の余錐の族の同型を表示変更後から戻す。 -/
lemma kanLeftTransportTargetEq_cocone {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F G : C ⟶ D} (hF : F = G)
    {α : SSet.Homotopy F₀ (δ ≫ F)} {β : SSet.Homotopy F₀ (δ ≫ G)}
    (h : α.h = β.h) {c : C _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F α c) :
    (kanLeftTransportTargetEq hF h t).cocone = t.cocone := by
  subst G
  have he : α = β := SSet.RelativeMorphism.Homotopy.ext h
  subst β
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
