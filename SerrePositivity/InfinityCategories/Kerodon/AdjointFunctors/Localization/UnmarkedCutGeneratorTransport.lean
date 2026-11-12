module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift

/-!
# 同じ Total 生成矢の表示の移送

概要：生成矢の等式に沿って固定切断とその圏を移し、元の全行・全縦射を保つ。
方針：生成矢の等式で帰納し、固定切断の一意性を使う。
規約：元の列・全縦射は変えず、表示だけを移す。
使われ方：単体作用素で基準行が変わった場合の厳密な整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
  (X Y : Paths C) (i : Fin w.length)

def changeGenerator {a b : Quiver.Total C} (h : a = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i b where
  obj P := ⟨P.row, h ▸ P.cut⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport (changeGenerator)


lemma changeGenerator_refl (a : Quiver.Total C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i (rfl : a = a) = 𝟭 _ := by
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport (changeGenerator_refl)


lemma changeGenerator_forget {a b : Quiver.Total C} (h : a = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.forget W w X Y i b = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.forget W w X Y i a := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport (changeGenerator_forget)


lemma changeGenerator_comp {a b c : Quiver.Total C} (h : a = b) (k : b = c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i (h.trans k) := by
  cases h
  cases k
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport (changeGenerator_comp)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport
