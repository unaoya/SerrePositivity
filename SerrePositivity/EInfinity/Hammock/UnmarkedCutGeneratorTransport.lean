module

public import SerrePositivity.EInfinity.Hammock.UnmarkedColumnLift

/-!
# 同じ Total 生成矢の表示の移送

概要：生成矢の等式に沿って固定切断とその圏を移し、元の全行・全縦射を保つ。
方針：生成矢の等式で帰納し、固定切断の一意性を使う。
規約：元の列・全縦射は変えず、表示だけを移す。
使われ方：単体作用素で基準行が変わった場合の厳密な整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : Word)
  (X Y : Paths C) (i : Fin w.length)

def changeGenerator {a b : Quiver.Total C} (h : a = b) :
    ColumnCut W w X Y i a ⥤ ColumnCut W w X Y i b where
  obj P := ⟨P.row, h ▸ P.cut⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

lemma changeGenerator_refl (a : Quiver.Total C) :
    changeGenerator W w X Y i (rfl : a = a) = 𝟭 _ := by
  rfl

lemma changeGenerator_forget {a b : Quiver.Total C} (h : a = b) :
    changeGenerator W w X Y i h ⋙ forget W w X Y i b = forget W w X Y i a := rfl

lemma changeGenerator_comp {a b c : Quiver.Total C} (h : a = b) (k : b = c) :
    changeGenerator W w X Y i h ⋙ changeGenerator W w X Y i k =
      changeGenerator W w X Y i (h.trans k) := by
  cases h
  cases k
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
