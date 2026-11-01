module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFixedCut

/-!
# 同じ元の生成矢の表示による固定切断の移送

概要：生成矢の等式で固定切断を移し、元の接頭射・残りの異種等式を保持する。
方針：生成矢の等式で帰納する。
規約：元の射列とその端点は保持する。
使われ方：圧縮後の各行の切断を元の生成矢へ揃える。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord.FixedCut
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Quiver.Total C} {X Y : C} {p : Quiver.Path X Y}

def changeGenerator (h : a = b) (P : FixedCut W a p) : FixedCut W b p := h ▸ P

lemma changeGenerator_left (h : a = b) (P : FixedCut W a p) :
    HEq (changeGenerator W h P).left P.left := by cases h; rfl

lemma changeGenerator_right (h : a = b) (P : FixedCut W a p) :
    HEq (changeGenerator W h P).right P.right := by cases h; rfl

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord.FixedCut
