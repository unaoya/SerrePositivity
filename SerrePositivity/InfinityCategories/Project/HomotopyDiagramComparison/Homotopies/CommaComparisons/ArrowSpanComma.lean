module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.ArrowSpan
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Equivalence

/-!
# 両脚の slice と元の Hom による三本矢の全図式の表示

概要：Low 命題 3.7 の三本矢の圏を両脚の指定射の slice の comma 圏で表示する。
方針：元の三射と三つの可換条件を slice・coslice・中間射へ分ける。
規約：元の対象・射を保持し、モデル構造や弱同値は要求しない。
使われ方：分解の余終性を三本矢の全図式へ適用する際の二変数の表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma

open CategoryTheory

variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C) (X Y : C)

/-- 概要：指定する左脚の slice の元の始域への射影（Low 命題 3.7）。
方針：既存の指定射の slice の忘却を合成する。
規約：全ての可換三角形を含む。
使われ方：元の中間 Hom の反変な変数。 -/
abbrev leftSliceForget : L.Over ⊤ X ⥤ C :=
  MorphismProperty.Over.forget L ⊤ X ⋙ Over.forget X

/-- 概要：指定する右脚の coslice の元の終域への射影（Low 命題 3.7）。
方針：既存の指定射の coslice の忘却を合成する。
規約：元の右脚の方向は Y から中間対象へ向かう。
使われ方：元の中間 Hom の共変な変数。 -/
abbrev rightSliceForget : R.Under ⊤ Y ⥤ C :=
  MorphismProperty.Under.forget R ⊤ Y ⋙ Under.forget Y

/-- 概要：三本矢を元の両脚と中間 Hom の comma 対象へ送る（Low 命題 3.7）。
方針：同じ両脚を slice 対象にし、中間射を構造射にする。
規約：三つの可換条件をそのまま保持する。
使われ方：三本矢の全図式の二変数表示の順関手。 -/
def toComma : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y ⥤ Comma (leftSliceForget L X) (rightSliceForget R Y) where
  obj S :=
    { left := MorphismProperty.Over.mk ⊤ S.leftMap S.left_mem
      right := MorphismProperty.Under.mk ⊤ S.rightMap S.right_mem
      hom := S.middle }
  map f :=
    { left := MorphismProperty.Over.homMk f.left f.left_w
      right := MorphismProperty.Under.homMk f.right f.right_w
      w := f.middle_w.symm }
  map_id S := CommaMorphism.ext rfl rfl
  map_comp f g := CommaMorphism.ext rfl rfl

/-- 概要：両脚と中間 Hom の comma を元の三本矢へ戻す（Low 命題 3.7）。
方針：元の slice 対象の構造射と comma の可換式を取り出す。
規約：元の対象と三射を回収する。
使われ方：三本矢の全図式の二変数表示の逆関手。 -/
def fromComma : Comma (leftSliceForget L X) (rightSliceForget R Y) ⥤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y where
  obj S :=
    { left := S.left.left
      right := S.right.right
      leftMap := S.left.hom
      middle := S.hom
      rightMap := S.right.hom
      left_mem := S.left.prop
      right_mem := S.right.prop }
  map f :=
    { left := f.left.left
      right := f.right.right
      left_w := Over.w f.left.hom
      middle_w := f.w.symm
      right_w := Under.w f.right.hom }
  map_id _S := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ rfl rfl
  map_comp _f _g := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ rfl rfl

/-- 概要：三本矢の二変数表示を戻すと同じ元の三本矢（Low 命題 3.7）。
方針：元の対象と射の eta 則を使う。
規約：全対象・全射の厳密な関手の等式。
使われ方：表示の逆則。 -/
lemma toComma_fromComma : toComma L R X Y ⋙ fromComma L R X Y = 𝟭 _ := rfl

/-- 概要：両脚の slice の二変数表示は元の三本矢の圏と同値（Low 命題 3.7）。
方針：同じ両脚と中間射の順逆を恒等の成分で比較する。
規約：同値の順関手は元の三射を使う toComma。
使われ方：三本矢の全図式のホモトピー余極限の表示。 -/
def commaEquivalence : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y ≌
    Comma (leftSliceForget L X) (rightSliceForget R Y) :=
  CategoryTheory.Equivalence.mk (toComma L R X Y) (fromComma L R X Y)
    (NatIso.ofComponents (fun S => Iso.refl S))
    (NatIso.ofComponents (fun S =>
      Comma.isoMk (MorphismProperty.Over.isoMk (Iso.refl S.left.left)
        (Category.id_comp S.left.hom))
        (MorphismProperty.Under.isoMk (Iso.refl S.right.right)
          (Category.comp_id S.right.hom))
        ((Category.id_comp S.hom).trans (Category.comp_id S.hom).symm)) (by
      intro S T f
      apply CommaMorphism.ext
      · apply MorphismProperty.Over.Hom.ext
        change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
        simp
      · apply MorphismProperty.Under.Hom.ext
        change f.right.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right.right
        simp))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma
