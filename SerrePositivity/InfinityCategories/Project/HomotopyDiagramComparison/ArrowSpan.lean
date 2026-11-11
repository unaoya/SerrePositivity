module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Functor.Const

/-!
# 指定する両脚を持つ三本矢の圏

概要：Dwyer–Kan の特殊な hammock の共通比較に使う三本矢の圏を構成する。
方針：両脚の射の類を入力し、二つの可換正方形と固定端点への整合を射にする。
規約：元の圏の射と合成を保持し、弱同値の条件は後続で証明する。
使われ方：trivial fibration と trivial cofibration を両脚に持つ frame 比較。
-/

@[expose] public section

universe u v

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

open CategoryTheory

variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C) (X Y : C)

/-- 概要：固定した端点を持つ三本矢の対象（Dwyer–Kan §7）。
方針：X ← U → V ← Y の両脚の射の類を明示する。
規約：中間射には射の類の条件を付けない。
使われ方：frame と hammock の共通比較圏。 -/
structure Object where
  left : C
  right : C
  leftMap : left ⟶ X
  middle : left ⟶ right
  rightMap : Y ⟶ right
  left_mem : L leftMap
  right_mem : R rightMap

variable {L R X Y}

/-- 概要：三本矢の間の元の二つの可換射（Dwyer–Kan §7）。
方針：固定端点と中間射との三つの整合式を保持する。
規約：縦射の弱同値性は両脚から導く。
使われ方：特殊な hammock の幅一の射。 -/
structure Hom (S T : Object L R X Y) where
  left : S.left ⟶ T.left
  right : S.right ⟶ T.right
  left_w : left ≫ T.leftMap = S.leftMap
  middle_w : S.middle ≫ right = left ≫ T.middle
  right_w : S.rightMap ≫ right = T.rightMap

/-- 概要：三本矢の射の等式は元の二つの射で決まる（Dwyer–Kan）。
方針：整合条件は命題であることを使う。
規約：元の射を同型類へ落とさない。
使われ方：圏の全法則の照合。 -/
@[ext] lemma hom_ext {S T : Object L R X Y} (f g : Hom S T)
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  cases hl
  cases hr
  rfl

/-- 概要：三本矢と可換縦射は元の合成による圏をなす（Dwyer–Kan）。
方針：成分ごとに合成し、各正方形の整合式を合成する。
規約：固定した両端点を保持する。
使われ方：特殊な hammock の nerve。 -/
instance objectCategory : Category.{v} (Object L R X Y) where
  Hom := Hom
  id S :=
    { left := 𝟙 S.left
      right := 𝟙 S.right
      left_w := Category.id_comp _
      middle_w := by simp
      right_w := Category.comp_id _ }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right
      left_w := by rw [Category.assoc, g.left_w, f.left_w]
      middle_w := by rw [← Category.assoc, f.middle_w, Category.assoc,
        g.middle_w, ← Category.assoc]
      right_w := by rw [← Category.assoc, f.right_w, g.right_w] }
  id_comp f := hom_ext _ _ (Category.id_comp _) (Category.id_comp _)
  comp_id f := hom_ext _ _ (Category.comp_id _) (Category.comp_id _)
  assoc f g h := hom_ext _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)

variable (L R X Y)

/-- 概要：三本矢の左の中間対象への射影（Dwyer–Kan）。
方針：元の対象と縦射の左成分を使う。
規約：元の合成を保持する。
使われ方：左脚の自然な比較。 -/
def leftProjection : Object L R X Y ⥤ C where
  obj S := S.left
  map f := f.left

/-- 概要：三本矢の右の中間対象への射影（Dwyer–Kan）。
方針：元の対象と縦射の右成分を使う。
規約：元の合成を保持する。
使われ方：右脚の自然な比較。 -/
def rightProjection : Object L R X Y ⥤ C where
  obj S := S.right
  map f := f.right

/-- 概要：元の左脚は X への自然な比較（Dwyer–Kan）。
方針：固定端点への可換条件を使う。
規約：各成分は同じ左脚。
使われ方：frame の augmentation との接続。 -/
def leftAugmentation : leftProjection L R X Y ⟶ (Functor.const _).obj X where
  app S := S.leftMap
  naturality S T f := by
    change f.left ≫ T.leftMap = S.leftMap ≫ 𝟙 X
    rw [Category.comp_id]
    exact f.left_w

/-- 概要：元の右脚は Y からの自然な比較（Dwyer–Kan）。
方針：固定端点からの可換条件を使う。
規約：各成分は同じ右脚。
使われ方：fibrant 置換の coaugmentation との接続。 -/
def rightAugmentation : (Functor.const _).obj Y ⟶ rightProjection L R X Y where
  app S := S.rightMap
  naturality S T f := by
    change 𝟙 Y ≫ T.rightMap = S.rightMap ≫ f.right
    rw [Category.id_comp]
    exact f.right_w.symm

/-- 概要：元の中間射は両射影の間の自然変換（Dwyer–Kan）。
方針：中間の可換正方形を使う。
規約：元の三本矢の中間射を保持する。
使われ方：共通比較の全次数の射。 -/
def middleTransformation : leftProjection L R X Y ⟶ rightProjection L R X Y where
  app S := S.middle
  naturality _ _ f := f.middle_w.symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
