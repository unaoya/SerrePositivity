module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAugmentation

/-!
# 恒等射影のbarを介して相対barへの自然な単位を構成する

## 概要
恒等射影のbarを介して相対barへの自然な単位を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0533][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0533
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A natural bar unit through the identity-projection bar

The source is lifted only to match the base Hom universe. No model
structure or weak equivalence of this unit is assumed.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev identityAugmentation : relative (𝟭 D) F ⟶
    F ⋙ SSet.uliftFunctor.{max uD vD, v} :=
  relativeAugmentation (𝟭 D) F (𝟙 F)

/-- The actual postcomposition of each comma chain gives the comparison component. -/
def unitComponent (d : D) :
    SSet.uliftFunctor.{vB, max uD vD v}.obj ((relative (𝟭 D) F).obj d) ⟶
      (relative p F).obj (p.obj d) where
  app n := ↾fun x => x.down ⋙ CostructuredArrow.post
    (Functor.Elements.π (F.flip.obj n)) p d
  naturality {_ _} _ := rfl

/- 旧宣言の技術注記：
Postcomposing all actual comma arrows is natural on all presentation maps.
-/
/-- 恒等射影のbarを介して相対barへの自然な単位を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def unit : relative (𝟭 D) F ⋙ SSet.uliftFunctor.{vB, max uD vD v} ⟶ p ⋙ relative p F where
  app d := unitComponent p F d
  naturality {d e} f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change (x.down ⋙ CostructuredArrow.map f) ⋙
      CostructuredArrow.post (Functor.Elements.π (F.flip.obj n)) p e =
      (x.down ⋙ CostructuredArrow.post (Functor.Elements.π (F.flip.obj n)) p d) ⋙
        CostructuredArrow.map (p.map f)
    refine CategoryTheory.Functor.ext (fun i => congrArg
      (CostructuredArrow.mk (S := elementProjection p F n) (Y := (x.down.obj i).left))
      (p.map_comp (x.down.obj i).hom f)) ?_
    intro i j h
    apply CostructuredArrow.hom_ext
    apply Functor.Elements.hom_ext
    simp

end SerrePositivity.SimplicialModel.BarConstruction
