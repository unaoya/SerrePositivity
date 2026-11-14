module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpan
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.UniverseLift.UniverseLiftHomotopy

/-!
# 相対bar比較spanの左脚を収縮する実ホモトピーを構成する

## 概要
相対bar比較spanの左脚を収縮する実ホモトピーを構成する。
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
[棚卸し m0532][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0532
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual left leg of the natural comparison span is a simplicial homotopy retract
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

lemma spanLeft_section_factor (d : D) :
    (spanLeft p F).app d ≫ spanSection p F d =
      SSet.uliftFunctor.{vB, max uD vD v}.map
        ((identityAugmentation F).app d ≫ identitySection F d) := by
  let U := SSet.uliftFunctor.{vB, max uD vD v}
  let e := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.iterationIso.{v, max uD vD, vB}.app (F.obj d)
  change (U.map ((identityAugmentation F).app d) ≫ e.hom) ≫
    (e.inv ≫ U.map (identitySection F d)) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← U.map_comp]

/- 旧宣言の技術注記：
The full diagonal contraction survives the actual lift and wrapper-flattening maps.
-/
/-- 相対bar比較spanの左脚を収縮する実ホモトピーを構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def spanLeftHomotopy (d : D) : SSet.Homotopy (𝟙 ((spanMiddle p F).obj d))
    ((spanLeft p F).app d ≫ spanSection p F d) := by
  have H := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.homotopy.{vB} (identityDiagonalHomotopy F d)
  change SSet.Homotopy
    (SSet.uliftFunctor.{vB, max uD vD v}.map (𝟙 ((relative (𝟭 D) F).obj d)))
    (SSet.uliftFunctor.{vB, max uD vD v}.map
      ((identityAugmentation F).app d ≫ identitySection F d)) at H
  rw [CategoryTheory.Functor.map_id, ← spanLeft_section_factor p F d] at H
  exact H

end SerrePositivity.SimplicialModel.BarConstruction
