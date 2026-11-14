module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarIdentity
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftIteration

/-!
# 相対bar比較spanのsectionが元のaugmentationのレトラクションを与える

## 概要
相対bar比較spanのsectionが元のaugmentationのレトラクションを与える。
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
[棚卸し m0531][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0531
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The natural comparison span through an identity-projection bar

The left map has an explicit pointwise section. The section is not claimed
to be natural in the base. Neither leg is assumed to be a weak equivalence.
-/

@[expose] public section
universe v uD vD uB vB
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev spanMiddle (_p : D ⥤ B) (F : D ⥤ SSet.{v}) : D ⥤ SSet.{max uD vD v vB} :=
  relative (𝟭 D) F ⋙ SSet.uliftFunctor.{vB, max uD vD v}

/-- The actual augmentation, with the two lift wrappers flattened naturally. -/
def spanLeft : spanMiddle p F ⟶ F ⋙ SSet.uliftFunctor.{max uD vD vB, v} :=
  Functor.whiskerRight (identityAugmentation F) SSet.uliftFunctor.{vB, max uD vD v} ≫
    (Functor.isoWhiskerLeft F (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.iterationIso.{v, max uD vD, vB})).hom

abbrev spanRight : spanMiddle p F ⟶ p ⋙ relative p F := unit p F

/-- A section at a fixed object, transported through the explicit flattening isomorphism. -/
def spanSection (d : D) : (SSet.uliftFunctor.{max uD vD vB, v}).obj (F.obj d) ⟶
    (spanMiddle p F).obj d :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.iterationIso.{v, max uD vD, vB}.app (F.obj d)).inv ≫
    SSet.uliftFunctor.{vB, max uD vD v}.map (identitySection F d)

/-- 相対bar比較spanのsectionが元のaugmentationのレトラクションを与える。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
lemma spanSection_retract (d : D) :
    spanSection p F d ≫ (spanLeft p F).app d = 𝟙 _ := by
  let U := SSet.uliftFunctor.{vB, max uD vD v}
  let e := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.iterationIso.{v, max uD vD, vB}.app (F.obj d)
  change (e.inv ≫ U.map (identitySection F d)) ≫
    (U.map ((identityAugmentation F).app d) ≫ e.hom) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (U.map (identitySection F d)), ← U.map_comp,
    identitySection_retract, U.map_id, Category.id_comp, e.inv_hom_id]

end SerrePositivity.SimplicialModel.BarConstruction
