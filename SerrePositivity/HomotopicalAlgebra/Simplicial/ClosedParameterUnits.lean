module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BinaryIntervalEndpoints

/-!
# 共有パラメータ上の内部Homの左単位則が実写像の等式として成り立つ

## 概要
共有パラメータ上の内部Homの左単位則が実写像の等式として成り立つ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0362][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0362
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Exact internal-Hom units with an arbitrary shared parameter

These unit equations apply to whole interval maps. In particular fixing
a binary interval at its final internal identity gives the original
other interval, with no replacement or Kan filling.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ClosedParameterUnits
variable {T X Y : SSet.{v}}

/-- 共有パラメータ上の内部Homの左単位則が実写像の等式として成り立つ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
lemma identity_comp (f : T ⟶ (ihom X).obj Y) :
    lift (toUnit T ≫ MonoidalClosed.id X) f ≫ MonoidalClosed.comp X X Y = f := by
  apply uncurry_injective
  rw [ClosedHomotopyComposition.uncurry_composition,
    ← ClosedParameterComposition.curry_fst X T, uncurry_curry]
  exact ParameterComposition.id_comp _

lemma comp_identity (f : T ⟶ (ihom X).obj Y) :
    lift f (toUnit T ≫ MonoidalClosed.id Y) ≫ MonoidalClosed.comp X Y Y = f := by
  apply uncurry_injective
  rw [ClosedHomotopyComposition.uncurry_composition,
    ← ClosedParameterComposition.curry_fst Y T, uncurry_curry]
  exact ParameterComposition.comp_id _

lemma firstFixed_interval {f₀ f₁ : T ⟶ (ihom X).obj Y} (F : SSet.Homotopy f₀ f₁) :
    (BinaryIntervalTriangles.firstFixed F (MonoidalClosed.comp X X Y)
      (f₁ := toUnit T ≫ MonoidalClosed.id X)).h = F.h := by
  change lift (fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id X))
    F.h ≫ MonoidalClosed.comp X X Y = F.h
  have h : fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id X) =
      toUnit (T ⊗ HomotopyBinarySquare.interval) ≫ MonoidalClosed.id X := by
    rw [← Category.assoc, comp_toUnit]
  rw [h, identity_comp]

lemma secondFixed_interval {f₀ f₁ : T ⟶ (ihom X).obj Y} (F : SSet.Homotopy f₀ f₁) :
    (BinaryIntervalTriangles.secondFixed F (MonoidalClosed.comp X Y Y)
      (g₁ := toUnit T ≫ MonoidalClosed.id Y)).h = F.h := by
  change lift F.h
    (fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id Y)) ≫
      MonoidalClosed.comp X Y Y = F.h
  have h : fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id Y) =
      toUnit (T ⊗ HomotopyBinarySquare.interval) ≫ MonoidalClosed.id Y := by
    rw [← Category.assoc, comp_toUnit]
  rw [h, comp_identity]

end SerrePositivity.SimplicialModel.ClosedParameterUnits
