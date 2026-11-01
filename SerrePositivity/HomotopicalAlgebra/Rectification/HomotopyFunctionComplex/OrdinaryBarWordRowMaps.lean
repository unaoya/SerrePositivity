module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordFunctoriality
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedSource

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordRowMaps

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All outer simplex operators act on the actual word Hom rows。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0245][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0245
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All outer simplex operators act on the actual word Hom rows
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowMaps
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable (C : Type u) [Category.{v} C] (X Y : D C)

abbrev row (n : SimplexCategoryᵒᵖ) := OrdinaryBarFixedRowWordHom.hom C n.unop.len X Y

def rowMap {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) : row C X Y n ⟶ row C X Y m where
  app k := ↾fun f => (AmbientWords.map (literalMap C θ)
    (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k))).map f
  naturality {k l} φ := by
    apply ConcreteCategory.hom_ext
    intro f
    change (AmbientWords.map (literalMap C θ) (MonoidWithZeroHom.id _)).map
      ((row C X Y n).map φ f) = (row C X Y m).map φ
        ((AmbientWords.map (literalMap C θ) (MonoidWithZeroHom.id _)).map f)
    rw [OrdinaryBarFixedRowWordHom.map_eq, OrdinaryBarFixedRowWordHom.map_eq]
    exact congr($(AmbientWords.commute (literalMap C θ) (WordSegment.degreeMap φ)).map f).symm

lemma literal_id (n : SimplexCategoryᵒᵖ) : literalMap C (𝟙 n) = 𝟭 ((diagram C).obj n) :=
  congrArg Cat.Hom.toFunctor ((literal C).map_id n)

lemma literal_comp {n m k : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (φ : m ⟶ k) :
    literalMap C (θ ≫ φ) = literalMap C θ ⋙ literalMap C φ :=
  congrArg Cat.Hom.toFunctor ((literal C).map_comp θ φ)

lemma rowMap_id (n : SimplexCategoryᵒᵖ) : rowMap C X Y (𝟙 n) = 𝟙 (row C X Y n) := by
  ext k f
  have h := congrArg (fun F => AmbientWords.map F
    (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k))) (literal_id C n)
  have hh := h.trans AmbientWords.map_id
  exact congr($(hh).map f)

lemma rowMap_comp {n m k : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (φ : m ⟶ k) :
    rowMap C X Y (θ ≫ φ) = rowMap C X Y θ ≫ rowMap C X Y φ := by
  ext l f
  have h : AmbientWords.map (literalMap C (θ ≫ φ))
      (MonoidWithZeroHom.id (WordSegment.degree.{max u v} l)) =
      AmbientWords.map (literalMap C θ) (MonoidWithZeroHom.id _) ⋙
        AmbientWords.map (literalMap C φ) (MonoidWithZeroHom.id _) := by
    rw [literal_comp]
    simpa only [MonoidWithZeroHom.comp_id] using AmbientWords.map_comp
      (literalMap C θ) (literalMap C φ) (MonoidWithZeroHom.id (WordSegment.degree.{max u v} l))
      (MonoidWithZeroHom.id _)
  exact congr($(h).map f)

def rows : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} where
  obj := row C X Y
  map := rowMap C X Y
  map_id := rowMap_id C X Y
  map_comp := rowMap_comp C X Y

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowMaps
