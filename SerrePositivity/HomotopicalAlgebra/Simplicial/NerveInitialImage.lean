module

public import SerrePositivity.CategoryTheory.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 中断した任意モデル源への一般化：NerveInitialImage

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：An initial object gives a model-free localized contraction of its nerve。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0474][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0474
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An initial object gives a model-free localized contraction of its nerve

The actual map to the terminal simplex has the actual initial vertex as
inverse after every functor inverting anodyne maps.
-/

@[expose] public section
universe u v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.NerveInitialImage
variable {C : Type u} [Category.{v} C] {a : C} (ha : IsInitial a)

def contraction : (Functor.const C).obj a ⟶ 𝟭 C where
  app c := ha.to c
  naturality {_ _} _ := ha.hom_ext _ _

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def terminalImageIso : L.obj (nerve C) ≅
    L.obj (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 0)) where
  hom := L.map (SSet.stdSimplex.isTerminalObj₀.from (nerve C))
  inv := L.map (NerveHomotopy.point a)
  hom_inv_id := by
    rw [← L.map_comp, NerveHomotopy.constant_eq]
    have h := AnodyneHomotopy.map_homotopy_eq L hL
      (NerveHomotopy.homotopy (contraction ha))
    exact h.trans (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    have h : NerveHomotopy.point a ≫ SSet.stdSimplex.isTerminalObj₀.from (nerve C) = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, L.map_id]

end SerrePositivity.SimplicialModel.NerveInitialImage
