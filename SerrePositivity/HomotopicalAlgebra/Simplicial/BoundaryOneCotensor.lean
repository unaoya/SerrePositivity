module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# 区間境界の二つの頂点に指定した余テンソル族を貼り合わせる

## 概要
区間境界の二つの頂点に指定した余テンソル族を貼り合わせる。
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
[棚卸し m0355][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0355
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing cotensor families on the actual two-vertex interval boundary
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BoundaryOneCotensor
abbrev vertex := SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)
abbrev boundary := (SSet.boundary.{v} 1).toSSet
abbrev zero : vertex.{v} ⟶ boundary.{v} := SSet.boundary.ι (1 : Fin 2)
abbrev one : vertex.{v} ⟶ boundary.{v} := SSet.boundary.ι (0 : Fin 2)

/-- Tensoring the actual boundary coproduct retains its universal property. -/
def tensorIsColimit (T : SSet.{v}) : IsColimit (BinaryCofan.mk (zero ▷ T) (one ▷ T)) := by
  exact mapIsColimitOfPreservesOfIsColimit (tensorRight T) _ _
    HomotopyFunctionComplex.BoundaryOne.isColimit

variable {T P : SSet.{v}} (a b : T ⟶ (ihom vertex).obj P)

/-- 区間境界の二つの頂点に指定した余テンソル族を貼り合わせる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
def glue : T ⟶ (ihom boundary).obj P :=
  curry ((tensorIsColimit T).desc (BinaryCofan.mk (uncurry a) (uncurry b)))

@[reassoc]
lemma glue_zero : glue a b ≫ (pre zero).app P = a := by
  apply uncurry_injective
  rw [uncurry_pre_app, glue, uncurry_curry]
  exact (tensorIsColimit T).fac (BinaryCofan.mk (uncurry a) (uncurry b)) ⟨WalkingPair.left⟩

@[reassoc]
lemma glue_one : glue a b ≫ (pre one).app P = b := by
  apply uncurry_injective
  rw [uncurry_pre_app, glue, uncurry_curry]
  exact (tensorIsColimit T).fac (BinaryCofan.mk (uncurry a) (uncurry b)) ⟨WalkingPair.right⟩

lemma hom_ext {f g : T ⟶ (ihom boundary).obj P}
    (h₀ : f ≫ (pre zero).app P =
      g ≫ (pre zero).app P)
    (h₁ : f ≫ (pre one).app P =
      g ≫ (pre one).app P) : f = g := by
  apply uncurry_injective
  apply (tensorIsColimit T).hom_ext
  intro j
  rcases j with ⟨j⟩
  cases j
  · exact (uncurry_pre_app _ f zero).symm.trans
      ((congrArg uncurry h₀).trans (uncurry_pre_app _ g zero))
  · exact (uncurry_pre_app _ f one).symm.trans
      ((congrArg uncurry h₁).trans (uncurry_pre_app _ g one))

end SerrePositivity.SimplicialModel.BoundaryOneCotensor
