module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-!
# 共有パラメータを持つ射の合成の転置は内部Homの標準合成に一致する

## 概要
共有パラメータを持つ射の合成の転置は内部Homの標準合成に一致する。
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
[棚卸し m0361][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0361
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Shared-parameter composition transposes to the standard internal-Hom composition
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ClosedParameterComposition
variable {X Y Z T : SSet.{v}}

/-- 共有パラメータを持つ射の合成の転置は内部Homの標準合成に一致する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
lemma curry_comp (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) :
    curry (ParameterComposition.comp f g) =
      lift (curry f) (curry g) ≫ MonoidalClosed.comp X Y Z := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    MonoidalClosed.compTranspose_eq]
  ext n x
  have hf := types_congr_hom (congr_app (uncurry_curry f) n) x
  rw [uncurry_eq] at hf
  have hg := types_congr_hom (congr_app (uncurry_curry g) n) (f.app n x, x.2)
  rw [uncurry_eq] at hg
  change ((ihom.ev X).app Y).app n (x.1, (curry f).app n x.2) = f.app n x at hf
  change ((ihom.ev Y).app Z).app n (f.app n x, (curry g).app n x.2) =
    g.app n (f.app n x, x.2) at hg
  change g.app n (f.app n x, x.2) = ((ihom.ev Y).app Z).app n
    (((ihom.ev X).app Y).app n (x.1, (curry f).app n x.2), (curry g).app n x.2)
  rw [hf]
  exact hg.symm

lemma curry_fst (X T : SSet.{v}) :
    curry (fst X T) = toUnit T ≫ MonoidalClosed.id X := by
  rw [fst_def, curry_natural_left, MonoidalClosed.id_eq]
  rfl

end SerrePositivity.SimplicialModel.ClosedParameterComposition
