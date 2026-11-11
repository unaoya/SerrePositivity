module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-!
# 互換なテンソル付きの全面の族を単体境界全体に貼り合わせる

## 概要
互換なテンソル付きの全面の族を単体境界全体に貼り合わせる。
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
[棚卸し m0358][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0358
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing actual whole tensor-parameter families along a simplicial boundary
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BoundaryTensorGluing
variable {T P : SSet.{v}}

abbrev Compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    T ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ faces j =
      T ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ faces k

lemma curry_compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : Compatible faces) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible (fun k => curry (faces k)) := by
  intro j k hjk
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
  exact hf j k hjk

/-- 互換なテンソル付きの全面の族を単体境界全体に貼り合わせる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
def desc {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : Compatible faces) : T ⊗ (SSet.boundary (n + 2)).toSSet ⟶ P :=
  uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc (fun k => curry (faces k)) (curry_compatible faces hf))

@[reassoc]
lemma desc_fac {n : ℕ}
    (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : Compatible faces) (k : Fin (n + 3)) :
    T ◁ SSet.boundary.ι k ≫ desc faces hf = faces k := by
  rw [desc, ← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc_fac, uncurry_curry]

lemma hom_ext {n : ℕ} {f g : T ⊗ (SSet.boundary (n + 1)).toSSet ⟶ P}
    (h : ∀ k : Fin (n + 2), T ◁ SSet.boundary.ι k ≫ f = T ◁ SSet.boundary.ι k ≫ g) :
    f = g := by
  have hc : curry f = curry g := by
    apply SSet.boundary.hom_ext
    intro k
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
    exact h k
  exact (uncurry_curry f).symm.trans ((congrArg uncurry hc).trans (uncurry_curry g))

end SerrePositivity.SimplicialModel.BoundaryTensorGluing
