module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FixedBoundaryExtensions

/-!
# 互換な余テンソルの面の全族を単体境界上に貼り合わせる

## 概要
互換な余テンソルの面の全族を単体境界上に貼り合わせる。
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
[棚卸し m0352][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0352
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing whole cotensor families along standard simplicial boundaries

Transposition exchanges the external family parameter and the boundary
parameter. Thus the actual subcomplex gluing theorem applies without
assuming a tensor colimit comparison or replacing the boundary object.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BoundaryCotensor
variable {T K P : SSet.{v}}

/-- Exchange the two actual parameters using symmetry and the closed adjunction. -/
def transpose (f : T ⟶ (ihom K).obj P) : K ⟶ (ihom T).obj P :=
  curry ((β_ T K).hom ≫ uncurry f)

lemma transpose_transpose (f : T ⟶ (ihom K).obj P) : transpose (transpose f) = f := by
  apply uncurry_injective
  simp only [transpose, uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry,
    Category.id_comp]

lemma transpose_injective : Function.Injective (transpose (T := T) (K := K) (P := P)) := by
  intro f g h
  simpa only [transpose_transpose] using congrArg transpose h

lemma transpose_restriction {A : SSet.{v}} (i : A ⟶ K) (f : T ⟶ (ihom K).obj P) :
    transpose (f ≫ (pre i).app P) = i ≫ transpose f := by
  apply uncurry_injective
  rw [transpose, uncurry_curry, uncurry_pre_app, uncurry_natural_left,
    transpose, uncurry_curry, ← Category.assoc, ← BraidedCategory.braiding_naturality_right]
  simp only [Category.assoc]

abbrev Compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    faces j ≫ (pre (SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)))).app P =
      faces k ≫ (pre (SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)))).app P

lemma transpose_compatible {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible (fun k => transpose (faces k)) := by
  intro j k hjk
  rw [← transpose_restriction, ← transpose_restriction, hf j k hjk]

/- 旧宣言の技術注記：
Glue all prescribed whole facet families into the actual boundary cotensor.
-/
/-- 互換な余テンソルの面の全族を単体境界上に貼り合わせる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
def standardDesc {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) : T ⟶ (ihom (SSet.boundary.{v} (n + 2)).toSSet).obj P :=
  transpose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc (fun k => transpose (faces k))
    (transpose_compatible faces hf))

@[reassoc]
lemma standardDesc_fac {n : ℕ}
    (faces : Fin (n + 3) → (T ⟶ (ihom
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))).obj P))
    (hf : Compatible faces) (k : Fin (n + 3)) :
    standardDesc faces hf ≫ (pre (SSet.boundary.ι k)).app P = faces k := by
  apply transpose_injective
  rw [transpose_restriction, standardDesc, transpose_transpose,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc_fac]

lemma hom_ext {n : ℕ} {f g : T ⟶ (ihom (SSet.boundary.{v} (n + 1)).toSSet).obj P}
    (h : ∀ k : Fin (n + 2), f ≫ (pre (SSet.boundary.ι k)).app P =
      g ≫ (pre (SSet.boundary.ι k)).app P) : f = g := by
  apply transpose_injective
  apply SSet.boundary.hom_ext
  intro k
  rw [← transpose_restriction, ← transpose_restriction, h k]

end SerrePositivity.SimplicialModel.BoundaryCotensor
