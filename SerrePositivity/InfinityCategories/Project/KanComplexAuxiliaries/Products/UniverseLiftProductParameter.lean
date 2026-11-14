module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftTensor
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.DiagramUniverseLift
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.DiagramTensor

/-!
# 動く小さいパラメータと標準単体の直積を小さい宇宙の対象で表す同型を構成する

## 概要
動く小さいパラメータと標準単体の直積を小さい宇宙の対象で表す同型を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0602][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0602
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual small-universe model of a moving parameter times a standard simplex
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
variable {D : Type uD} [Category.{vD} D] (K : D ⥤ SSet.{v}) (m : ℕ)

/- 旧宣言の技術注記：
A natural isomorphism of actual parameter diagrams, without any model structure.
-/
/-- 動く小さいパラメータと標準単体の直積を小さい宇宙の対象で表す同型を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def iso : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk m))) ≅
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
      (SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk m)) :=
  NatIso.ofComponents (fun d => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorIso (K.obj d)
    (SSet.stdSimplex.obj (SimplexCategory.mk m)) ≪≫
      whiskerLeftIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (K.obj d)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso m))
    (by intro d e f; ext n x; rfl)

lemma hom_family (d : D) {P : SSet.{v}}
    (h : K.obj d ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk m) ⟶ P) :
    ((iso.{w} K m).hom.app d) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap h = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map h := by
  ext n x
  rfl

lemma operator {m n : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.map θ) K)
      SSet.uliftFunctor.{w, v} ≫ (iso.{w} K n).hom =
    (iso.{w} K m).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.map θ)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) := by
  ext d s x
  rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
