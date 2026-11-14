module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftFillers
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 単体的宇宙liftの直積と元の直積のliftとの実際の比較射を構成する

## 概要
単体的宇宙liftの直積と元の直積のliftとの実際の比較射を構成する。
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
[棚卸し m0603][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0603
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual universe comparison for whole tensor and standard-simplex families
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- The actual degreewise product comparison, independent of model structures. -/
def tensorIso (K T : SSet.{v}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (K ⊗ T) ≅ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} T :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => (ULift.up x.down.1, ULift.up x.down.2)
      invFun := fun x => ULift.up (x.1.down, x.2.down)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro m n f; ext x; rfl)

variable {K T P : SSet.{v}}

/-- 単体的宇宙liftの直積と元の直積のliftとの実際の比較射を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def tensorMap (h : K ⊗ T ⟶ P) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P :=
  (tensorIso K T).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map h

def lowerTensor (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) : K ⊗ T ⟶ P :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower ((tensorIso K T).hom ≫ h)

lemma tensorMap_lowerTensor (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) :
    tensorMap (lowerTensor h) = h := by
  rw [tensorMap, lowerTensor, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower, Iso.inv_hom_id_assoc]

lemma lowerTensor_tensorMap (h : K ⊗ T ⟶ P) : lowerTensor (tensorMap.{w} h) = h := by
  rw [lowerTensor, tensorMap, Iso.hom_inv_id_assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map]

/-- Lift the entire original family to the actual larger standard simplex. -/
def simplexTensorMap {n : ℕ} (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk n) ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj K ◁ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso n).inv ≫ tensorMap h

def lowerSimplexTensor {n : ℕ}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk n) ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) :
      K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P :=
  lowerTensor (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj K ◁ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso n).hom ≫ h)

lemma lowerSimplexTensor_simplexTensorMap {n : ℕ}
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    lowerSimplexTensor (simplexTensorMap.{w} h) = h := by
  rw [lowerSimplexTensor, simplexTensorMap, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, lowerTensor_tensorMap]

lemma simplexTensorMap_lowerSimplexTensor {n : ℕ}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk n) ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) :
    simplexTensorMap (lowerSimplexTensor h) = h := by
  rw [simplexTensorMap, lowerSimplexTensor, tensorMap_lowerTensor, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

lemma simplexTensorMap_operator {n m : ℕ}
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ◁ SSet.stdSimplex.map θ ≫ simplexTensorMap h =
      simplexTensorMap ((K ◁ SSet.stdSimplex.map θ) ≫ h) := by
  ext d x
  rfl

lemma simplexTensorMap_source {V : SSet.{v}} (i : V ⟶ K) {n : ℕ}
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} i ▷ SSet.stdSimplex.obj (SimplexCategory.mk n) ≫ simplexTensorMap h =
      simplexTensorMap ((i ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ h) := by
  ext d x
  rfl

lemma simplexTensorMap_target {Q : SSet.{v}} {n : ℕ}
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) (q : P ⟶ Q) :
    simplexTensorMap.{w} h ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map q = simplexTensorMap (h ≫ q) := by
  ext d x
  rfl

lemma simplexTensorMap_constant (b : K ⟶ P) (n : ℕ) :
    simplexTensorMap.{w} (fst K (SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ b) =
      fst (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map b := by
  ext d x
  rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
