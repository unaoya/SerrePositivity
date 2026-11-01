module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WeightedWordHom
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.WeightedPathParameterMap

/-!
# 中断した任意モデル源への一般化：FreeWordHom

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual ambient-word Hom augmentation for a free source is inverted。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0400][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0400
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual ambient-word Hom augmentation for a free source is inverted
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.QuiverWeightedPaths

namespace SerrePositivity.SimplicialModel.FreeWordHom
variable (V : Type u) [Quiver.{v} V] (X Y : V)

abbrev degreeEquiv (n : SimplexCategoryᵒᵖ) :=
  normalFormEquiv V (WordSegment.degree.{max u v} n) X Y

def hom : SSet.{max u v} where
  obj n := (targetSource V (WordSegment.degree.{max u v} n)).obj X ⟶
    (targetSource V (WordSegment.degree.{max u v} n)).obj Y
  map {n m} θ := ↾fun f => degreeEquiv V X Y m
    (mapWeights (WordSegment.degreeMap θ) ((degreeEquiv V X Y n).symm f))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    change degreeEquiv V X Y n
      (mapWeights (WordSegment.degreeMap (𝟙 n)) ((degreeEquiv V X Y n).symm f)) = f
    rw [WordPresentationDiagram.degreeMap_id]
    exact (congrArg (degreeEquiv V X Y n)
      (mapWeights_id ((degreeEquiv V X Y n).symm f))).trans
        ((degreeEquiv V X Y n).apply_symm_apply f)
  map_comp {a b c} θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    change degreeEquiv V X Y c
      (mapWeights (WordSegment.degreeMap (θ ≫ φ)) ((degreeEquiv V X Y a).symm f)) =
        degreeEquiv V X Y c (mapWeights (WordSegment.degreeMap φ)
          ((degreeEquiv V X Y b).symm (degreeEquiv V X Y b
            (mapWeights (WordSegment.degreeMap θ) ((degreeEquiv V X Y a).symm f)))))
    rw [Equiv.symm_apply_apply, mapWeights_comp, WordPresentationDiagram.degreeMap_comp]
    rfl

def comparisonIso : hom V X Y ≅ WeightedWordHom.hom V X Y :=
  NatIso.ofComponents (fun n => Equiv.toIso (degreeEquiv V X Y n).symm) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    exact (degreeEquiv V X Y m).symm_apply_apply _)

lemma map_eq {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (f : (hom V X Y).obj n) :
    (hom V X Y).map θ f = (AmbientWords.map (𝟭 (Paths V)) (WordSegment.degreeMap θ)).map f := by
  change eval V _ (mapWeights (WordSegment.degreeMap θ) ((degreeEquiv V X Y n).symm f)) = _
  rw [← map_eval]
  exact congrArg (fun g => (AmbientWords.map (𝟭 (Paths V)) (WordSegment.degreeMap θ)).map g)
    ((degreeEquiv V X Y n).apply_symm_apply f)

def augmentation : hom V X Y ⟶ WeightedWordHom.base V X Y :=
  (comparisonIso V X Y).hom ≫ WeightedWordHom.projection V X Y

lemma augmentation_app (n : SimplexCategoryᵒᵖ) (f : (hom V X Y).obj n) :
    (augmentation V X Y).app n f =
      ULift.up ((AmbientWords.augmentation (Paths V) (WordSegment.degree.{max u v} n)).map f) := by
  change ULift.up (forget ((degreeEquiv V X Y n).symm f)) = _
  apply congrArg ULift.up
  calc
    _ = (AmbientWords.augmentation (Paths V) (WordSegment.degree.{max u v} n)).map
        (eval V _ ((degreeEquiv V X Y n).symm f)) := (augmentation_eval V _ _).symm
    _ = _ := congrArg
      (fun g => (AmbientWords.augmentation (Paths V) (WordSegment.degree.{max u v} n)).map g)
      ((degreeEquiv V X Y n).apply_symm_apply f)

lemma localized_augmentation_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (augmentation V X Y)) := by
  rw [augmentation, Functor.map_comp]
  have : IsIso (AnodyneHomotopy.anodyneQ.map (WeightedWordHom.projection V X Y)) :=
    WeightedWordHom.localized_projection_isIso V X Y
  infer_instance

end SerrePositivity.SimplicialModel.FreeWordHom
