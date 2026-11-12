module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom

/-!
# 中断した任意モデル源への一般化：SmallKanHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Small Kan values with small interval-homotopy-class morphisms。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0573][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0573
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Small Kan values with small interval-homotopy-class morphisms

This is an ordinary category, not an enrichment or a strict simplicial
replacement of a diagram. Its universe-lift realization is fully faithful
in the large anodyne localization. No simplicial model structure is used.
-/

@[expose] public section
universe v w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SmallKanHomotopy

structure Object where
  value : SSet.{v}
  kan : SSet.modelCategoryQuillen.J.rlp (terminal.from value)

def comp {X Y Z : Object.{v}} (f : HomotopyClasses.obj X.value Y.value)
    (g : HomotopyClasses.obj Y.value Z.value) : HomotopyClasses.obj X.value Z.value :=
  Quot.liftOn f (fun f => HomotopyClasses.pre f g) (fun _ _ ⟨H⟩ => by
    refine Quot.inductionOn g (fun g => ?_)
    exact HomotopyClasses.sound (HomotopyClasses.postHomotopy g H))

instance : Category.{v} Object.{v} where
  Hom X Y := HomotopyClasses.obj X.value Y.value
  id X := HomotopyClasses.mk (𝟙 X.value)
  comp := comp
  id_comp f := by
    refine Quot.inductionOn f (fun f => ?_)
    exact congrArg HomotopyClasses.mk (Category.id_comp f)
  comp_id f := by
    refine Quot.inductionOn f (fun f => ?_)
    exact congrArg HomotopyClasses.mk (Category.comp_id f)
  assoc f g h := by
    refine Quot.inductionOn f (fun f => ?_)
    refine Quot.inductionOn g (fun g => ?_)
    refine Quot.inductionOn h (fun h => ?_)
    exact congrArg HomotopyClasses.mk (Category.assoc f g h)

variable {D : Type uD} [Category.{vD} D] (L : SSet.{max w v} ⥤ D)
  [L.IsLocalization SSet.anodyneExtensions]

def realization : Object.{v} ⥤ D where
  obj X := L.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X.value)
  map {X Y} f := UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan f
  map_id X := by
    change L.map (SSet.uliftFunctor.{w, v}.map (𝟙 X.value)) = 𝟙 _
    rw [SSet.uliftFunctor.map_id, L.map_id]
  map_comp {X Y Z} f g := by
    refine Quot.inductionOn f (fun f => ?_)
    refine Quot.inductionOn g (fun g => ?_)
    change L.map (SSet.uliftFunctor.{w, v}.map (f ≫ g)) =
      L.map (SSet.uliftFunctor.{w, v}.map f) ≫ L.map (SSet.uliftFunctor.{w, v}.map g)
    rw [SSet.uliftFunctor.map_comp, L.map_comp]

def fullyFaithful : (realization.{v, w} L).FullyFaithful where
  preimage {X Y} f := (UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan).symm f
  map_preimage {X Y} f :=
    (UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan).apply_symm_apply f
  preimage_map {X Y} f :=
    (UniverseLift.smallLocalizedHomEquiv.{w, v} L X.value Y.value Y.kan).symm_apply_apply f

end SerrePositivity.SimplicialModel.SmallKanHomotopy
