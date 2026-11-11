module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionChoices
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleTransport

/-!
# 中断した任意モデル源への一般化：OrdinaryBarCompositionReindex

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual reindexing of the small composition triangle choice space。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0151][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0151
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual reindexing of the small composition triangle choice space
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T U : SSet.{v}} {X Y Z : D C}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
  (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Z) (i : U ⟶ T)

lemma compositeComparison_reindex :
    curry (nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h ≫
      (pre i).app ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) =
    curry (nativeRestrictionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (lift (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) ≫
        OrdinaryBarFixedWordResolution.composition C X Y Z) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e)).h := by
  rw [curry_pre_app]
  have h := nativeRestrictionComparison_substitute hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e i
  have he : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} i ≫
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) =
    lift (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) ≫
      OrdinaryBarFixedWordResolution.composition C X Y Z := by rw [← Category.assoc, comp_lift]
  rw [he] at h
  rw [h]

lemma inputComparison_reindex : curry (compositionComparison hcof hfib P j f g c d).h ≫
      (pre i).app ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) =
    curry (compositionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d)).h := by
  rw [curry_pre_app, compositionComparison_substitute]

def compositionChoices_reindex : compositionChoices hcof hfib P j f g c d e ⟶
    compositionChoices hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e) :=
  ComparisonTriangleTransport.map _ _ _ _ ((pre i).app _)
    (compositeComparison_reindex hcof hfib P j f g e i)
    (inputComparison_reindex hcof hfib P j f g c d i)

def compositionTriangle_reindex (a : compositionTriangleData hcof hfib P j f g c d e) :
    compositionTriangleData hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e) :=
  ComparisonTriangleTransport.data _ _ _ _ ((pre i).app _)
    (compositeComparison_reindex hcof hfib P j f g e i)
    (inputComparison_reindex hcof hfib P j f g c d i) a

lemma compositionChoiceFamily_reindex {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    compositionChoiceFamily hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e) (q ≫ compositionChoices_reindex hcof hfib P j f g c d e i) =
    i ▷ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q := by
  rw [compositionChoiceFamily, compositionChoices_reindex, ComparisonTriangleTransport.family_map,
    uncurry_pre_app]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
