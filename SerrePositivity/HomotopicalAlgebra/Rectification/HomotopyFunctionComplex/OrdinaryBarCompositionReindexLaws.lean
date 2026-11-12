module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionReindex

/-!
# 中断した任意モデル源への一般化：OrdinaryBarCompositionReindexLaws

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Identity, composition, and selected-point laws for composition-choice reindexing。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0152][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0152
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Identity, composition, and selected-point laws for composition-choice reindexing
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T U V : SSet.{v}} {X Y Z : D C}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
  (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Z)

lemma compositionChoices_reindex_id : compositionChoices_reindex hcof hfib P j f g c d e (𝟙 T) =
    𝟙 (compositionChoices hcof hfib P j f g c d e) := by
  unfold compositionChoices_reindex
  simp only [pre_id, NatTrans.id_app]
  exact ComparisonTriangleTransport.map_id _ _

lemma compositionChoices_reindex_comp (i : U ⟶ T) (k : V ⟶ U) :
    compositionChoices_reindex hcof hfib P j f g c d e i ≫
      compositionChoices_reindex hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e) k =
    compositionChoices_reindex hcof hfib P j f g c d e (k ≫ i) := by
  apply pullback.hom_ext
  · simp only [compositionChoices_reindex, ComparisonTriangleTransport.map, Category.assoc,
      RelativeChoiceSpace.postMap_inclusion, RelativeChoiceSpace.postMap_inclusion_assoc]
    rw [← (ihom (SSet.stdSimplex.obj (SimplexCategory.mk 2))).map_comp]
    have hq : (pre i).app ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) ≫
        (pre k).app _ = (pre (k ≫ i)).app _ := RelativeChoiceSpace.restriction_comp k i
    rw [hq]
  · simp only [compositionChoices_reindex, ComparisonTriangleTransport.map, Category.assoc,
      RelativeChoiceSpace.postMap_projection]

variable (i : U ⟶ T)

lemma compositionTriangle_point_reindex (a : compositionTriangleData hcof hfib P j f g c d e) :
    ComparisonTriangleChoices.ofData _ _ a ≫
        compositionChoices_reindex hcof hfib P j f g c d e i =
      ComparisonTriangleChoices.ofData _ _
        (compositionTriangle_reindex hcof hfib P j f g c d e i a) :=
  ComparisonTriangleTransport.ofData_map _ _ _ _ _ _ _ _

lemma compositionTriangle_family_reindex (a : compositionTriangleData hcof hfib P j f g c d e) :
    uncurry (compositionTriangle_reindex hcof hfib P j f g c d e i a).triangle =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ uncurry a.triangle := by
  change uncurry (a.triangle ≫ (pre i).app _) = _
  rw [uncurry_pre_app]

abbrev selectedTriangleReindexComparison := comparisonOfCompositionTriangles hcof hfib P
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g)
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e)
  (compositionTriangle_reindex hcof hfib P j f g c d e i
    (compositionTriangle hcof hfib P j f g c d e))
  (compositionTriangle hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
