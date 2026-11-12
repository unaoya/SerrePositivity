module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentEvaluation

/-!
# 中断した任意モデル源への一般化：OrdinaryBarRelativeNativeComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Native interval comparisons decoded from the relative descent space。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0212][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0212
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Native interval comparisons decoded from the relative descent space

The comparison is an actual homotopy between maps into the original
small internal Hom, extracted from the one global comparison interval.
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
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def nativeRestrictionComparison {T : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y) :
    SSet.Homotopy (nativeFamily hcof hfib P j (g ≫ smallAugmentation C X Y) c)
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j g) := by
  let H := RestrictionDescentChoices.fixedFamilyComparison (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c
  let W := HomotopyClasses.preHomotopy (lift (lift j g) (𝟙 _)) H
  apply UniverseLift.lowerHomotopy
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints W ?_ ?_
  · change lift (lift j g) (𝟙 _) ≫ parameterAugmentation P X Y ▷ _ ≫
        family hcof hfib P c = _
    rw [← Category.assoc, lift_whiskerRight, lift_whiskerLeft]
    rfl
  · change lift (lift j g) (𝟙 _) ≫ fst _ _ ≫
      OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y = _
    rw [← Category.assoc, lift_fst,
      OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily]

lemma nativeRestrictionComparison_substitute {T U : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y) (i : U ⟶ T) :
    (nativeRestrictionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c)).h =
        i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (nativeRestrictionComparison hcof hfib P j g c).h := by
  ext n x
  simp only [nativeRestrictionComparison, UniverseLift.lowerHomotopy,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, RestrictionDescentChoices.fixedFamilyComparison,
    RestrictionDescentChoices.familyComparison, RestrictionDescentChoices.parameterComparison,
    HomotopyClassesClosed.uncurryHomotopy, HomotopyClasses.preHomotopy,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor]
  rfl

lemma native_relative_comparison_extension {U V : SSet.{v}} {X Y : D C} (i : U ⟶ V) [Mono i]
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ P)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} U ⟶ choices hcof hfib P X Y) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ choices hcof hfib P X Y,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e = c ∧
        i ≫ nativeFamily hcof hfib P j (g ≫ smallAugmentation C X Y) e =
          nativeFamily hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
            ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) ≫ smallAugmentation C X Y) c ∧
        i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (nativeRestrictionComparison hcof hfib P j g e).h =
            (nativeRestrictionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
              (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) c).h := by
  obtain ⟨e, he, hf⟩ := native_relative_extension hcof hfib P i j
    (g ≫ smallAugmentation C X Y) c
  refine ⟨e, he, ?_, ?_⟩
  · simpa only [Category.assoc] using hf
  · rw [← nativeRestrictionComparison_substitute, he]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
