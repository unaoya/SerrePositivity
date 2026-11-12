module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeComposition
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTriangle

/-!
# 中断した任意モデル源への一般化：OrdinaryBarRelativeCompositionTriangle

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual composition triangle retains all three Hom comparisons。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0209][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0209
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual composition triangle retains all three Hom comparisons

Two sides retain the selected comparison for the composite and the
simultaneous composite of the two selected input comparisons. The third
side compares the descended composite with the composite descended maps.
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
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
  (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Z)

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma composite_augmentation : (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) ≫
    smallAugmentation C X Z =
      lift (f ≫ smallAugmentation C X Y) (g ≫ smallAugmentation C Y Z) ≫
        baseComposition C X Y Z := by
  rw [Category.assoc, augmentation_composition, ← Category.assoc, lift_map]

abbrev compositionTriangle := KanComparisonTriangle.build
  (nativeRestrictionComparison hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
  (compositionComparison hcof hfib P j f g c d)
  (SimplexParameterHom.native_kan (small hcof hfib X) (small hcof hfib Z)
    (OrdinaryBarSmallReference.value_kan hcof hfib Z))

abbrev compositionTriangleFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶
    (ihom (small hcof hfib X)).obj (small hcof hfib Z) :=
  KanComparisonTriangle.family _ _ (compositionTriangle hcof hfib P j f g c d e)

lemma compositionTriangle_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    compositionTriangleFamily hcof hfib P j f g c d e =
      (compositionComparison hcof hfib P j f g c d).h :=
  KanComparisonTriangle.family_zero _ _ _

lemma compositionTriangle_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    compositionTriangleFamily hcof hfib P j f g c d e =
      (nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h :=
  KanComparisonTriangle.family_one _ _ _

abbrev nativeCompositionComparison :=
  KanComparisonTriangle.comparison _ _ (compositionTriangle hcof hfib P j f g c d e)

lemma compositionTriangle_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    compositionTriangleFamily hcof hfib P j f g c d e =
      (nativeCompositionComparison hcof hfib P j f g c d e).h :=
  KanComparisonTriangle.family_two _ _ _

def nativeCompositionComparison_base : SSet.Homotopy
    (nativeFamily hcof hfib P j
      (lift (f ≫ smallAugmentation C X Y) (g ≫ smallAugmentation C Y Z) ≫
        baseComposition C X Y Z) e)
    (lift (nativeFamily hcof hfib P j (f ≫ smallAugmentation C X Y) c)
      (nativeFamily hcof hfib P j (g ≫ smallAugmentation C Y Z) d) ≫
        MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (nativeCompositionComparison hcof hfib P j f g c d e)
    (by rw [composite_augmentation]) rfl

def nativeUnitComparison {V : SSet.{v}} (A : D C)
    (k : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ P)
    (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ choices hcof hfib P A A) :
    SSet.Homotopy
      (nativeFamily hcof hfib P k (SSet.stdSimplex.isTerminalObj₀.from _ ≫ baseIdentity C A) s)
      (toUnit V ≫ MonoidalClosed.id (small hcof hfib A)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (nativeRestrictionComparison hcof hfib P k
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C A) s)
    (by rw [Category.assoc, augmentation_identity])
    (OrdinaryBarDiagonalClosedAction.nativeFamily_identity hcof hfib P A k)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
