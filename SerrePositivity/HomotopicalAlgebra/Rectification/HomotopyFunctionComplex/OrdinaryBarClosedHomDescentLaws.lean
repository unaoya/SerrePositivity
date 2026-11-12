module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent

/-!
# 中断した任意モデル源への一般化：OrdinaryBarClosedHomDescentLaws

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Parameterized identity and composition homotopies after Hom descent。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0147][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0147
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Parameterized identity and composition homotopies after Hom descent

The maps and the intervals are in the original small value universe.
These are individual comparison intervals, not a coherent strictification.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

lemma native_identity_homotopy {T : SSet.{v}} (X : D C)
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P) :
    Nonempty (SSet.Homotopy
      (nativeFamily hcof hfib P j (SSet.stdSimplex.isTerminalObj₀.from _ ≫ baseIdentity C X))
      (toUnit T ≫ MonoidalClosed.id (small hcof hfib X))) := by
  have h := native_restriction_homotopy hcof hfib P j
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X)
  simpa only [Category.assoc, augmentation_identity,
    OrdinaryBarDiagonalClosedAction.nativeFamily_identity] using h

lemma native_composition_homotopy {T : SSet.{v}} {X Y Z : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ baseHom C X Y)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ baseHom C Y Z) :
    Nonempty (SSet.Homotopy
      (nativeFamily hcof hfib P j (lift f g ≫ baseComposition C X Y Z))
      (lift (nativeFamily hcof hfib P j f) (nativeFamily hcof hfib P j g) ≫
        MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z))) := by
  let f' := f ≫ (OrdinaryBarHomSections.small C X Y).section_
  let g' := g ≫ (OrdinaryBarHomSections.small C Y Z).section_
  let c := lift f' g' ≫ OrdinaryBarFixedWordResolution.composition C X Y Z
  have hc : c ≫ smallAugmentation C X Z = lift f g ≫ baseComposition C X Y Z := by
    dsimp only [c]
    rw [Category.assoc, augmentation_composition, ← Category.assoc, lift_map]
    dsimp only [f', g']
    simp only [Category.assoc, SplitEpi.id, Category.comp_id]
  have h := native_restriction_homotopy hcof hfib P j c
  rw [hc] at h
  dsimp only [c] at h
  rw [OrdinaryBarDiagonalClosedAction.nativeFamily_comp] at h
  exact h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
