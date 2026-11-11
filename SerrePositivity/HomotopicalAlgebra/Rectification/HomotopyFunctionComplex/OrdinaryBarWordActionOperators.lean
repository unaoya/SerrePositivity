module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordActionOperators

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All free-resolution operator laws on native small word-arrow action families。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0238][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0238
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All free-resolution operator laws on native small word-arrow action families
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordActionOperators
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarWordAction OrdinaryBarWordEvaluationOperators
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {T : SSet.{v}}

lemma family_face (i : Fin (n + 2))
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P n)
    {X Y : degree (D C) (n + 2)}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ hom (C := C) (n + 1) X Y) :
    family hcof hfib P n j (f ≫ WordPresentationSourceMap.mapHomSame
        (FreeGeneratorFaces.fixedFace (D C) (n + 1) i) X Y) =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) f := by
  ext k x
  have he := congr($(evaluation_face (C := C) hcof hfib P n i k
    (j.app k (ULift.up x.2))).map (f.app k (ULift.up x.2)))
  exact congrArg ULift.down (types_congr_hom he (ULift.up x.1))

lemma family_degeneracy (i : Fin (n + 1))
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    family hcof hfib P (n + 1) j (f ≫ WordPresentationSourceMap.mapHomSame
        (degeneracyFunctor (D C) n i) X Y) =
      family hcof hfib P n
        (j ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) f := by
  ext k x
  have he := congr($(evaluation_degeneracy (C := C) hcof hfib P n i k
    (j.app k (ULift.up x.2))).map (f.app k (ULift.up x.2)))
  exact congrArg ULift.down (types_congr_hom he (ULift.up x.1))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordActionOperators
