module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom

/-!
# 中断した任意モデル源への一般化：OrdinaryBarDiagonalAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The whole diagonal parameter acts by actual maps of lifted small values。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0153][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0153
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The whole diagonal parameter acts by actual maps of lifted small values
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAction
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarDiagonalEvaluation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

def action (X Y : D C) : lifted hcof hfib X ⊗
    (P ⊗ OrdinaryBarFixedWordResolution.hom C X Y) ⟶ lifted hcof hfib Y where
  app n := ↾fun x => (evaluation hcof hfib P n x.2.1).map x.2.2 x.1
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (evaluation_naturality hcof hfib P θ x.2.1 X Y x.2.2 x.1).symm

def largeFamily {T : SSet.{max u v}} {X Y : D C} (j : T ⟶ P)
    (f : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    lifted hcof hfib X ⊗ T ⟶ lifted hcof hfib Y :=
  lifted hcof hfib X ◁ lift j f ≫ action hcof hfib P X Y

lemma largeFamily_substitute {T U : SSet.{max u v}} {X Y : D C} (j : T ⟶ P)
    (f : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) (i : U ⟶ T) :
    largeFamily hcof hfib P (i ≫ j) (i ≫ f) =
      ParameterComposition.substitute i (largeFamily hcof hfib P j f) := by
  ext n x
  rfl

lemma lower_largeFamily {T : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (largeFamily hcof hfib P j f) =
      OrdinaryBarDiagonalEvaluation.family hcof hfib P j f := by
  ext n x
  rfl

lemma largeFamily_identity {T : SSet.{max u v}} (X : D C) (j : T ⟶ P) :
    largeFamily hcof hfib P j
      (SSet.stdSimplex.isTerminalObj₀.from T ≫ OrdinaryBarFixedWordResolution.identity C X) =
      fst (lifted hcof hfib X) T := by
  ext n x
  change (evaluation hcof hfib P n (j.app n x.2)).map
    (𝟙 ((SerrePositivity.RetractWords.quotient (FreeGeneratorCategories.degree (D C)
      (n.unop.len + 1)) (WordSegment.degree.{max u v} n)).obj (.small X))) x.1 = x.1
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma largeFamily_comp {T : SSet.{max u v}} {X Y Z : D C} (j : T ⟶ P)
    (f : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    ParameterComposition.comp (largeFamily hcof hfib P j f) (largeFamily hcof hfib P j g) =
      largeFamily hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) := by
  ext n x
  change _ = (evaluation hcof hfib P n (j.app n x.2)).map (f.app n x.2 ≫ g.app n x.2) x.1
  rw [CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAction
