module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRetractSystem
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordRetractionAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordContraction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual word contractions of the ordinary bar retracts。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0240][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0240
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual word contractions of the ordinary bar retracts

Only the small simplicial-set model is used. Word parameters and ambient
retracts may live in the larger auxiliary universe. Concatenation acts
strictly, without a semigroup assumption on the original interval contraction.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordContraction
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (b : Cᵒᵖ × C)

abbrev wordEval (n : SimplexCategoryᵒᵖ) :=
  WordRetractionAction.eval (section_ hcof hfib b) (projection hcof hfib b)
    (section_fac hcof hfib b) (contraction hcof hfib b)
    (contraction_over hcof hfib b) (contraction_on_section hcof hfib b) n

abbrev wordAction : ambient hcof hfib b ⊗ WordSegment.obj ⟶ ambient hcof hfib b :=
  WordRetractionAction.action (section_ hcof hfib b) (projection hcof hfib b)
    (section_fac hcof hfib b) (contraction hcof hfib b)
    (contraction_over hcof hfib b) (contraction_on_section hcof hfib b)

lemma wordAction_letter : ambient hcof hfib b ◁ WordSegment.letter ≫
    wordAction hcof hfib b = (contraction hcof hfib b).h :=
  WordRetractionAction.action_letter _ _ _ _ _ _

lemma wordAction_mul : ambient hcof hfib b ◁ WordSegment.mul ≫ wordAction hcof hfib b =
    (α_ (ambient hcof hfib b) WordSegment.obj WordSegment.obj).inv ≫
      wordAction hcof hfib b ▷ WordSegment.obj ≫ wordAction hcof hfib b :=
  WordRetractionAction.action_mul _ _ _ _ _ _

lemma wordAction_over : wordAction hcof hfib b ≫ projection hcof hfib b =
    fst (ambient hcof hfib b) WordSegment.obj ≫ projection hcof hfib b :=
  WordRetractionAction.action_over _ _ _ _ _ _

lemma wordAction_section : section_ hcof hfib b ▷ WordSegment.obj ≫
    wordAction hcof hfib b = fst (lifted hcof hfib b) WordSegment.obj ≫ section_ hcof hfib b :=
  WordRetractionAction.action_section _ _ _ _ _ _

def family {T : SSet.{max u v}} (t : T ⟶ WordSegment.obj) :
    ambient hcof hfib b ⊗ T ⟶ ambient hcof hfib b :=
  ambient hcof hfib b ◁ t ≫ wordAction hcof hfib b

lemma family_substitute {T U : SSet.{max u v}} (t : T ⟶ WordSegment.obj) (j : U ⟶ T) :
    family hcof hfib b (j ≫ t) = ParameterComposition.substitute j (family hcof hfib b t) := by
  ext n x
  rfl

lemma family_mul {T : SSet.{max u v}} (t w : T ⟶ WordSegment.obj) :
    ParameterComposition.comp (family hcof hfib b t) (family hcof hfib b w) =
      family hcof hfib b (lift t w ≫ WordSegment.mul) := by
  ext n x
  change _ = wordEval hcof hfib b n
    (t.app n x.2 * w.app n x.2) x.1
  rw [map_mul]
  rfl

lemma family_unit (T : SSet.{max u v}) :
    family hcof hfib b (WordSegment.unitAt T) =
      ParameterComposition.const T (𝟙 (ambient hcof hfib b)) := by
  ext n x
  change wordEval hcof hfib b n 1 x.1 = x.1
  rw [map_one, RetractEndomorphisms.one_apply]

lemma family_zero (T : SSet.{max u v}) :
    family hcof hfib b (WordSegment.zeroAt T) =
      ParameterComposition.const T (projection hcof hfib b ≫ section_ hcof hfib b) := by
  ext n x
  change wordEval hcof hfib b n 0 x.1 = _
  rw [map_zero, RetractEndomorphisms.zero_apply]
  rfl

lemma family_over {T : SSet.{max u v}} (t : T ⟶ WordSegment.obj) :
    family hcof hfib b t ≫ projection hcof hfib b =
      fst (ambient hcof hfib b) T ≫ projection hcof hfib b := by
  ext n x
  exact (wordEval hcof hfib b n (t.app n x.2)).over x.1

lemma family_section {T : SSet.{max u v}} (t : T ⟶ WordSegment.obj) :
    section_ hcof hfib b ▷ T ≫ family hcof hfib b t =
      fst (lifted hcof hfib b) T ≫ section_ hcof hfib b := by
  ext n x
  exact (wordEval hcof hfib b n (t.app n x.2)).fixed x.1

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordContraction
