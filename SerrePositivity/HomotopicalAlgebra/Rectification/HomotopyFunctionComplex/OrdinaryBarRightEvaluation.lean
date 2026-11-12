module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReference
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionBarReduction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftPadding

/-!
# 中断した任意モデル源への一般化：OrdinaryBarRightEvaluation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The original right leg is invertible exactly when the ordinary evaluation is。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0216][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0216
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The original right leg is invertible exactly when the ordinary evaluation is

The reference composite is already invertible by the small model theorem.
No invertibility of either the evaluation or the right leg is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRightEvaluation
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

lemma padded_reference :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app
      ((OrdinaryResolutionPairs.raw (C := C)).obj
        (OrdinaryResolutionPairs.forgetFrames.obj R))).hom ≫
      BarConstruction.commaSection (OrdinaryResolutionPairs.projection (C := C))
        OrdinaryResolutionPairs.raw
        (d := OrdinaryResolutionPairs.forgetFrames.obj R)
        (𝟙 ((RightResolutionMapping.projection (C := C)).obj R)) =
      OrdinaryBarReference.sectionMap R := by
  ext n x
  rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma right_isIso_iff_evaluation :
    IsIso (AnodyneHomotopy.anodyneQ.map ((OrdinaryResolutionBar.right (C := C)).app R)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluation.evaluation R a b)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have hcomp : IsIso (Q.map (OrdinaryBarReference.sectionMap R) ≫
      Q.map (OrdinaryBarEvaluation.evaluation R a b)) := by
    rw [← Q.map_comp]
    exact OrdinaryBarReference.section_evaluation_isIso R a b hcof hfib
  have heval : IsIso (Q.map (OrdinaryBarReference.sectionMap R)) ↔
      IsIso (Q.map (OrdinaryBarEvaluation.evaluation R a b)) := by
    constructor
    · intro h
      have := h
      exact (isIso_comp_left_iff _ _).mp hcomp
    · intro h
      have := h
      exact (isIso_comp_right_iff _ _).mp hcomp
  have hpad : IsIso (Q.map (BarConstruction.commaSection
      (OrdinaryResolutionPairs.projection (C := C)) OrdinaryResolutionPairs.raw
      (d := OrdinaryResolutionPairs.forgetFrames.obj R)
      (𝟙 ((RightResolutionMapping.projection (C := C)).obj R)))) ↔
      IsIso (Q.map (OrdinaryBarReference.sectionMap R)) := by
    have := Functor.map_isIso (F := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app ((OrdinaryResolutionPairs.raw (C := C)).obj
        (OrdinaryResolutionPairs.forgetFrames.obj R))).hom
    rw [← padded_reference, Q.map_comp]
    exact (isIso_comp_left_iff _ _).symm
  exact (OrdinaryResolutionBar.right_image_isIso_iff Q
    (Localization.inverts Q SSet.anodyneExtensions) R).trans
    ((BarConstruction.spanRight_isIso_iff_section OrdinaryResolutionPairs.projection
      OrdinaryResolutionPairs.raw Q (Localization.inverts Q SSet.anodyneExtensions)
        (OrdinaryResolutionPairs.forgetFrames.obj R)).trans (hpad.trans heval))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRightEvaluation
