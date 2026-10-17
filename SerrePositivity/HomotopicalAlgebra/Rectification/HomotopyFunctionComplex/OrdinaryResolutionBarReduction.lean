module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionBar
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex

/-!
# 中断した任意モデル源への一般化：OrdinaryResolutionBarReduction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Reduction of the original right comparison to ordinary resolutions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0254][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0254
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reduction of the original right comparison to ordinary resolutions

Only objectwise frame choices are needed for the converse. No functorial
section, faithfulness, cofinality, or weak equivalence of a right leg is assumed.
-/

@[expose] public section
universe v u uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev ordinaryMiddle : OrdinaryResolutionPairs.Index (C := C) ⥤ SSet.{max u v} :=
  BarConstruction.spanMiddle OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw

abbrev ordinaryRight : ordinaryMiddle (C := C) ⟶ OrdinaryResolutionPairs.projection ⋙ functor :=
  BarConstruction.spanRight OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw

def middleComparison : middle (C := C) ⟶
    OrdinaryResolutionPairs.forgetFrames ⋙ ordinaryMiddle :=
  BarConstruction.middleReindex OrdinaryResolutionPairs.forgetFrames
    OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw

lemma right_factorization : middleComparison (C := C) ≫
    Functor.whiskerLeft OrdinaryResolutionPairs.forgetFrames ordinaryRight = right :=
  BarConstruction.middleReindex_right OrdinaryResolutionPairs.forgetFrames
    OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def middleComparisonImageIso : middle (C := C) ⋙ L ≅
    (OrdinaryResolutionPairs.forgetFrames ⋙ ordinaryMiddle) ⋙ L :=
  BarConstruction.middleReindexImageIso OrdinaryResolutionPairs.forgetFrames
    OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw L hL

include hL in
lemma right_image_isIso_iff (R : RightResolutionMapping.Index C) :
    IsIso (L.map ((right (C := C)).app R)) ↔
      IsIso (L.map ((ordinaryRight (C := C)).app
        (OrdinaryResolutionPairs.forgetFrames.obj R))) :=
  BarConstruction.reindexedRight_image_isIso_iff OrdinaryResolutionPairs.forgetFrames
    OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw L hL R

include hL in
lemma right_natural_image_isIso_iff :
    IsIso (Functor.whiskerRight (right (C := C)) L) ↔
      IsIso (Functor.whiskerRight (ordinaryRight (C := C)) L) := by
  constructor
  · intro h
    have : ∀ P, IsIso ((Functor.whiskerRight (ordinaryRight (C := C)) L).app P) := by
      intro P
      let R : RightResolutionMapping.Index C :=
        (op (FramedResolution.ofResolution P.1.unop),
          op (FramedResolution.ofResolution P.2.unop))
      have : IsIso (L.map ((right (C := C)).app R)) :=
        inferInstanceAs (IsIso ((Functor.whiskerRight (right (C := C)) L).app R))
      exact (right_image_isIso_iff L hL R).mp this
    exact NatIso.isIso_of_isIso_app _
  · intro h
    have : ∀ R, IsIso ((Functor.whiskerRight (right (C := C)) L).app R) := by
      intro R
      apply (right_image_isIso_iff L hL R).mpr
      exact inferInstanceAs (IsIso ((Functor.whiskerRight (ordinaryRight (C := C)) L).app
        (OrdinaryResolutionPairs.forgetFrames.obj R)))
    exact NatIso.isIso_of_isIso_app _

end SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar
