module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.UniverseLiftAnodyne

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionInvariance

/-!
# 中断した任意モデル源への一般化：OrdinaryBarMappingComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Natural comparison of the ordinary bar with the small mapping diagrams。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0200][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0200
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Natural comparison of the ordinary bar with the small mapping diagrams

The whole diagrams compare after any functor inverting anodyne extensions.
The base bar remains large. Only the original small simplicial model is used.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hcof hfib hL in
lemma small_map_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : weakEquivalences SSet.{v} f) :
    IsIso (L.map (SSet.uliftFunctor.{max u v, v}.map f)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.anodyneQ_map_isIso_of_weakEquivalence hcof hfib f hf)

include hcof hfib hL in
lemma right_isIso : IsIso (Functor.whiskerRight
    (OrdinaryResolutionBar.right (C := C)) L) := by
  have (R : RightResolutionMapping.Index C) :
      IsIso ((Functor.whiskerRight (OrdinaryResolutionBar.right (C := C)) L).app R) :=
    AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _
      (OrdinaryBarEvaluationEquivalence.right_isIso R
        (OrdinaryBarCenters.leftSystem R hcof) (OrdinaryBarCenters.rightSystem R hcof)
        hcof hfib)
  exact NatIso.isIso_of_isIso_app _

/-- The natural span is used as a span, without choosing evaluations on the base. -/
def mixedIso :
    (MixedBiresolutionComparison.functor (C := C) ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  have := right_isIso (C := C) hcof hfib L hL
  exact (BarConstruction.spanLeftComparisonIso (RightResolutionMapping.projection (C := C))
    MixedBiresolutionComparison.functor L hL).symm ≪≫
      asIso (Functor.whiskerRight OrdinaryResolutionBar.right L)

def resolutionIso :
    (RightResolutionMapping.functor (C := C) hcof hfib ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  let η := Functor.whiskerRight
    (Functor.whiskerRight (MixedResolutionInvariance.comparison (C := C) hcof hfib)
      SSet.uliftFunctor.{max u v, v}) L
  have (R : RightResolutionMapping.Index C) : IsIso (η.app R) :=
    small_map_isIso hcof hfib L hL _
      (MixedResolutionInvariance.comparison_weakEquivalence hcof hfib R)
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact (asIso η).symm ≪≫ mixedIso hcof hfib L hL

/-- Degree zero is the existing replacement mapping diagram pulled back along
the actual target presentation functor. -/
def zeroIso :
    (RightResolutionMapping.zero (C := C) hcof hfib ⋙
      SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
    (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  let η := Functor.whiskerRight
    (Functor.whiskerRight (RightResolutionMapping.comparison (C := C) hcof hfib)
      SSet.uliftFunctor.{max u v, v}) L
  have (R : RightResolutionMapping.Index C) : IsIso (η.app R) :=
    small_map_isIso hcof hfib L hL _
      (RightResolutionMapping.comparison_weakEquivalence hcof hfib R)
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact asIso η ≪≫ resolutionIso hcof hfib L hL

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison
