module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallTargetKernelQuotient
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarMappingComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarBaseInvariance

/-!
# 中断した任意モデル源への一般化：PresentationKernelQuotient

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A proved small finite-boundary kernel on the full presentation index。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0261][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0261
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A proved small finite-boundary kernel on the full presentation index

The relation is constructed, not an input certificate. Its base is the
category of actual resolution presentations. Descent to Cᵒᵖ × C is not
asserted, and no section of the presentation projection is chosen.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev reference : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  MixedBiresolutionComparison.functor ⋙ AnodyneKanReplacement.functor

def referenceComparison : MixedBiresolutionComparison.functor (C := C) ⟶ reference :=
  Functor.whiskerLeft MixedBiresolutionComparison.functor AnodyneKanReplacement.unit

def toReference : OrdinaryResolutionBar.middle (C := C) ⟶
    reference ⋙ SSet.uliftFunctor.{max u v, v} :=
  OrdinaryResolutionBar.left ≫ Functor.whiskerRight referenceComparison SSet.uliftFunctor

lemma reference_kan (R : RightResolutionMapping.Index C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (reference.obj R)) :=
  AnodyneKanReplacement.terminal_rlp _

lemma toReference_localized_isIso (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((toReference (C := C)).app R)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have : IsIso (Q.map ((OrdinaryResolutionBar.left (C := C)).app R)) := by
    change IsIso ((OrdinaryResolutionBar.leftAnodyneIso (C := C)).hom.app R)
    infer_instance
  have : IsIso (Q.map (SSet.uliftFunctor.{max u v, v}.map
      ((referenceComparison (C := C)).app R))) :=
    UniverseLift.anodyneQ_lift_inverts _ (AnodyneKanReplacement.unit_anodyne _)
  change IsIso (Q.map ((OrdinaryResolutionBar.left (C := C)).app R ≫
    SSet.uliftFunctor.{max u v, v}.map ((referenceComparison (C := C)).app R)))
  rw [Q.map_comp]
  infer_instance

abbrev enlarged : RightResolutionMapping.Index C ⥤ SSet.{max u v} :=
  SmallTargetKernelQuotient.middle (toReference (C := C))

abbrev relation : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence (enlarged (C := C)) :=
  SmallTargetKernelQuotient.relation toReference

lemma quotient_small (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((relation (C := C)).rel R n)) :=
  SmallTargetKernelQuotient.quotient_small toReference R n

lemma quotient_boundary_rlp (R : RightResolutionMapping.Index C) :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection (relation (C := C))).app R) :=
  SmallTargetKernelQuotient.quotient_boundary_rlp toReference reference_kan
    toReference_localized_isIso R

abbrev functor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  SmallDiagramQuotient.functor relation quotient_small

lemma terminal_rlp (R : RightResolutionMapping.Index C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((functor (C := C)).obj R)) :=
  SmallDiagramQuotient.kan relation quotient_small quotient_boundary_rlp R
    (SmallTargetKernelQuotient.middle_kan toReference reference_kan R)

def left : OrdinaryResolutionBar.middle (C := C) ⟶
    functor ⋙ SSet.uliftFunctor.{max u v, v} :=
  SmallTargetKernelQuotient.unit toReference ≫
    SmallDiagramQuotient.projection relation quotient_small

lemma left_localized_isIso (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((left (C := C)).app R)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have : IsIso (Q.map ((SmallTargetKernelQuotient.unit (toReference (C := C))).app R)) :=
    Localization.inverts Q _ _ (SmallTargetKernelQuotient.unit_anodyne toReference R)
  have : IsIso (Q.map ((SmallDiagramQuotient.projection
      (relation (C := C)) quotient_small).app R)) :=
    MonoRightLiftingContraction.image_isIso _
      (SmallDiagramQuotient.projection_mono_rlp relation quotient_small quotient_boundary_rlp R)
      Q (Localization.inverts Q _)
  change IsIso (Q.map (_ ≫ _))
  rw [Q.map_comp]
  infer_instance

def leftImageIso {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    OrdinaryResolutionBar.middle (C := C) ⋙ L ≅
      (functor ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L := by
  have (R : RightResolutionMapping.Index C) : IsIso ((Functor.whiskerRight
      (SmallTargetKernelQuotient.unit (toReference (C := C))) L).app R) :=
    hL _ (SmallTargetKernelQuotient.unit_anodyne toReference R)
  have : IsIso (Functor.whiskerRight (SmallTargetKernelQuotient.unit
      (toReference (C := C))) L) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerRight (SmallTargetKernelQuotient.unit toReference) L) ≪≫
    SmallDiagramQuotient.imageIso relation quotient_small quotient_boundary_rlp L hL

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def baseComparisonIso {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    (functor (C := C) ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
      (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L := by
  have := OrdinaryBarMappingComparison.right_isIso (C := C) hcof hfib L hL
  exact (leftImageIso L hL).symm ≪≫
    asIso (Functor.whiskerRight OrdinaryResolutionBar.right L)

include hcof hfib in
lemma map_weakEquivalence {R S : RightResolutionMapping.Index C} (f : R ⟶ S)
    (hs : weakEquivalences C ((RightResolutionMapping.projection.map f).1.unop))
    (ht : weakEquivalences C ((RightResolutionMapping.projection.map f).2)) :
    weakEquivalences SSet.{v} ((functor (C := C)).map f) := by
  apply (UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib _).mpr
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  exact (NatIso.isIso_map_iff (baseComparisonIso hcof hfib Q (Localization.inverts Q _)) f).mpr
    (OrdinaryBarBaseInvariance.localized_map_isIso hcof hfib _ hs ht)

end SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient
