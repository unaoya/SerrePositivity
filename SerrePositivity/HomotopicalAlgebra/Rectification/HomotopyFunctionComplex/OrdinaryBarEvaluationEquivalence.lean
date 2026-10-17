module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRightEvaluation
public import Mathlib.CategoryTheory.EpiMono

/-!
# 中断した任意モデル源への一般化：OrdinaryBarEvaluationEquivalence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The original ordinary resolution-bar evaluation is inverted。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0162][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0162
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The original ordinary resolution-bar evaluation is inverted

The reference-to-row interval controls row followed by evaluation. Both
original simplex augmentations control the other composite. Only the
original small simplicial model is used; the large value universe has no model.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence
open OrdinaryBarReferenceRowHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma nerveAugmentation_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveAugmentation R)) := by
  have hf := (AnodyneHomotopy.weakEquivalences_iff_anodyneQ_isIso hcof hfib
    (OrdinaryBarReferenceRows.augmentation R)).mp
      (MixedResolutionComparison.comparison_weakEquivalence hcof hfib R)
  exact UniverseLift.anodyneQ_map_isIso_of_small.{max u v, v} _
    (SimplexNerve.map_localized_isIso _ hf)

include hcof hfib in
lemma reference_evaluation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (referenceComposite R ≫ OrdinaryBarEvaluation.evaluation R a b)) := by
  have haug := UniverseLift.anodyneQ_map_isIso_of_small.{max u v, v}
    (SimplexNerve.augmentation.app (OrdinaryBarReferenceRows.raw R))
    (SimplexNerve.augmentation_localized_isIso _)
  have : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{max u v, v}.map
      (SimplexNerve.augmentation.app (OrdinaryBarReferenceRows.raw R)))) := haug
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarReference.sectionMap R ≫ OrdinaryBarEvaluation.evaluation R a b)) :=
    OrdinaryBarReference.section_evaluation_isIso R a b hcof hfib
  rw [referenceComposite, Category.assoc, Category.assoc,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

include hcof hfib in
lemma row_evaluation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarEvaluatedEndpoint.rowNerveMap R ≫ OrdinaryBarEvaluation.evaluation R a b)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have h := AnodyneHomotopy.map_homotopy_eq Q (Localization.inverts Q SSet.anodyneExtensions)
    (HomotopyClasses.postHomotopy (OrdinaryBarEvaluation.evaluation R a b) (homotopy R))
  rw [reference_factorization, row_factorization, Category.assoc] at h
  rw [Q.map_comp (nerveAugmentation R)
    (OrdinaryBarEvaluatedEndpoint.rowNerveMap R ≫ OrdinaryBarEvaluation.evaluation R a b)] at h
  have : IsIso (Q.map (referenceComposite R ≫ OrdinaryBarEvaluation.evaluation R a b)) :=
    reference_evaluation_isIso R a b hcof hfib
  have : IsIso (Q.map (nerveAugmentation R)) := nerveAugmentation_isIso R hcof hfib
  have hc : IsIso (Q.map (nerveAugmentation R) ≫ Q.map
      (OrdinaryBarEvaluatedEndpoint.rowNerveMap R ≫ OrdinaryBarEvaluation.evaluation R a b)) :=
    h ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hc

include a b hcof hfib in
lemma row_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarEvaluatedEndpoint.rowNerveMap R)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  let e := Q.map (OrdinaryBarEvaluatedEndpoint.evaluationNerveMap R a b)
  let r := Q.map (OrdinaryBarEvaluatedEndpoint.rowNerveMap R)
  let t := Q.map (OrdinaryBarEvaluation.evaluation R a b)
  have her : IsIso (e ≫ r) := by
    have h := OrdinaryBarEvaluatedEndpoint.image_eq R a b Q
      (Localization.inverts Q SSet.anodyneExtensions)
    exact h ▸ OrdinaryBarAugmentationEquivalences.large_localized_isIso R
  have hrt : IsIso (r ≫ t) := by
    rw [← Q.map_comp]
    exact row_evaluation_isIso R a b hcof hfib
  have : Mono r := mono_of_mono r t
  have : IsSplitEpi r := IsSplitEpi.mk'
    { section_ := inv (e ≫ r) ≫ e
      id := by rw [Category.assoc, IsIso.inv_hom_id] }
  exact isIso_of_mono_of_isSplitEpi r

include hcof hfib in
lemma evaluation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarEvaluation.evaluation R a b)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluatedEndpoint.rowNerveMap R)) :=
    row_isIso R a b hcof hfib
  have h := row_evaluation_isIso R a b hcof hfib
  rw [CategoryTheory.Functor.map_comp] at h
  exact (isIso_comp_left_iff _ _).mp h

include hcof hfib in
lemma evaluation_image_isIso {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (OrdinaryBarEvaluation.evaluation R a b)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _ (evaluation_isIso R a b hcof hfib)

include a b hcof hfib in
lemma right_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    ((OrdinaryResolutionBar.right (C := C)).app R)) :=
  (OrdinaryBarRightEvaluation.right_isIso_iff_evaluation R a b hcof hfib).mpr
    (evaluation_isIso R a b hcof hfib)

include hcof hfib in
lemma right_natural_isIso : IsIso (Functor.whiskerRight
    (OrdinaryResolutionBar.right (C := C)) AnodyneHomotopy.anodyneQ) := by
  have : ∀ R, IsIso ((Functor.whiskerRight (OrdinaryResolutionBar.right (C := C))
      AnodyneHomotopy.anodyneQ).app R) := fun R =>
    right_isIso R (OrdinaryBarCenters.leftSystem R hcof)
      (OrdinaryBarCenters.rightSystem R hcof) hcof hfib
  exact NatIso.isIso_of_isIso_app _

include hcof hfib in
lemma ordinaryRight_natural_isIso : IsIso (Functor.whiskerRight
    (OrdinaryResolutionBar.ordinaryRight (C := C)) AnodyneHomotopy.anodyneQ) :=
  (OrdinaryResolutionBar.right_natural_image_isIso_iff AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).mp
      (right_natural_isIso (C := C) hcof hfib)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence
