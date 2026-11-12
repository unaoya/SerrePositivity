module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 中断した任意モデル源への一般化：OrdinaryBarPiZero

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual components of the ordinary resolution bar are ordinary localized morphisms。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0204][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0204
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual components of the ordinary resolution bar are ordinary localized morphisms

The source is any model category. Only the original small simplicial model
is used to compare the raw entry with the bar. No large value model is used.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarPiZero
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma entry_localized_isIso (R : OrdinaryResolutionPairs.Index (C := C)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarMappingClasses.entry R)) := by
  let S := MixedBiresolutionComparison.pair R.1.unop R.2.unop
  let a := OrdinaryBarCenters.leftSystem S hcof
  let b := OrdinaryBarCenters.rightSystem S hcof
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (OrdinaryBarEvaluation.evaluation S a b)) :=
    OrdinaryBarEvaluationEquivalence.evaluation_isIso S a b hcof hfib
  have hc := OrdinaryBarReference.section_evaluation_isIso S a b hcof hfib
  rw [CategoryTheory.Functor.map_comp] at hc
  have : IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarReference.sectionMap S)) :=
    (isIso_comp_right_iff _ _).mp hc
  let e : SSet.uliftFunctor.{max u v, v}.obj (OrdinaryResolutionPairs.raw.obj R) ≅
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (OrdinaryResolutionPairs.raw.obj R) :=
    NatIso.ofComponents (fun _ => Equiv.toIso
      { toFun := fun x => ⟨x.down⟩
        invFun := fun x => ⟨x.down⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }) (by intro n m θ; rfl)
  have hs : OrdinaryBarMappingClasses.entry R = e.hom ≫ OrdinaryBarReference.sectionMap S := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [hs, CategoryTheory.Functor.map_comp]
  infer_instance

include hcof hfib in
lemma entry_piZero_bijective (R : OrdinaryResolutionPairs.Index (C := C)) :
    Function.Bijective (SSet.mapπ₀ (OrdinaryBarMappingClasses.entry R)) :=
  PiZeroLocalization.piZero_bijective _ (entry_localized_isIso hcof hfib R)

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

include hcof hfib in
lemma piZeroLabel_injective (b : Cᵒᵖ × C) :
    Function.Injective (OrdinaryBarMappingClasses.piZeroLabel Q b) := by
  intro x y h
  let R := OrdinaryBarLabelSurjectivity.ofBase b
  obtain ⟨x, rfl⟩ := (entry_piZero_bijective hcof hfib R).surjective x
  obtain ⟨y, rfl⟩ := (entry_piZero_bijective hcof hfib R).surjective y
  obtain ⟨⟨f⟩, rfl⟩ := SSet.π₀.mk_surjective x
  obtain ⟨⟨g⟩, rfl⟩ := SSet.π₀.mk_surjective y
  change OrdinaryBarMappingClasses.label Q _ _
      ((OrdinaryBarMappingClasses.entry R).app _ ⟨f⟩) =
    OrdinaryBarMappingClasses.label Q _ _
      ((OrdinaryBarMappingClasses.entry R).app _ ⟨g⟩) at h
  rw [OrdinaryBarMappingClasses.entry_label, OrdinaryBarMappingClasses.entry_label] at h
  exact OrdinaryRawLabelHomotopy.entry_component_eq Q R h

include hcof hfib in
lemma piZeroLabel_bijective (b : Cᵒᵖ × C) :
    Function.Bijective (OrdinaryBarMappingClasses.piZeroLabel Q b) :=
  ⟨piZeroLabel_injective hcof hfib Q b,
    OrdinaryBarLabelSurjectivity.piZeroLabel_surjective Q b⟩

def piZeroEquiv (b : Cᵒᵖ × C) :
    SSet.π₀ (OrdinaryResolutionBar.functor.obj b) ≃ (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  (Equiv.ofBijective _ (piZeroLabel_bijective hcof hfib Q b)).trans
    (LocalizedHomDiagram.equiv Q b)

include hcof hfib Q in
lemma piZero_small (b : Cᵒᵖ × C) :
    Small.{v} (SSet.π₀ ((OrdinaryResolutionBar.functor (C := C)).obj b)) :=
  small_of_injective (piZeroLabel_injective hcof hfib Q b)

lemma piZeroEquiv_mk (R : OrdinaryResolutionPairs.Index (C := C))
    (f : (OrdinaryResolutionPairs.raw.obj R).obj (Opposite.op (SimplexCategory.mk 0))) :
    piZeroEquiv hcof hfib Q _
        (SSet.π₀.mk ((OrdinaryBarMappingClasses.entry R).app _ ⟨f⟩)) =
      (OrdinaryMappingClassLabel.sourceIso Q R (SimplexCategory.mk 0)).inv ≫ Q.map f ≫
        (OrdinaryMappingClassLabel.targetIso Q R (SimplexCategory.mk 0)).inv := by
  change LocalizedHomDiagram.equiv Q _ (OrdinaryBarMappingClasses.label Q _ _ _) = _
  rw [OrdinaryBarMappingClasses.entry_label, OrdinaryMappingClassLabel.label_equiv]

lemma piZeroEquiv_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    piZeroEquiv hcof hfib Q c (SSet.mapπ₀ (OrdinaryResolutionBar.functor.map f) z) =
      Q.map f.1.unop ≫ piZeroEquiv hcof hfib Q b z ≫ Q.map f.2 := by
  change LocalizedHomDiagram.equiv Q c
    (OrdinaryBarMappingClasses.piZeroLabel Q c (SSet.mapπ₀ _ z)) = _
  rw [OrdinaryBarMappingClasses.piZeroLabel_base, LocalizedHomDiagram.types_map]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarPiZero
