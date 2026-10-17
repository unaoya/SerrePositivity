module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedSmallAction
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.NerveSmallAction

/-!
# 中断した任意モデル源への一般化：ResolutionMixedActionOperators

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All external simplex operators on the same small mixed triangle and facet actions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0312][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0312
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All external simplex operators on the same small mixed triangle and facet actions
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedSmallFamilies ResolutionMixedSmallAction

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev inputMap {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C) :=
  NerveSmallAction.inputMap C (cornerD C) c θ Z
abbrev outputMap {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C) :=
  NerveSmallAction.outputMap C hcof hfib (cornerD C) c θ Z

/-- Every external face and degeneracy uses the actual final cube's two resolution maps. -/
lemma action_operator (side : Bool) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ action C hcof hfib side c Z t =
    ResolutionArrowActionTransport.kan C hcof hfib
      ((cornerD C).obj ((NerveSmallAction.reindexChain c θ).obj (Fin.last m))) Z
      (NerveSmallAction.prefixParameter (smallParameter C) c θ ≫
        family C hcof hfib side (NerveSmallAction.reindexChain c θ))
      ((NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ t) ≫ inputMap C c θ Z) ≫
        outputMap C hcof hfib c θ Z :=
  NerveSmallAction.operator C hcof hfib (cornerD C) (smallParameter C)
    (system C hcof hfib side) c θ Z t

lemma action_operator_of_input (side : Bool) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z)
    (t' : chainParameter C (NerveSmallAction.reindexChain c θ) ⟶
      input C ((NerveSmallAction.reindexChain c θ).obj (Fin.last m)) Z)
    (ht : (NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ t) ≫ inputMap C c θ Z =
      NerveSmallAction.prefixParameter (smallParameter C) c θ ≫ t') :
    NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ action C hcof hfib side c Z t =
    (NerveSmallAction.prefixParameter (smallParameter C) c θ ≫
      action C hcof hfib side (NerveSmallAction.reindexChain c θ) Z t') ≫
        outputMap C hcof hfib c θ Z :=
  NerveSmallAction.operator_of_input C hcof hfib (cornerD C) (smallParameter C)
    (system C hcof hfib side) c θ Z t t' ht

/-- The same operator law holds for every one of the already fixed whole facet systems. -/
lemma faceAction_operator_of_input (side : Bool) (k : Fin 3) {n m : ℕ}
    (c : ComposableArrows (Index C) n) (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : faceParameter C c ⟶ input C (c.obj (Fin.last n)) Z)
    (t' : faceParameter C (NerveSmallAction.reindexChain c θ) ⟶
      input C ((NerveSmallAction.reindexChain c θ).obj (Fin.last m)) Z)
    (ht : (NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫ t) ≫
      inputMap C c θ Z = NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫ t') :
    NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫
      faceAction C hcof hfib side k c Z t =
    (NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫
      faceAction C hcof hfib side k (NerveSmallAction.reindexChain c θ) Z t') ≫
        outputMap C hcof hfib c θ Z :=
  NerveSmallAction.operator_of_input C hcof hfib (cornerD C) (smallIntervalParameter C)
    (faceSystem C hcof hfib side k) c θ Z t t' ht

omit [ModelCategory SSet.{v}] in
lemma face_prefix (k : Fin 3) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫
      ((smallFaceMap C k).app (c.obj (θ.toOrderHom 0)) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m)) =
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk m)) ≫
      NerveSmallAction.prefixParameter (smallParameter C) c θ := by
  change _ ▷ _ ≫ _ ▷ _ = _ ▷ _ ≫ _ ▷ _
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  exact congrArg (fun f => f ▷ SSet.stdSimplex.obj (SimplexCategory.mk m))
    ((smallFaceMap C k).naturality (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))))

omit [ModelCategory SSet.{v}] in
lemma face_operator (k : Fin 3) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk m)) ≫
      NerveSmallAction.operatorParameter (smallParameter C) c θ =
    NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫
      ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) :=
  whisker_exchange ((smallFaceMap C k).app (c.obj 0)) (SSet.stdSimplex.{v}.map θ)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators
