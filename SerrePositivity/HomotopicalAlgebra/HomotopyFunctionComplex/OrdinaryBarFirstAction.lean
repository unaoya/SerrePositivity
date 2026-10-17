module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFirstAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole first-endpoint actions on the actual bar comma chains。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0163][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0163
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole first-endpoint actions on the actual bar comma chains

Every face uses the actual prefix comparison and its raw Hom map. The
reference output is fixed, while both target resolutions change.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstAction
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

abbrev output : SSet.{v} := MixedResolutionLiftAction.output R.1.unop.inner R.2.unop.inner
abbrev input (d : OrdinaryBarCenters.Comma R) : SSet.{v} :=
  OrdinaryResolutionPairs.raw.obj d.left

lemma output_map {d e : (OrdinaryBarCenters.Comma R)ᵒᵖ} (f : d ⟶ e) :
    (MixedResolutionCenters.output C).map ((OrdinaryBarCenters.centers R).map f) =
      𝟙 (output R) := by
  change MixedDiagonalHom.map (FramedResolution.diagonal.map (𝟙 R.1.unop))
    (FramedResolution.diagonal.map (𝟙 R.2.unop)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact MixedDiagonalHom.map_id _ _

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

def action {n : ℕ} (c : ComposableArrows (OrdinaryBarCenters.Comma R) n)
    (t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ input R (c.obj 0)) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ output R :=
  MixedResolutionCenters.action C (OrdinaryBarCenters.center R (c.obj 0))
    (a.app (ofChain c)) (b.app (ofChain c)) t

lemma operator {n m : ℕ} (c : ComposableArrows (OrdinaryBarCenters.Comma R) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ input R (c.obj 0)) :
    SSet.stdSimplex.map θ ≫ action R a b c t =
      action R a b ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        ((SSet.stdSimplex.map θ ≫ t) ≫ OrdinaryResolutionPairs.raw.map
          (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).left) := by
  let f := (OrdinaryBarCenters.centers R).map
    (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).op
  have ha := NerveFirstChoice.reindex_compatibility (OrdinaryBarCenters.leftChoices R) a c θ
  have hb := NerveFirstChoice.reindex_compatibility (OrdinaryBarCenters.rightChoices R) b c θ
  change SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
    a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (MixedResolutionCenters.leftChoices C).map f at ha
  change SSet.stdSimplex.map θ ≫ b.app (ofChain c) =
    b.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (MixedResolutionCenters.rightChoices C).map f at hb
  unfold action
  rw [MixedResolutionCenters.action_parameter, ha, hb,
    MixedResolutionCenters.action_transport, output_map]
  change action R a b ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
      ((SSet.stdSimplex.map θ ≫ t) ≫ OrdinaryResolutionPairs.raw.map
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).left) ≫ 𝟙 (output R) = _
  exact Category.comp_id _

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstAction
