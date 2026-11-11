module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameter

/-!
# 中断した任意モデル源への一般化：NerveMovingParameterRelative

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Retaining coherent moving boundaries in changing parameter diagrams。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0484][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0484
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Retaining coherent moving boundaries in changing parameter diagrams
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveMovingParameterRelative
variable {D : Type uD} [Category.{vD} D]
  (L K : D ⥤ SSet.{max w v}) (i : L ⟶ K) (F : D ⥤ SSet.{v})

def restriction : NerveMovingParameter.values K F ⟶ NerveMovingParameter.values L F :=
  Functor.whiskerLeft (NerveBiparameter.endpoints D)
    (Functor.whiskerRight (NatTrans.prod (NatTrans.op i) (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} F)))
      (Functor.uncurry.obj MonoidalClosed.internalHom))

lemma restriction_app (s : Index D) : (restriction L K i F).app s =
    (pre (i.app (NerveSimplexStart.start s))).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (endpoint s))) := by
  change (pre (i.app (NerveSimplexStart.start s))).app
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (endpoint s))) ≫
    (ihom (L.obj (NerveSimplexStart.start s))).map
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (endpoint s)))) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

variable (hp : ∀ d, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (F.obj d))
  (hi : ∀ d, Mono (i.app d))

include hp hi in
lemma rightLifting : ∀ s, (MorphismProperty.monomorphisms SSet.{max w v}).rlp
    ((restriction L K i F).app s) := by
  intro s A B j hj
  have : Mono j := hj
  have : Mono (i.app (NerveSimplexStart.start s)) := hi _
  rw [restriction_app]
  exact LargeParameterRelativeChoice.restriction_lifting (hp (endpoint s)) _ j

variable (target : NerveMovingParameter.System L F) (n : ℕ)
  (old : NerveMovingParameter.LowerSystem K F n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (restriction L K i F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) target)

/-- Keep the entire moving boundary system and the entire prescribed lower parameter system. -/
def extend : NerveMovingParameter.System K F :=
  NerveDiagramExtension.extend (NerveMovingParameter.values K F) (NerveMovingParameter.values L F)
    (restriction L K i F) (NerveMovingParameter.values_inverts K F)
    (NerveMovingParameter.values_inverts L F) (rightLifting L K i F hp hi)
    target n old hboundary

lemma extend_boundary : extend L K i F hp hi target n old hboundary ≫ restriction L K i F =
    target := NerveDiagramExtension.extend_boundary _ _ _ _ _ _ _ _ _ _

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend L K i F hp hi target n old hboundary) = old :=
  NerveDiagramExtension.extend_restrict _ _ _ _ _ _ _ _ _ _

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend L K i F hp hi target n old hboundary).app s.obj = old.app s :=
  congr_app (extend_restrict L K i F hp hi target n old hboundary) s

variable (families : ∀ d, K.obj d ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj d))
  (hfamilies : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) (restriction L K i F) =
      Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) target)

def extendFamilies : NerveMovingParameter.System K F :=
  extend L K i F hp hi target 1 (NerveMovingParameter.vertices K F families) hfamilies

lemma extendFamilies_evaluate (d : D) :
    NerveMovingParameter.evaluate K F (extendFamilies L K i F hp hi target families hfamilies) d =
      families d := by
  change uncurry' (RelativeChoiceSpace.pointUnitIso.inv ≫
    (extendFamilies L K i F hp hi target families hfamilies).app
      (ofChain (ComposableArrows.mk₀ d))) = families d
  rw [show (extendFamilies L K i F hp hi target families hfamilies).app
      (ofChain (ComposableArrows.mk₀ d)) = RelativeChoiceSpace.name (families d) from
    (extend_component L K i F hp hi target 1 (NerveMovingParameter.vertices K F families) hfamilies
      ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩).trans
        (NerveMovingParameter.vertices_at_object K F families d)]
  simp only [RelativeChoiceSpace.name, Iso.inv_hom_id_assoc, uncurry'_curry']

lemma extendFamilies_boundary : extendFamilies L K i F hp hi target families hfamilies ≫
    restriction L K i F = target := extend_boundary _ _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveMovingParameterRelative
