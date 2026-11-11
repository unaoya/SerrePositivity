module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveNaturalBoundary

/-!
# 中断した任意モデル源への一般化：NerveRelativeNaturalBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Moving relative extension with a prescribed strict natural boundary。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0492][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0492
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Moving relative extension with a prescribed strict natural boundary

The low-degree compatibility is derived from the actual objectwise
boundary equations. No coherent boundary or compatibility is left as an
additional input: the natural boundary supplies its whole canonical system.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary
variable {D : Type uD} [Category.{vD} D]
  (L K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v}) (i : L ⟶ K)
  (b : L ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} F)
  (families : ∀ d, K.obj d ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj d))
  (he : ∀ d, i.app d ≫ families d = b.app d)

include he in
lemma compatible : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveNaturalBoundary.ofNatTrans L (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) b) := by
  apply NatTrans.ext
  funext s
  have hzero : dimension s.obj = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.property)
  let c := eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F).obj
    (NerveMovingParameter.start_eq_endpoint_zero s.obj hzero))
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.name
    (families (NerveSimplexStart.start s.obj) ≫ c)) ≫
      (NerveMovingParameterRelative.restriction L K i F).app s.obj = _
  rw [NerveMovingParameterRelative.restriction_app]
  apply Eq.trans ?_ (NerveNaturalBoundary.ofNatTrans_zero L
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) b s.obj hzero).symm
  have hn : RelativeChoiceSpace.name (families (NerveSimplexStart.start s.obj) ≫ c) ≫
      (pre (i.app (NerveSimplexStart.start s.obj))).app
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (endpoint s.obj))) =
    RelativeChoiceSpace.name (b.app (NerveSimplexStart.start s.obj) ≫ c) := by
    apply (RelativeChoiceSpace.name_precomp (i.app (NerveSimplexStart.start s.obj))
      (families (NerveSimplexStart.start s.obj) ≫ c)).trans
    exact congrArg RelativeChoiceSpace.name
      ((Category.assoc _ _ _).symm.trans (congrArg (fun e => e ≫ c) (he _)))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun e => SSet.stdSimplex.isTerminalObj₀.from _ ≫ e) hn)


variable (hp : ∀ d, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (F.obj d)) (hi : ∀ d, Mono (i.app d))

/-- Keep every whole original family and every strict boundary in one all-center system. -/
def extend : NerveMovingParameter.System K F :=
  NerveMovingParameterRelative.extendFamilies L K i F hp hi
    (NerveNaturalBoundary.ofNatTrans L (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) b) families
    (compatible L K F i b families he)

lemma extend_evaluate (d : D) : NerveMovingParameter.evaluate K F
    (extend L K F i b families he hp hi) d = families d :=
  NerveMovingParameterRelative.extendFamilies_evaluate _ _ _ _ _ _ _ _ _ d

lemma extend_boundary : extend L K F i b families he hp hi ≫
    NerveMovingParameterRelative.restriction L K i F =
      NerveNaturalBoundary.ofNatTrans L (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted F) b :=
  NerveMovingParameterRelative.extendFamilies_boundary _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary
