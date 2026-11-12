module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterEvaluation

/-!
# 中断した任意モデル源への一般化：NerveMovingFamilyFit

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole family compatibility derived from actual objectwise boundary equations。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0481][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0481
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole family compatibility derived from actual objectwise boundary equations
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveMovingFamilyFit
variable {D : Type uD} [Category.{vD} D]
  (K : D ⥤ SSet.{max w v}) (F : D ⥤ SSet.{v})

/-- Every coherent boundary recovers its entire degree-zero system from its actual evaluations. -/
lemma lower_recover (a : NerveMovingParameter.System K F) :
    NerveMovingParameter.vertices K F (NerveMovingParameter.evaluate K F a) =
      Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) a := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s, hs⟩
  rcases s with @⟨m, c⟩
  rcases m with ⟨⟨n⟩⟩
  change n < 1 at hs
  have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hs)
  subst n
  change ComposableArrows D 0 at c
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact (NerveMovingParameter.vertices_at_object K F _ d).trans
    (NerveBiparameterMaps.name_evaluate K F a d)

variable (L : D ⥤ SSet.{max w v}) (i : L ⟶ K)
  (families : ∀ d, K.obj d ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj d))

lemma vertices_restriction : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    NerveMovingParameter.vertices L F (fun d => i.app d ≫ families d) := by
  apply NatTrans.ext
  funext s
  rcases s with ⟨s, hs⟩
  rcases s with @⟨m, c⟩
  rcases m with ⟨⟨n⟩⟩
  change n < 1 at hs
  have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hs)
  subst n
  change ComposableArrows D 0 at c
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective c
  change (NerveMovingParameter.vertices K F families).app
    ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩ ≫
      (NerveMovingParameterRelative.restriction L K i F).app
        (ofChain (ComposableArrows.mk₀ d)) = _
  rw [NerveMovingParameter.vertices_at_object, NerveMovingParameter.vertices_at_object,
    NerveMovingParameterRelative.restriction_app]
  exact RelativeChoiceSpace.name_precomp (i.app d) (families d)

variable (target : NerveMovingParameter.System L F)
  (he : ∀ d, i.app d ≫ families d = NerveMovingParameter.evaluate L F target d)

include he in
lemma compatible : NerveMovingParameter.vertices K F families ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveMovingParameterRelative.restriction L K i F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1) target := by
  rw [vertices_restriction, funext he, lower_recover]

variable (hp : ∀ d, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (F.obj d)) (hi : ∀ d, Mono (i.app d))

/-- Objectwise equations supply the lower-system fit, with no extra coherent fit input. -/
def extend : NerveMovingParameter.System K F :=
  NerveMovingParameterRelative.extendFamilies L K i F hp hi target families
    (compatible K F L i families target he)

lemma extend_evaluate (d : D) : NerveMovingParameter.evaluate K F
    (extend K F L i families target he hp hi) d = families d :=
  NerveMovingParameterRelative.extendFamilies_evaluate _ _ _ _ _ _ _ _ _ d

lemma extend_boundary : extend K F L i families target he hp hi ≫
    NerveMovingParameterRelative.restriction L K i F = target :=
  NerveMovingParameterRelative.extendFamilies_boundary _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveMovingFamilyFit
