module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterEvaluation
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftTensor

/-!
# 中断した任意モデル源への一般化：NerveSmallFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Read whole moving coherent systems back as original-universe chain families。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0494][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0494
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Read whole moving coherent systems back as original-universe chain families

The indexing category may be large. Each entire finite chain family, including
its full small parameter, lives in the original universe of its values.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveSmallFamilies
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) F)

/-- The full small parameter and full chain simplex are retained before applying an action. -/
def family {n : ℕ} (c : ComposableArrows D n) :
    K.obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      F.obj (c.obj (Fin.last n)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor (uncurry (a.app (ofChain c)))

lemma family_lift {n : ℕ} (c : ComposableArrows D n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{w} (family K F a c) = uncurry (a.app (ofChain c)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_lowerSimplexTensor _

lemma family_naturality {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    K.obj (c.obj 0) ◁ SSet.stdSimplex.map θ ≫ family K F a c =
      ((K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m) ≫
        family K F a ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) := by
  let initialMap := c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))
  let tail := c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))
  have h0 : SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
      (a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (K.map initialMap))).app
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (c.obj (θ.toOrderHom (Fin.last m)))))) ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (K.obj (c.obj 0)))).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (F.map tail)) :=
    NerveBiparameter.reindex_compatibility
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} F) a c θ
  have h := congrArg (fun k : SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk m) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (K.obj (c.obj 0)))).obj
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (c.obj (Fin.last n)))) => uncurry k) h0
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_pre_app] at h
  apply (show Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{w}
    (K := K.obj (c.obj 0)) (P := F.obj (c.obj (Fin.last n))) (n := m)) from
    by
      intro f g hfg
      have he := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor z) hfg
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor_simplexTensorMap] using he)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_operator, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_target,
    ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_source, family_lift, family_lift]
  exact h

/-- Object evaluation is also an entire map of original small simplicial sets. -/
def point (d : D) : K.obj d ⟶ F.obj d :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (NerveMovingParameter.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) F a d)

lemma point_lift (d : D) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (point K F a d) =
    NerveMovingParameter.evaluate (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) F a d :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower _

lemma family_restrict (L : D ⥤ SSet.{v}) (i : L ⟶ K) {n : ℕ}
    (c : ComposableArrows D n) :
    family L F (NerveBiparameterMaps.restrict (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} L)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} F)
      (Functor.whiskerRight i SSet.uliftFunctor.{w, v}) a) c =
      (i.app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family K F a c := by
  apply (show Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{w}
    (K := L.obj (c.obj 0)) (P := F.obj (c.obj (Fin.last n))) (n := n)) from
    by
      intro f g hfg
      have he := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor z) hfg
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor_simplexTensorMap] using he)
  rw [family_lift, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap_source, family_lift]
  exact uncurry_pre_app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (F.obj (c.obj (Fin.last n))))
    (a.app (ofChain c)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (i.app (c.obj 0)))

end SerrePositivity.SimplicialModel.NerveSmallFamilies
