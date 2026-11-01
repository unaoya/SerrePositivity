module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathEndpoints
public import SerrePositivity.InfinityCategories.ModelBridge.WeakThreeArrow

/-!
# 元の長い forward ブロックへの自明な置換の伝播

概要：自明 fibration・自明 cofibration の置換は、元の全頂点と全縦弱同値を保つ。
方針：元の全頂点の pullback・pushout の射は自明であり、比較は二つのうち三つで反映。
規約：モデル圏の left/right proper 性・元の対象の cofibrancy は要求しない。
使われ方：backward 列の挿入の関手的比較に使う左右の forward ブロック。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n : ℕ}

lemma pullbackProjection_trivialFibration (s : TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) (i : Fin (n + 1)) :
    trivialFibrations C ((pullbackProjection s).app i) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback (terminalLeg s.right i) s.hom).flip hs

lemma pushoutInclusion_trivialCofibration (s : InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) (i : Fin (n + 1)) :
    trivialCofibrations C ((pushoutInclusion s).app i) :=
  MorphismProperty.of_isPushout (IsPushout.of_hasPushout s.hom (initialLeg s.left i)).flip hs

lemma pullbackComparison_weakEquivalence {s t : TerminalReplacement C n} (m : s ⟶ t)
    (hs : trivialFibrations C s.hom) (ht : trivialFibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.right.app i)) (i : Fin (n + 1)) :
    weakEquivalences C ((pullbackComparison m).app i) := by
  apply (weakEquivalences C).of_postcomp _ (pullback.fst (terminalLeg t.right i) t.hom)
    (pullbackProjection_trivialFibration t ht i).2
  change weakEquivalences C (pullbackComparisonApp m i ≫
    pullback.fst (terminalLeg t.right i) t.hom)
  rw [pullbackComparisonApp_fst]
  exact (weakEquivalences C).comp_mem _ _ (pullbackProjection_trivialFibration s hs i).2 (hm i)

lemma pushoutComparison_weakEquivalence {s t : InitialReplacement C n} (m : s ⟶ t)
    (hs : trivialCofibrations C s.hom) (ht : trivialCofibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.left.app i)) (i : Fin (n + 1)) :
    weakEquivalences C ((pushoutComparison m).app i) := by
  apply (weakEquivalences C).of_precomp (pushout.inr s.hom (initialLeg s.left i)) _
    (pushoutInclusion_trivialCofibration s hs i).2
  change weakEquivalences C (pushout.inr s.hom (initialLeg s.left i) ≫ pushoutComparisonApp m i)
  rw [pushoutComparisonApp_inr]
  exact (weakEquivalences C).comp_mem _ _ (hm i) (pushoutInclusion_trivialCofibration t ht i).2

end SerrePositivity.EInfinity.Hammock.ForwardPath
