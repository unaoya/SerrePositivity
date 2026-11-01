module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardPathNormalizeNaturality
public import SerrePositivity.InfinityCategories.ModelBridge.ForwardPathModelPropagation

/-!
# 端点の正規化とモデル圏の弱同値

概要：正規化後も各頂点の自明な置換と全縦弱同値を保持する。
方針：元のブロックの伝播定理と、端点の移送同型との合成を使う。
規約：proper 性・cofibrancy は仮定しない。長さ零も含む。
使われ方：左右の forward ブロックを貼る際の縦弱同値の条件。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n : ℕ}

lemma normalizedPullbackProjection_trivialFibration (s : TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) (i : Fin (n + 1)) :
    trivialFibrations C ((normalizedPullbackProjection s).app i) := by
  rw [normalizedPullbackProjection_app]
  exact (trivialFibrations C).comp_mem _ _ ((trivialFibrations C).of_isIso _)
    (pullbackProjection_trivialFibration s hs i)

lemma normalizedPushoutInclusion_trivialCofibration (s : InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) (i : Fin (n + 1)) :
    trivialCofibrations C ((normalizedPushoutInclusion s).app i) := by
  rw [normalizedPushoutInclusion_app]
  exact (trivialCofibrations C).comp_mem _ _ (pushoutInclusion_trivialCofibration s hs i)
    ((trivialCofibrations C).of_isIso _)

lemma normalizedPullbackComparison_weakEquivalence {s t : TerminalReplacement C n}
    (m : s ⟶ t) (hs : trivialFibrations C s.hom) (ht : trivialFibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.right.app i)) (i : Fin (n + 1)) :
    weakEquivalences C ((normalizedPullbackComparison m).app i) := by
  rw [normalizedPullbackComparison_app]
  exact (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso _)
    ((weakEquivalences C).comp_mem _ _ (pullbackComparison_weakEquivalence m hs ht hm i)
      ((weakEquivalences C).of_isIso _))

lemma normalizedPushoutComparison_weakEquivalence {s t : InitialReplacement C n}
    (m : s ⟶ t) (hs : trivialCofibrations C s.hom) (ht : trivialCofibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.left.app i)) (i : Fin (n + 1)) :
    weakEquivalences C ((normalizedPushoutComparison m).app i) := by
  rw [normalizedPushoutComparison_app]
  exact (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso _)
    ((weakEquivalences C).comp_mem _ _ (pushoutComparison_weakEquivalence m hs ht hm i)
      ((weakEquivalences C).of_isIso _))

end SerrePositivity.EInfinity.Hammock.ForwardPath
