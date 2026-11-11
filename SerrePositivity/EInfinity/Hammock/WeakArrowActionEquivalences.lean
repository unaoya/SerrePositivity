module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakArrowActionHomotopies
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 指定射の前後合成は元の hammock の弱ホモトピー同値

概要：元の forward 射と backward 列による前後合成の両方を反転する。
方針：実際の両逆ホモトピーを anodyne 局所化での同型に送り、Kan 標的で判定する。
規約：始域・終域の Kan 性や単体集合のモデル構造は要求しない。
使われ方：端点の移動を含む相対自然変換の比較。
-/

@[expose] public section
universe u v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WeakArrow
open CategoryTheory SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g) (A : C)
  {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

def postcompositionIso : L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W A X) ≅ L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W A Y) where
  hom := L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g))
  inv := L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg))
  hom_inv_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postSourceHomotopy g hg A)).symm.trans
      (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postTargetHomotopy g hg A)).trans
      (L.map_id _)

def precompositionIso : L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X A) ≅ L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y A) where
  hom := L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) A)
  inv := L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) A)
  hom_inv_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.preSourceHomotopy g hg A)).symm.trans
      (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.preTargetHomotopy g hg A)).trans
      (L.map_id _)

include hg in
lemma postcompose_forward_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (postcompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

lemma postcompose_backward_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (postcompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_inv

include hg in
lemma precompose_forward_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) A) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (precompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_inv

lemma precompose_backward_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) A) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (precompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.EInfinity.Hammock.WeakArrow
