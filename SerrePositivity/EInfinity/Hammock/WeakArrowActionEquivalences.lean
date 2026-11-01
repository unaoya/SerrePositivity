module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WeakArrowActionHomotopies
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

def postcompositionIso : L.obj (colimitGraph W A X) ≅ L.obj (colimitGraph W A Y) where
  hom := L.map (postcomposePointMap A (arrowMap W g))
  inv := L.map (postcomposePointMap A (backwardMap g hg))
  hom_inv_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (postSourceHomotopy g hg A)).symm.trans
      (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (postTargetHomotopy g hg A)).trans
      (L.map_id _)

def precompositionIso : L.obj (colimitGraph W X A) ≅ L.obj (colimitGraph W Y A) where
  hom := L.map (precomposePointMap (backwardMap g hg) A)
  inv := L.map (precomposePointMap (arrowMap W g) A)
  hom_inv_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (preSourceHomotopy g hg A)).symm.trans
      (L.map_id _)
  inv_hom_id := by
    rw [← L.map_comp]
    exact (AnodyneHomotopy.map_homotopy_eq L hL (preTargetHomotopy g hg A)).trans
      (L.map_id _)

include hg in
lemma postcompose_forward_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (postcomposePointMap A (arrowMap W g)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (postcompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

lemma postcompose_backward_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (postcomposePointMap A (backwardMap g hg)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (postcompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_inv

include hg in
lemma precompose_forward_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (precomposePointMap (arrowMap W g) A) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (precompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_inv

lemma precompose_backward_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (precomposePointMap (backwardMap g hg) A) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (precompositionIso g hg A AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.EInfinity.Hammock.WeakArrow
