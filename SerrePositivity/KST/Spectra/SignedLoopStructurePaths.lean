module

public import SerrePositivity.KST.Spectra.SignedAdjointCompositionPaths
public import SerrePositivity.KST.Spectra.SignedLoopSequence

/-!
概要：元の Kan 随伴の符号付き loop 列の構造比較を、普遍的な基点固定区間の有限鎖で作る。
方針：元の随伴の厳密な式を二つの交換符号区間に照合し、評価で uncurry する。
規約：指定部分への垂直性は別工程。使われ方：元の全 Hom の構造比較の区間データ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 元の随伴構造射の比較を、普遍的な交換符号区間から作った実際の有限鎖で実現する。 -/
lemma kanAdjoint_signedLoopTail_basedChain {X : KanSequence.{u}}
    (hX : X.OmegaCondition) (n : ℕ) :
    PointedMapping.VerticalChain (PointedObject.toPoint ((signedLoopTail X).level (n + 1)).space)
      (PointedSimplicialSet.circle.{u} ◁ kanAdjoint X n ≫ (signedLoopTail X).sigma n)
      (X.sigma n ≫ kanAdjoint X (n + 1)) := by
  have hc : PointedMapping.VerticalChain
      (PointedObject.toPoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((signedLoopTail X).level (n + 1)).space))
      (curry (PointedSimplicialSet.circle.{u} ◁ kanAdjoint X n ≫ (signedLoopTail X).sigma n))
      (curry (X.sigma n ≫ kanAdjoint X (n + 1))) := by
    rw [curry_natural_left, curry_natural_right]
    change PointedMapping.VerticalChain _
      (kanAdjoint X n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((signedLoopTail X).sigma n))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n) ≫
        (ihom PointedSimplicialSet.circle.{u}).map (kanAdjoint X (n + 1)))
    erw [signedLoopTail_adjoint X n, ← kanAdjoint_comparison X n,
      ← kanAdjoint_comparison X (n + 1)]
    exact SignedAdjointPaths.chain (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2)))
      (hX (n + 2)) (kanAdjoint X n) (kanAdjoint X (n + 1))
  have hu := hc.basedUncurry
  simp only [uncurry_curry] at hu
  exact hu

end SerrePositivity.KST.Spectra.KanSequence
