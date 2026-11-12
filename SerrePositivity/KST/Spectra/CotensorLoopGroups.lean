module

public import SerrePositivity.KST.Spectra.CotensorRestriction
public import SerrePositivity.KST.Spectra.SpectrumBoundary
public import SerrePositivity.KST.Spectra.LoopHomotopyGroups

/-!
概要：cotensor の整数次数群の段表示と円を源とする場合の次数移動。
方針：BF 比較射の群同型と loop の長完全列による同型を合成する。
規約：整数次数の群の計算であり、Sp の ∞ 普遍性を含めない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の loop 模型の群の計算。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cotensor の整数次数群と任意の許容段の内部 Hom の群との同型。
方針：正次数の段表示と BF 比較射の群同型を合成する。
規約：k は許容段、n+1 は実際の正次数。
使われ方：BF 1978 §2、HA §1.4.2。cotensor の自己射の π_* の計算。 -/
def cotensorStageEquiv (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u})
    (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) :
    homotopyGroup (cotensor A X) j ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A (X.level k).space).right n
        (PointedSimplicialSet.basepoint (PointedObject.basedHom A (X.level k).space)) :=
  (positiveStageEquiv (cotensor A X) j k n hk hd).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n ((cotensorProjection A X).app k).right
      (cotensorProjection_piIsomorphism A X k) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))

/-- 概要：円を源とする cotensor は整数次数群を一つ上げる。
方針：同じ許容段で BF 比較と loop の群同型を使い、元のスペクトルの整数次数へ戻す。
規約：全整数次数 j について π_j(cotensor(S¹,X))≃π_{j+1}(X)。
使われ方：BF 1978 §2、HA §1.4.2。有理 telescope の loop 模型の次数調整。 -/
def cotensorLoopHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (cotensor PointedSimplicialSet.circle.{u} X) j ≃*
      homotopyGroup X (j + 1) := by
  have hk : -(j + 1) ≤ (boundaryStage j : ℤ) := by
    have h := boundaryStage_admissible j
    omega
  have hd : degree (j + 1) (boundaryStage j) = (boundaryIndex j + 1) + 1 := by
    have h := boundaryStage_degree j
    have hk := boundaryStage_admissible j
    unfold degree at h ⊢
    omega
  exact (cotensorStageEquiv PointedSimplicialSet.circle.{u} X j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).trans
      ((loopPositiveHomotopyEquiv (X.level (boundaryStage j)).space (boundaryIndex j)).trans
        (positiveStageEquiv X (j + 1) (boundaryStage j) (boundaryIndex j + 1) hk hd).symm)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
