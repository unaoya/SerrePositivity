module

public import SerrePositivity.KST.Spectra.SpectrumTail

/-!
概要：tail の整数次数の群の比較の自然性。
方針：隣接する二つの段の同じ正次数表示へ移して比較する。
規約：スペクトルの射は厳密な射を使う。
使われ方：BF 1978 §2、HA §1.4.2。有理 telescope の次数補正と標準射の計算。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：tail による整数次数の比較はスペクトルの厳密な射に関して自然。
方針：両辺を元の一段先の正次数表示へ送り、段表示の自然性を使う。
規約：全整数次数 j。
使われ方：BF 1978 §2、HA §1.4.2。有理化の次数補正と実際の標準射の比較。 -/
theorem tailHomotopyEquiv_natural {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (j : ℤ) (a : homotopyGroup (tail X) j) :
    tailHomotopyEquiv Y j (homotopyMap (tailMap f) j a) =
      homotopyMap f (j - 1) (tailHomotopyEquiv X j a) := by
  let k := boundaryStage j
  let n := boundaryIndex j
  have hk : -(j - 1) ≤ ((k + 1 : ℕ) : ℤ) := by
    have h := boundaryStage_admissible j
    dsimp only [k]
    omega
  have hd : degree (j - 1) (k + 1) = n + 1 :=
    (degree_tail j k).trans (boundaryStage_degree j)
  let eX := positiveStageEquiv X (j - 1) (k + 1) n hk hd
  let eY := positiveStageEquiv Y (j - 1) (k + 1) n hk hd
  have hX : eX (tailHomotopyEquiv X j a) =
      positiveStageEquiv (tail X) j k n (boundaryStage_admissible j)
        (boundaryStage_degree j) a := eX.apply_symm_apply _
  have hY : eY (tailHomotopyEquiv Y j (homotopyMap (tailMap f) j a)) =
      positiveStageEquiv (tail Y) j k n (boundaryStage_admissible j)
        (boundaryStage_degree j) (homotopyMap (tailMap f) j a) := eY.apply_symm_apply _
  apply eY.injective
  calc
    _ = positiveStageEquiv (tail Y) j k n (boundaryStage_admissible j)
        (boundaryStage_degree j) (homotopyMap (tailMap f) j a) := hY
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (f.app (k + 1)).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
        (positiveStageEquiv (tail X) j k n (boundaryStage_admissible j)
          (boundaryStage_degree j) a) :=
      positiveStageEquiv_natural (tailMap f) j k n
        (boundaryStage_admissible j) (boundaryStage_degree j) a
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (f.app (k + 1)).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
        (eX (tailHomotopyEquiv X j a)) := congrArg _ hX.symm
    _ = _ := (positiveStageEquiv_natural f (j - 1) (k + 1) n hk hd
      (tailHomotopyEquiv X j a)).symm

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
