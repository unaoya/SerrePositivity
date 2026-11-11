module

public import SerrePositivity.KST.Spectra.LoopPositivePower
public import SerrePositivity.KST.Spectra.CotensorLoopGroups

/-!
概要：円の Kan 置換の次数射による BF cotensor の整数次数の作用。
方針：任意段の比較で実際の loop の正次数の計算へ移す。
規約：cofibrant 比較の持ち上げの選択は群の作用に影響しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。有理 telescope の遷移射。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cotensor の任意段表示は源の制限射と整合する。
方針：BF 比較射との可換式を誘導群準同型へ送り、段表示の自然性を使う。
規約：k は許容段、n+1 は正次数。
使われ方：BF 1978 §2、HA §1.4.2。円の次数射の整数次数での作用。 -/
theorem cotensorStageEquiv_pre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (X : OmegaSpectrum.{u}) (j : ℤ) (k n : ℕ)
    (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1)
    (a : homotopyGroup (cotensor B X) j) :
    cotensorStageEquiv A X j k n hk hd (homotopyMap (cotensorPre i X) j a) =
      pointedGroupMap n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level k).space)
        (cotensorStageEquiv B X j k n hk hd a) := by
  simp only [cotensorStageEquiv, MulEquiv.trans_apply]
  rw [positiveStageEquiv_natural]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply]
  change pointedGroupMap n ((cotensorProjection A X).app k)
    (pointedGroupMap n ((cotensorPre i X).app k) _) =
      pointedGroupMap n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level k).space)
        (pointedGroupMap n ((cotensorProjection B X).app k) _)
  erw [← pointedGroupMap_comp, ← pointedGroupMap_comp, cotensorPre_comparison]
  rfl

/-- 概要：円の実際の次数射は BF cotensor の全整数次数で m 乗を誘導する。
方針：必ず正次数となる許容段を選び、loop の正次数の冪作用へ帰着する。
規約：m は任意の自然数、j は任意の整数。
使われ方：BF 1978 §2、HA §1.4.2。有理 telescope の実際の構造射の計算。 -/
theorem cotensorPre_power_homotopyMap (X : OmegaSpectrum.{u}) (m : ℕ) (j : ℤ)
    (a : homotopyGroup (cotensor CirclePower.space.{u} X) j) :
    homotopyMap (cotensorPre (CirclePower.powerMap m) X) j a = a ^ m := by
  apply (cotensorStageEquiv CirclePower.space X j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).injective
  rw [cotensorStageEquiv_pre, map_pow]
  exact LoopMappingClasses.groupMap_pre_power _ m _ _

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
