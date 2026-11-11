module

public import SerrePositivity.KST.Spectra.PointedCochainDensityFunctor
public import SerrePositivity.KST.Spectra.GroupCochainTotalization

/-!
概要：群 cochain の通常の Tot と群圏の BK end の点つき同型。
方針：基点を保つ密度の同型と EG の重みの比較を合成する。
規約：有限性を仮定しない通常の点つき同型。Sp の ∞ 極限性は扱わない。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。Tot の Kan Ω 列への移送。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：群 cochain の通常の Tot は群圏の点つき BK end と同型。
方針：標準単体の密度の点つき同型と over nerve から EG への重みの同型を合成する。
規約：任意の点つき係数図式について定義する。
使われ方：Goerss–Jardine VIII §§1–2。hG の点つき通常の Tot 表示。 -/
def totalizationEndIso (G : Type u) [Group G]
    (D : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}) :
    PointedTotalization.obj (weightedCochains (universalCoverWeight G) D) ≅
      PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) D :=
  (totalizationEndNatIso G).app D

end

end SerrePositivity.KST.Spectra.GroupActionCochains
