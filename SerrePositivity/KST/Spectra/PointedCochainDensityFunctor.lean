module

public import SerrePositivity.KST.Spectra.PointedCochainDensityNaturality
public import SerrePositivity.KST.Spectra.GroupUniversalCoverEnd
public import SerrePositivity.KST.Spectra.PointedWeightedEndWeightFunctor

/-!
概要：点つき密度比較と群圏の重み比較を係数関手の自然同型へ束ねる。
方針：検証済みの各成分の自然性を使い、比較全体を関手の段階で合成する。
規約：通常の係数図式の圏の自然同型。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。hG と通常の Tot の関手的な比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき cochain の通常の Tot と完全な重みの end の係数関手の自然同型。
方針：点つき密度の同型とその係数への自然性を束ねる。
規約：通常の係数図式の圏での同型。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。密度比較の関手的な合成。 -/
def SimplexDensity.pointedTotalizationEndNatIso {I : Type u} [SmallCategory I]
    (W : I ⥤ SSet.{u}) :
    weightedCochainsFunctor (discreteLevels W) ⋙ PointedTotalization.functor ≅
      PointedWeightedEnd.functor W :=
  NatIso.ofComponents (fun D ↦ pointedTotalizationEndIso W D)
    (fun τ ↦ pointedTotalizationEndIso_natural W τ)

/-- 概要：群圏の BK end と EG の end の係数関手の自然同型。
方針：EG の重みの比較とその係数への自然性を束ねる。
規約：有限群に限らない通常の係数関手の同型。
使われ方：Goerss–Jardine VIII §2。hG の係数関手と EG の end の比較。 -/
def GroupActionCochains.universalCoverEndNatIso (G : Type u) [Group G] :
    PointedWeightedEnd.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) ≅
      PointedWeightedEnd.functor (universalCoverDiagram G) :=
  PointedWeightedEnd.weightToFunctor.mapIso (bousfieldKanUniversalCoverIso G).symm.op

/-- 概要：群 cochain の通常の Tot と BK end の係数関手の自然同型。
方針：点つき密度の自然同型と重みの自然同型の逆を関手の段階で合成する。
規約：任意の点つき係数図式について成立する。
使われ方：Goerss–Jardine VIII §§1–2。hG と通常の Tot の射の比較。 -/
def GroupActionCochains.totalizationEndNatIso (G : Type u) [Group G] :
    weightedCochainsFunctor (universalCoverWeight G) ⋙ PointedTotalization.functor ≅
      PointedWeightedEnd.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) :=
  SimplexDensity.pointedTotalizationEndNatIso (universalCoverDiagram G) ≪≫
    (universalCoverEndNatIso G).symm

end

end SerrePositivity.KST.Spectra
