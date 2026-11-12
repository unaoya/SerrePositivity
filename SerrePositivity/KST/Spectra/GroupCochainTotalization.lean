module

public import SerrePositivity.KST.Spectra.CochainDensityIso
public import SerrePositivity.KST.Spectra.GroupUniversalCoverEnd

/-!
概要：群 cochain の通常の Tot の基礎と点つき BK end の基礎の同型、および Kan 性。
方針：EG の各次数の離散重みの密度の同型と群圏の BK 重みの比較を合成する。
規約：基点を忘れた単体集合の同型を構成する。Sp の ∞ 極限性は主張しない。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。hG と通常の Tot の段ごとの比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

/-- 概要：群 cochain の通常の Tot の基礎と群圏の BK end の基礎は同型。
方針：標準単体の密度と over nerve から EG への重みの同型を合成する。
規約：任意の点つき係数図式で定義し、基点を忘れた同型を与える。
使われ方：Goerss–Jardine VIII §§1–2。hG の段ごとの通常の Tot の表示。 -/
def underlyingTotalizationEndIso
    (D : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}) :
    (PointedTotalization.obj (weightedCochains (universalCoverWeight G) D)).right ≅
      (PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) D).right := by
  let e := SimplexDensity.pointedUnderlyingTotalizationEndIso (universalCoverDiagram G) D
  rw [← universalCoverWeight_eq_discreteLevels G] at e
  exact e ≪≫ PointedSimplicialSet.forget.mapIso (universalCoverEndIso G D).symm

/-- 概要：Kan 係数を持つ群 cochain の通常の Tot は Kan 複体。
方針：完全な BK end の Kan 性を実際の単体集合の同型で移す。
規約：群の有限性は不要。Reedy 置換なしの通常の Tot の主張。
使われ方：Goerss–Jardine VIII §§1–2。通常の Tot の Kan 模型の実証。 -/
lemma totalization_kanComplex
    (D : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u})
    [∀ i, KanComplex (D.obj i).right] :
    KanComplex (PointedTotalization.obj (weightedCochains (universalCoverWeight G) D)).right := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (underlyingTotalizationEndIso G D).symm

end

end SerrePositivity.KST.Spectra.GroupActionCochains
