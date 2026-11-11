module

public import SerrePositivity.KST.Spectra.GroupPointedTotalization
public import SerrePositivity.KST.Spectra.PointedCochainDensityNaturality

/-!
概要：群 cochain の通常の Tot と群圏の BK end の点つき比較の係数への自然性。
方針：密度の自然性と EG の重みの end の自然性を合成する。
規約：係数の Kan 性や群の有限性は不要。
使われ方：Goerss–Jardine VIII §§1–2。通常の Tot の射と hG の射の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet


namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：群 cochain の通常の Tot と BK end の比較は係数の射に自然。
方針：EG の end への比較を後合成して二つの自然性を使う。
規約：厳密な点つき射の等式。
使われ方：Goerss–Jardine VIII §§1–2。hG と通常の Tot の関手的な模型比較。 -/
lemma totalizationEndIso_natural (G : Type u) [Group G]
    {D E : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    PointedTotalization.map (weightedCochainsMap (universalCoverWeight G) τ) ≫
        (totalizationEndIso G E).hom =
      (totalizationEndIso G D).hom ≫
        PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) τ :=
  (totalizationEndNatIso G).hom.naturality τ

end

end SerrePositivity.KST.Spectra.GroupActionCochains
