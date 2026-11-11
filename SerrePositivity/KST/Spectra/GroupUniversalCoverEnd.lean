module

public import SerrePositivity.KST.Spectra.GroupUniversalCoverDiagram
public import SerrePositivity.KST.Spectra.PointedWeightedEndBifunctor
public import SerrePositivity.KST.Spectra.PointedWeightedConePreMap

/-!
概要：群圏の Bousfield–Kan end と EG の作用の end の点つき比較。
方針：重みの自然同型を反変な点つき end 関手へ送り、係数と錐への自然性を示す。
規約：単体集合の厳密な同型であり、Sp の ∞ 極限性を主張しない。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。群 cochain の Tot への比較の入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet


namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

/-- 概要：群圏の点つき BK end と EG からの点つき同変写像の end の比較。
方針：over nerve と EG の重みの同型を反変 end 関手へ送る。
規約：係数に Kan 性を要求しない。
使われ方：Goerss–Jardine VIII §2。hG の重みの実際の変更。 -/
def universalCoverEndIso (D : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}) :
    PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) D ≅
      PointedWeightedEnd.obj (universalCoverDiagram G) D :=
  (PointedWeightedEnd.weightFunctor D).mapIso (bousfieldKanUniversalCoverIso G).symm.op

/-- 概要：EG への end の比較は係数図式の射に自然。
方針：重みの前合成と係数の後合成の可換式を使う。
規約：通常の点つき射の等式。
使われ方：Goerss–Jardine VIII §2。hG の射の比較。 -/
lemma universalCoverEndIso_natural
    {D E : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) τ ≫
        (universalCoverEndIso G E).hom =
      (universalCoverEndIso G D).hom ≫
        PointedWeightedEnd.map (universalCoverDiagram G) τ :=
  PointedWeightedEnd.map_preMap (bousfieldKanUniversalCoverIso G).inv τ

/-- 概要：厳密な錐からの標準射は EG への end の比較で保存される。
方針：錐の定数族の重みの前合成への自然性を使う。
規約：錐が極限錐であることを仮定しない。
使われ方：Goerss–Jardine VIII §2。自明作用の標準射の比較。 -/
lemma coneComparison_universalCoverEndIso
    {D : AsSmall.{u} (SingleObj G) ⥤ PointedSimplicialSet.{u}} (c : Cone D) :
    PointedWeightedEnd.coneComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} (SingleObj G))) c ≫
        (universalCoverEndIso G D).hom =
      PointedWeightedEnd.coneComparison (universalCoverDiagram G) c :=
  PointedWeightedEnd.coneComparison_preMap (bousfieldKanUniversalCoverIso G).inv c

end

end SerrePositivity.KST.Spectra.GroupActionCochains
