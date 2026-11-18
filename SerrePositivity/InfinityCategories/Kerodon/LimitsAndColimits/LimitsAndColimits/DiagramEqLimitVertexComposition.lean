module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertexComputations
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoComposition

/-!
概要：図式の等式で移した指定極限の比較は、同じ標準頂点比較と可換する。
方針：等式の帰納法の後、錐の終対象への射の一意性の合成則を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存の比較の法則。
使われ方：S8 の固定された値の同型を変えず、途中の極限の選択を消去する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 図式等式による比較の後の指定極限の比較は、元の同じ比較になる。 -/
lemma limitVertexIsoOfDiagramEq_hom_comp {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (h : F = G) (c : JoinCone F) (d e : JoinCone G)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (limitVertexIsoOfDiagramEq h c d hc hd).hom ≫ (limitVertexIso d e hd he).hom =
      (limitVertexIsoOfDiagramEq h c e hc he).hom := by
  cases h
  exact limitVertexIso_hom_comp c d e hc hd he

/-- 指定極限の比較の後の図式等式による比較も、元の同じ比較になる。 -/
lemma limitVertexIso_hom_comp_diagramEq {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (h : F = G) (c d : JoinCone F) (e : JoinCone G)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (limitVertexIso c d hc hd).hom ≫ (limitVertexIsoOfDiagramEq h d e hd he).hom =
      (limitVertexIsoOfDiagramEq h c e hc he).hom := by
  cases h
  exact limitVertexIso_hom_comp c d e hc hd he

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
