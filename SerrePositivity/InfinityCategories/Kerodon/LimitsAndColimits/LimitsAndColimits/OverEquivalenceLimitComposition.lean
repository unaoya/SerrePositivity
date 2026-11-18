module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentRestrictionLimitTargetComposition

/-!
概要：底上の同値による元の指定極限頂点の比較は、前後の標準極限比較と可換する。
方針：元の定義内の図式等式による移送を固定し、同じ比較の合成則へ帰着する。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02K2）の既存比較の法則。
使われ方：S8 の離散重みの同じ値比較で、途中の極限の選択を消去する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {A B K X : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory X]

/-- 元の底上の比較の定義内にある、同じ図式等式による移送。 -/
private def equivalentRestrictionDiagramTransport (a : A ⟶ B) (ha : IsQCatEquivalence a)
    (O : B ⟶ X) (d : JoinCone O) (hd : IsLimitCone d)
    (F : A ⟶ X) (h : F = a ≫ O) (c : JoinCone F) (hc : IsLimitCone c) :
    VertexIso c.vertex d.vertex := by
  cases h
  exact limitVertexIsoOfEquivalentRestriction a ha O c d hc hd

/-- 同じ図式等式の移送は、始域の標準極限比較との合成に両立する。 -/
private lemma equivalentRestrictionDiagramTransport_source_comp
    (a : A ⟶ B) (ha : IsQCatEquivalence a) (O : B ⟶ X)
    (d : JoinCone O) (hd : IsLimitCone d) (F : A ⟶ X) (h : F = a ≫ O)
    (c c' : JoinCone F) (hc : IsLimitCone c) (hc' : IsLimitCone c') :
    (limitVertexIso c c' hc hc').hom ≫
      (equivalentRestrictionDiagramTransport a ha O d hd F h c' hc').hom =
        (equivalentRestrictionDiagramTransport a ha O d hd F h c hc).hom := by
  cases h
  exact limitVertexIso_hom_comp_equivalentRestriction a ha O c c' d hc hc' hd

/-- 同じ図式等式の移送は、標的の標準極限比較との合成に両立する。 -/
private lemma equivalentRestrictionDiagramTransport_target_comp
    (a : A ⟶ B) (ha : IsQCatEquivalence a) (O : B ⟶ X)
    (d e : JoinCone O) (hd : IsLimitCone d) (he : IsLimitCone e)
    (F : A ⟶ X) (h : F = a ≫ O) (c : JoinCone F) (hc : IsLimitCone c) :
    (equivalentRestrictionDiagramTransport a ha O d hd F h c hc).hom ≫
      (limitVertexIso d e hd he).hom =
        (equivalentRestrictionDiagramTransport a ha O e he F h c hc).hom := by
  cases h
  exact limitVertexIsoOfEquivalentRestriction_hom_comp a ha O c d e hc hd he

/-- 底上の元の比較の前に始域の標準極限比較を合成しても、同じ比較になる。 -/
lemma limitVertexIso_hom_comp_overEquivalence (a : A ⟶ B) (ha : IsQCatEquivalence a)
    {p : A ⟶ K} {q : B ⟶ K} (hw : a ≫ q = p) (O : K ⟶ X)
    (c c' : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hc' : IsLimitCone c') (hd : IsLimitCone d) :
    (limitVertexIso c c' hc hc').hom ≫
      (limitVertexIsoOfOverEquivalence a ha hw O c' d hc' hd).hom =
        (limitVertexIsoOfOverEquivalence a ha hw O c d hc hd).hom := by
  have h : p ≫ O = a ≫ (q ≫ O) := by rw [← Category.assoc, hw]
  change (limitVertexIso c c' hc hc').hom ≫
    (equivalentRestrictionDiagramTransport a ha (q ≫ O) d hd (p ≫ O) h c' hc').hom =
      (equivalentRestrictionDiagramTransport a ha (q ≫ O) d hd (p ≫ O) h c hc).hom
  exact equivalentRestrictionDiagramTransport_source_comp a ha (q ≫ O) d hd
    (p ≫ O) h c c' hc hc'

/-- 底上の元の比較の後に標的の標準極限比較を合成しても、同じ比較になる。 -/
lemma limitVertexIsoOfOverEquivalence_hom_comp (a : A ⟶ B) (ha : IsQCatEquivalence a)
    {p : A ⟶ K} {q : B ⟶ K} (hw : a ≫ q = p) (O : K ⟶ X)
    (c : JoinCone (p ≫ O)) (d e : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (limitVertexIsoOfOverEquivalence a ha hw O c d hc hd).hom ≫
      (limitVertexIso d e hd he).hom =
        (limitVertexIsoOfOverEquivalence a ha hw O c e hc he).hom := by
  have h : p ≫ O = a ≫ (q ≫ O) := by rw [← Category.assoc, hw]
  change (equivalentRestrictionDiagramTransport a ha (q ≫ O) d hd (p ≫ O) h c hc).hom ≫
    (limitVertexIso d e hd he).hom =
      (equivalentRestrictionDiagramTransport a ha (q ≫ O) e he (p ≫ O) h c hc).hom
  exact equivalentRestrictionDiagramTransport_target_comp a ha (q ≫ O) d e hd he
    (p ≫ O) h c hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
