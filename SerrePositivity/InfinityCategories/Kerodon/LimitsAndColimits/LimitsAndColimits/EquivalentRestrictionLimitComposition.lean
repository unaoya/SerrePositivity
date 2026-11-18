module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.DiagramEqLimitVertexComposition

/-!
概要：同値な添字への指定極限の比較と、始域の標準頂点比較の合成則。
方針：同じ制限錐への標準比較と頂点の等式による移送に分け、合成則を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02K2）の既存の比較の法則。
使われ方：S8 の指定された離散重みの値の同型を保持した比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同値な添字に沿う比較の前に標準頂点比較を合成しても、元の同じ比較になる。 -/
lemma limitVertexIso_hom_comp_equivalentRestriction {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (a : A ⟶ B) (ha : IsQCatEquivalence a) (O : B ⟶ X)
    (c c' : JoinCone (a ≫ O)) (d : JoinCone O)
    (hc : IsLimitCone c) (hc' : IsLimitCone c') (hd : IsLimitCone d) :
    (limitVertexIso c c' hc hc').hom ≫
      (limitVertexIsoOfEquivalentRestriction a ha O c' d hc' hd).hom =
        (limitVertexIsoOfEquivalentRestriction a ha O c d hc hd).hom := by
  have hda := (isLimitCone_iff_restrict_equivalentShape a ha d).mp hd
  rw [limitVertexIsoOfEquivalentRestriction_hom a ha O c' d hc' hd hda,
    limitVertexIsoOfEquivalentRestriction_hom a ha O c d hc hd hda,
    ← Category.assoc, limitVertexIso_hom_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
