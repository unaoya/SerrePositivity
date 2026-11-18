module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentRestrictionLimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoRestriction

/-!
概要：同値な添字による固定した極限頂点の比較と、標的極限の比較の合成則。
方針：同じ制限錐の比較と頂点移送に分け、制限の射影の自然性を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02K2）の既存比較の法則。
使われ方：S8 の元の圏への値の比較で、途中の指定極限の選択を照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の同値な添字による比較に標的の標準極限比較を合成しても、同じ比較になる。 -/
lemma limitVertexIsoOfEquivalentRestriction_hom_comp {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (a : A ⟶ B) (ha : IsQCatEquivalence a) (O : B ⟶ X)
    (c : JoinCone (a ≫ O)) (d e : JoinCone O)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (limitVertexIsoOfEquivalentRestriction a ha O c d hc hd).hom ≫
        (limitVertexIso d e hd he).hom =
      (limitVertexIsoOfEquivalentRestriction a ha O c e hc he).hom := by
  have hdf := (isLimitCone_iff_restrict_equivalentShape a ha d).mp hd
  have hef := (isLimitCone_iff_restrict_equivalentShape a ha e).mp he
  rw [limitVertexIsoOfEquivalentRestriction_hom a ha O c d hc hd hdf,
    limitVertexIsoOfEquivalentRestriction_hom a ha O c e hc he hef,
    Category.assoc, limitVertexIso_restrict_hom a d e hd he hdf hef,
    ← Category.assoc, limitVertexIso_hom_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
