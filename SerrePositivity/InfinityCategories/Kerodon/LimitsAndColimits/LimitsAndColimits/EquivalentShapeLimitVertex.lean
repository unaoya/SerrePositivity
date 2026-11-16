module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction

/-!
概要：同値な添字で同じ係数を持つ指定極限錐の頂点を比較する。
方針：大きい錐を制限し、既存の極限の一意性を同じ図式に適用する。
規約：元の二つの錐を引数とし、同値な添字に単射性を加えない。
使われ方：Kerodon §7.1（Tag 02K2）、HTT 5.1.5.6 の重み付き切断の値の比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 図式の等式で型を揃えた指定極限錐の頂点の比較。Kerodon §7.1（Tag 02K2）。 -/
def limitVertexIsoOfDiagramEq {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (h : F = G) (c : JoinCone F) (d : JoinCone G)
    (hc : IsLimitCone c) (hd : IsLimitCone d) : VertexIso c.vertex d.vertex := by
  cases h
  exact limitVertexIso c d hc hd

/-- 同値な添字への制限は、指定した二つの極限錐の頂点を比較する。
Kerodon §7.1（Tag 02K2）、既存の制限と極限の一意性の合成則。 -/
def limitVertexIsoOfEquivalentRestriction {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (a : A ⟶ B) (ha : IsQCatEquivalence a) (O : B ⟶ X)
    (c : JoinCone (a ≫ O)) (d : JoinCone O) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    VertexIso c.vertex d.vertex := by
  have hr := (isLimitCone_iff_restrict_equivalentShape a ha d).mp hd
  have h := limitVertexIso c (restrictJoinCone d a) hc hr
  exact (restrictJoinCone_vertex d a) ▸ h

/-- 底上の同値と可換式に沿って、同じ底係数を持つ指定極限錐の頂点を比較する。
Kerodon §7.1（Tag 02K2）、係数の等式による移送と既存の極限の一意性。 -/
def limitVertexIsoOfOverEquivalence {A B K X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (a : A ⟶ B) (ha : IsQCatEquivalence a) {p : A ⟶ K} {q : B ⟶ K}
    (hw : a ≫ q = p) (O : K ⟶ X)
    (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d) : VertexIso c.vertex d.vertex := by
  have he : p ≫ O = a ≫ (q ≫ O) := by rw [← Category.assoc, hw]
  have htransport : ∀ (F : A ⟶ X) (h : F = a ≫ (q ≫ O))
      (s : JoinCone F), IsLimitCone s → VertexIso s.vertex d.vertex := by
    intro F h s hs
    cases h
    exact limitVertexIsoOfEquivalentRestriction a ha (q ≫ O) s d hs hd
  exact htransport (p ≫ O) he c hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
