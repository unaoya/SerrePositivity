module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertexComputations

/-!
概要：底上の同値による指定極限頂点比較を、同じ制限錐との標準比較へ戻す。
方針：図式等式による移送を局所化し、既存の制限比較の順射の計算を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存比較の計算法則。
使われ方：R04-RI。相対同型による底上の二つの比較を同じ図式の錐で照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

private def diagramRestrictionComparison {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (ef : IsQCatEquivalence f) (O : B ⟶ X)
    (d : JoinCone O) (hd : IsLimitCone d) (F : A ⟶ X) (h : F = f ≫ O)
    (c : JoinCone F) (hc : IsLimitCone c) : VertexIso c.vertex d.vertex := by
  cases h
  exact limitVertexIsoOfEquivalentRestriction f ef O c d hc hd

private lemma diagramRestrictionComparison_hom {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (f : A ⟶ B) (ef : IsQCatEquivalence f) (O : B ⟶ X)
    (d : JoinCone O) (hd : IsLimitCone d) (F : A ⟶ X) (h : F = f ≫ O)
    (c : JoinCone F) (hc : IsLimitCone c)
    (hr : IsLimitCone ((restrictJoinCone d f).cast h.symm)) :
    (diagramRestrictionComparison f ef O d hd F h c hc).hom =
      (limitVertexIso c ((restrictJoinCone d f).cast h.symm) hc hr).hom ≫
        eqToHom (congrArg HomotopyCategory.mk
          ((JoinCone.vertex_cast _ h.symm).trans (restrictJoinCone_vertex d f))) := by
  cases h
  exact limitVertexIsoOfEquivalentRestriction_hom f ef O c d hc hd hr

/-- 同じ底上の比較の順射は、固定条件を揃えた元の制限錐との標準比較である。 -/
@[cite HTT "1.2.13" (partial := special) "既存の底上の同値による比較を、同じ制限錐で計算する法則。"]
lemma limitVertexIsoOfOverEquivalence_hom_restriction {A B K X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (p : A ⟶ K) (q : B ⟶ K) (f : A ⟶ B) (hf : f ≫ q = p)
    (ef : IsQCatEquivalence f) (O : K ⟶ X)
    (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d) :
    let he : p ≫ O = f ≫ (q ≫ O) := by rw [← Category.assoc, hf]
    let df := (restrictJoinCone d f).cast he.symm
    ∀ hdf : IsLimitCone df,
    (limitVertexIsoOfOverEquivalence f ef hf O c d hc hd).hom =
      (limitVertexIso c df hc hdf).hom ≫
        eqToHom (congrArg HomotopyCategory.mk
          ((JoinCone.vertex_cast _ he.symm).trans (restrictJoinCone_vertex d f))) := by
  intro he df hdf
  change (diagramRestrictionComparison f ef (q ≫ O) d hd (p ≫ O) he c hc).hom = _
  exact diagramRestrictionComparison_hom f ef (q ≫ O) d hd (p ≫ O) he c hc hdf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
