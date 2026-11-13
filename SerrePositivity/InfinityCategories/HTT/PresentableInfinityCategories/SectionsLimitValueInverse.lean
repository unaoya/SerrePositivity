module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsLimitValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FamilyEquivalenceReflection

/-!
概要：同じ指定極限への値比較と元の錐の値の切断写像は、逆順でも恒等に同型。
方針：既検証の右逆の全族同型を、同じ比較の同値性によって反映する。
規約：元の選択した比較も切断写像も変更しない。
使われ方：指定極限の間の辺から切断制限の四角形を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 元の値の切断写像から同じ指定極限の値へ戻る全族は恒等射と同型。 -/
def coneSectionsValueMap_sectionsLimitValueIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCone F) (hc : IsLimitCone c) :
    FunctorIso
      (coneSectionsValueMapAt F c c.vertex rfl ≫
        (SSet.uliftFunctor.{u + 1, u}).map (sectionsLimitValueEquivalence F c hc).hom)
      (𝟙 _) := by
  let e := sectionsLimitValueEquivalence F c hc
  apply functorIsoOfPrecompEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).map e.hom) e.isQCatEquivalence.ulift
  simpa only [Category.assoc, Category.id_comp, Category.comp_id, e] using
    FunctorIso.postcomp (sectionsLimitValueEquivalence_coneSectionsIso F c hc)
      ((SSet.uliftFunctor.{u + 1, u}).map e.hom)

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
