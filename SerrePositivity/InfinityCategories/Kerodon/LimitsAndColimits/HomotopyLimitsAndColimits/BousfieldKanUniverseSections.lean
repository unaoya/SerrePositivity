module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanUniverseWeight
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestrictionIso

/-!
概要：元のBK切断空間のULiftを、同じAsSmall添字とULift係数のBK切断空間へ同型にする。
方針：元の普遍評価による切断空間の同型に、指定downによるBK重み同型の制限を合成する。
規約：IS-W2 R02〜R03の既存構成の宇宙移送則。Kan性は要求しない。
使われ方：同じ普遍BK点を全Hom∞比較の宇宙へ送る。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory
variable (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u})

/-- 同じ指定downと同じ係数ULiftによる、元のBK切断空間の実同型。 -/
def bousfieldKanUniverseSectionsIso :
    (SSet.uliftFunctor.{max u v,u}).obj (bousfieldKanHolim H) ≅
      bousfieldKanHolim ((AsSmall.down : AsSmall.{v} I ⥤ I) ⋙ H ⋙
        SSet.uliftFunctor.{max u v,u}) :=
  weightedSectionsUniverseIso I (bousfieldKanWeight I) H ≪≫
    weightedSectionsWeightIso (bousfieldKanUniverseWeightIso I) ((weightedDiagramUniverse.{u,v} I).obj H)

/-- 同じ同型の順射は、普遍評価の比較と元のBK重みのdownによる前合成。 -/
theorem bousfieldKanUniverseSectionsIso_hom :
    (bousfieldKanUniverseSectionsIso.{u,v} I H).hom =
      weightedSectionsUniverseComparison I (bousfieldKanWeight I) H ≫
        weightedSectionsPre (bousfieldKanUniverseWeightDown I) ((weightedDiagramUniverse.{u,v} I).obj H) := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
