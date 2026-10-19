module

public import SerrePositivity.KST.Spectra.CospanBousfieldKanWeight
public import SerrePositivity.KST.Spectra.CospanLoopWeightComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedSectionsOpposite

/-!
概要：区間重みの end から、通常の cospan の元の BK end への比較を構成する。
方針：BK 重みをホーンに同定し、指定した collapse で区間へ写す。
規約：中央の係数の Kan 性だけ。使われ方：円評価の実際の比較辺の Hom–end 計算。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra

/-- 元の BK 重みから区間への、ホーンの右辺を潰す指定した自然変換。 -/
def cospanBKCollapse : bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
    loopIntervalWeight :=
  cospanBKWeightIso.hom ≫ loopHornCollapse

/-- ホーン重みの end を、通常の cospan の元の BK end へ同定する。 -/
def cospanBKHomEndIso (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}) :
    weightedSections loopHornWeight H ≅ bousfieldKanHolim H :=
  weightedSectionsWeightIso cospanBKWeightIso H

/-- 指定した collapse による、区間の end から元の BK end への比較射。 -/
def cospanBKLoopEndComparison (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}) :
    weightedSections loopIntervalWeight H ⟶ bousfieldKanHolim H :=
  weightedSectionsPre cospanBKCollapse H

/-- 元の比較射は、ホーンへの制限と実際の BK end の同型の合成。 -/
lemma cospanBKLoopEndComparison_factor (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}) :
    cospanBKLoopEndComparison H =
      weightedSectionsPre loopHornCollapse H ≫ (cospanBKHomEndIso H).hom :=
  weightedSectionsPre_comp _ _ _

/-- 元の BK end への比較射は、中央の Kan 性だけで実際のホモトピー逆を持つ。 -/
lemma cospanBKLoopEndComparison_homotopyEquivalence
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))] :
    IsSimplicialHomotopyEquivalence (cospanBKLoopEndComparison H) := by
  obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := loopHornCollapseEnd_homotopyEquivalence H
  let e := cospanBKHomEndIso H
  rw [cospanBKLoopEndComparison_factor]
  refine ⟨e.inv ≫ g, ?_, ?_⟩
  · simpa only [e, Category.assoc, Iso.hom_inv_id_assoc] using Nonempty.intro h₁
  · have h := functorHomotopyPostcomp (functorHomotopyPrecomp h₂ e.inv) e.hom
    simpa only [Category.assoc, Category.id_comp, e.inv_hom_id] using Nonempty.intro h

/-- 比較の各成分は、指定した BK collapse による内部 Hom の前合成。 -/
lemma cospanBKLoopEndComparison_π (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    (i : AsSmall.{u} WalkingCospan) :
    cospanBKLoopEndComparison H ≫
        weightedSectionsπ (bousfieldKanWeight (AsSmall.{u} WalkingCospan)) H i =
      weightedSectionsπ loopIntervalWeight H i ≫
        (MonoidalClosed.pre (cospanBKCollapse.app i)).app (H.obj i) :=
  weightedSectionsPre_π _ _ _

/-- 元の BK end への比較は、係数図式の全ての自然変換に自然。 -/
lemma cospanBKLoopEndComparison_naturality
    {H H' : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (η : H ⟶ H') :
    cospanBKLoopEndComparison H ≫ (bousfieldKanHolimFunctor _).map η =
      weightedSectionsMap loopIntervalWeight η ≫ cospanBKLoopEndComparison H' :=
  weightedSectionsPre_naturality _ _

end SerrePositivity.KST.Spectra
