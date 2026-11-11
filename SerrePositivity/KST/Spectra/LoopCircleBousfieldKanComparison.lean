module

public import SerrePositivity.KST.Spectra.LoopIntervalEndCircleIso
public import SerrePositivity.KST.Spectra.CospanBousfieldKanLoopComparison

/-!
概要：基点付き円の写像空間から、零 cospan の元の BK end への実際の比較射。
方針：区間 end の厳密な同型の逆と、指定した BK collapse による制限を合成する。
規約：標的の Kan 性だけで実際のホモトピー逆を持つ。使われ方：円評価の BF 比較の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 標準の基点付き円の写像空間から、元の BK end への指定した比較射。 -/
def loopCircleBKComparison (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (loopCoefficient Y) :=
  (loopIntervalEndCircleIso Y).inv ≫ cospanBKLoopEndComparison (loopCoefficient Y)

/-- 元の円の写像空間から BK end への比較は、実際の単体的ホモトピー同値。 -/
lemma loopCircleBKComparison_homotopyEquivalence (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (loopCircleBKComparison Y) := by
  have centralKan : KanComplex ((loopCoefficient Y).obj (AsSmall.up.obj .one)) :=
    inferInstanceAs (KanComplex Y.right)
  obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := cospanBKLoopEndComparison_homotopyEquivalence (loopCoefficient Y)
  let e := loopIntervalEndCircleIso Y
  refine ⟨g ≫ e.hom, ?_, ?_⟩
  · have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp h₁ e.inv) e.hom
    simpa only [loopCircleBKComparison, e, Category.assoc, Category.id_comp,
      Iso.inv_hom_id] using Nonempty.intro h
  · simpa only [loopCircleBKComparison, e, Category.assoc, Iso.hom_inv_id_assoc]
      using Nonempty.intro h₂

/-- 比較の全成分は、円の区間への制限と指定した BK collapse への前合成。 -/
lemma loopCircleBKComparison_π (Y : PointedSimplicialSet.{u})
    (i : AsSmall.{u} WalkingCospan) :
    loopCircleBKComparison Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)) (loopCoefficient Y) i =
      (loopIntervalEndCircleIso Y).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) i ≫
          (pre (cospanBKCollapse.app i)).app ((loopCoefficient Y).obj i) := by
  rw [loopCircleBKComparison, Category.assoc, cospanBKLoopEndComparison_π]

end SerrePositivity.KST.Spectra
