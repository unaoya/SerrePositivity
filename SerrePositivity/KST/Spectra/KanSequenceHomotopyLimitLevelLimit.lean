module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitEnd
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

/-!
概要：元の重み付き wedge を各段で評価した錐は、点つき単体集合の実際の極限。
方針：multifork の整合条件を点つき end の条件へ移し、その普遍射と射影公式を使う。
規約：Kan 列の極限性から逆向きに仮定しない。使われ方：Hom の極限保存との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed Opposite

namespace SerrePositivity.KST.Spectra.KanSequence
local instance homotopyLevelSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}
variable {I : Type u} [SmallCategory I] (D : I ⥤ KanSequence.{u}) (n : ℕ)

/-- 段で評価した multifork の整合条件は、元の点つき end の条件。 -/
lemma homotopyLimitLevelFamily_condition
    (s : Multifork ((multicospanIndexEnd (weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D)).map
      (levelEvaluation n))) {i j : I} (f : i ⟶ j) :
    s.ι i ≫ ((PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)).obj
        (op i)).map f =
      s.ι j ≫ ((PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        (levelDiagram D n)).map f.op).app j := by
  have h := Multifork.condition s (Arrow.mk f)
  change s.ι i ≫ (ihom (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i))).map
      ((D.map f).app n) = s.ι j ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
      (PointedObject.adjoinFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map f)) _ at h
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  dsimp only [PointedWeightedEnd.diagram, Enriched.FunctorCategory.diagram,
    eHomFunctor, Functor.comp, Functor.op, Functor.whiskeringLeft, Functor.whiskeringRight]
  simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  exact h

/-- 段で評価した元の wedge は、点つき end の普遍性で極限である。 -/
def homotopyLimitWedge_mapLevel_isLimit :
    IsLimit ((homotopyLimitWedge D).map (levelEvaluation n)) :=
  Multifork.IsLimit.mk _
    (fun s ↦ end_.lift
      (F := PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n))
      (fun i ↦ s.ι i)
      (fun _ _ f ↦ homotopyLimitLevelFamily_condition D n s f))
    (fun s i ↦ end_.lift_π
      (F := PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n))
      (fun j ↦ s.ι j) (fun _ _ f ↦ homotopyLimitLevelFamily_condition D n s f) i)
    (fun s m hm ↦ by
      apply end_.hom_ext
      intro i
      exact (hm i).trans (end_.lift_π
        (F := PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n))
        (fun j ↦ s.ι j) (fun _ _ f ↦ homotopyLimitLevelFamily_condition D n s f) i).symm)

/-- 各段評価関手で写した元の homotopy end の錐の実際の極限性。 -/
def homotopyLimitWedge_level_isLimit :
    IsLimit ((levelEvaluation n).mapCone (homotopyLimitWedge D)) :=
  ((homotopyLimitWedge D).isLimitMapEquiv (levelEvaluation n)).symm
    (homotopyLimitWedge_mapLevel_isLimit D n)

end SerrePositivity.KST.Spectra.KanSequence
