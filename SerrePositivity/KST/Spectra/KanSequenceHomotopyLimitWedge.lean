module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitEvaluation
public import SerrePositivity.KST.Spectra.KanSequenceWeightedDiagram

/-!
概要：実際の homotopy end の Kan 列から、重み付き内部 Hom 図式への厳密な wedge。
方針：構造可換な射影を用い、end の射影の自然性を全段で検査する。
規約：wedge の極限性は別工程。使われ方：小図式の homotopy limit の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed

namespace SerrePositivity.KST.Spectra.KanSequence

/-- 段ごとの homotopy end は、Kan 列の重み付き内部 Hom 図式の厳密な wedge を持つ。 -/
def homotopyLimitWedge {I : Type u} [SmallCategory I] (D : I ⥤ KanSequence.{u}) :
    Wedge (weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D) :=
  Wedge.mk (homotopyLimit D) (homotopyLimitEvaluation D) (fun _ _ f ↦ by
    apply Hom.ext_app
    intro n
    change end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)) _ ≫
        (ihom (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj _))).map ((D.map f).app n) =
      end_.π (PointedWeightedEnd.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n)) _ ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (PointedObject.adjoinFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map f)) _
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact PointedWeightedEnd.π_condition (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (levelDiagram D n) f)

end SerrePositivity.KST.Spectra.KanSequence
