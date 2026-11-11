module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanConeEndPrecomposition

/-!
概要：構成済みの Kan coend の coherent な比較族を、普遍点と coslice の前合成で計算する。
方針：全 Hom の復元公式を一般の end の作用へ移し、実際の比較の uncurry を評価する。
規約：元の図式上の比較そのものの等式。構成済みの錐全体への延長はまだ主張しない。
使われ方：HTT 4.2.4.1 の coend の余錐と native な極限判定の幾何的接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- Hom パラメータへ、構成済みの Kan coend の普遍切断点を添える射。 -/
def bousfieldKanColimitPointParameter (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙
          SSet.opFunctor) ⊗
        (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op :=
  (λ_ _).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomPoint F ▷ _)

/-- 既存の coherent 錐の比較は、普遍点への end の前合成による実際の比較に一致する。 -/
lemma bousfieldKanCoherentConeComparison_of_point_action
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison F Y =
      (SSet.uliftFunctor.{u + 1, u}).map (bousfieldKanColimitPointParameter F Y) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConeEndPrecomposition F.op (Opposite.op Y)
            (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F.op (Opposite.op Y) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison_of_point F Y).symm
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanEndPostcomposition_eq F
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison, h, Functor.map_comp, Category.assoc]
  rfl

/-- 既存の比較の全 Hom パラメータの評価は、普遍点から構成した coslice の族そのもの。 -/
lemma bousfieldKanCoherentConeComparison_uncurry
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeComparison F Y) =
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ) ◁
        (SSet.uliftFunctor.{u + 1, u}).map (bousfieldKanColimitPointParameter F Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve Iᵒᵖ)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
              (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor) ⊗
            (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((α_ (nerve Iᵒᵖ)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
                (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
                  (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor))
              (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op).inv ≫
              (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
                (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
                  (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor) ▷
                (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op)) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).hom ≫
              _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCoslicePrecompositionFamily F.op (Opposite.op Y)
                (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) := by
  rw [bousfieldKanCoherentConeComparison_of_point_action, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedHomHolimConeComparison_precomposition_uncurry,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedCosliceEndPrecompositionEvaluation_eq_family]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
