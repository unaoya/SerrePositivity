module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentConePointSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.BousfieldKanColimitConeComposition

/-!
概要：Kan coend の coherent 錐の切断を、end の普遍点の weighted な評価へ戻す。
方針：固定頂点の錐と切断の全単射を計算し、coend の普遍点の照合式を使う。
規約：頂点の等式による移送を含む実際の切断そのものの等式。
使われ方：coend の錐全体の Hom の族を既存の Hom 比較へ制限する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- coend の反対錐の正規化した coslice 切断は、その普遍点の評価に等しい。 -/
lemma bousfieldKanCoherentOppositeCone_cosliceSection (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F) ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F)) =
      inv (fst ((SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ))
        (Δ[0] : SSet.{u + 1})) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConePoint F)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedVertexConeSpaceEquiv_cosliceSection _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F)

/-- coend の end の普遍点を、持ち上げた切断の零単体として表示する射。 -/
def bousfieldKanLiftedEndPoint (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
          (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)) :=
  SSet.yonedaEquiv.symm (ULift.up
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋0⦌) PUnit.unit))

/-- coend の切断点の Yoneda 表示は、end の普遍点と既存の比較の合成。 -/
lemma bousfieldKanCoherentConePoint_yoneda (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConePoint F) =
      bousfieldKanLiftedEndPoint F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F.op
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConePoint_of_end_point, bousfieldKanLiftedEndPoint,
    SSet.yonedaEquiv_symm_comp]

/-- 普遍点の weighted nerve での実際の評価。 -/
def bousfieldKanConeWeightedPointSection (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
          (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)) :=
  inv (fst _ (Δ[0] : SSet.{u + 1})) ≫ (_ ◁ bousfieldKanLiftedEndPoint F) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op
          (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor))

/-- 錐の正規化した切断は、普遍点の weighted な切断と coslice 比較の合成。 -/
lemma bousfieldKanCoherentOppositeCone_cosliceSection_weighted (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F) ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w))
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F)) =
      bousfieldKanConeWeightedPointSection F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison F.op
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) := by
  erw [bousfieldKanCoherentOppositeCone_cosliceSection, bousfieldKanCoherentConePoint_yoneda,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_uncurry]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
