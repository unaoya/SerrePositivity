module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKCoherentCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedConeEndPrecomposition

/-!
概要：円 cotensor の coherent 錐の元の切断を、反転 BK 点の weighted な評価へ戻す。
方針：固定頂点の全単射の評価式と、元の end の普遍評価を合成する。
規約：錐全体の切断の厳密な式。使われ方：全 Hom 比較族の制限と頂点評価の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circlePointSectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の反転 BK 点を、持ち上げた end への零単体の射として表す。 -/
def circleBKLiftedEndPoint (Y : OmegaSpectrum.{u}) :
    (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor)) :=
  SSet.yonedaEquiv.symm (ULift.up (circleBKReflectedEndPoint Y))

/-- 元の coherent な切断点の Yoneda 表示は、元の反転 BK 点を比較で送った射。 -/
lemma circleBKCoherentConePoint_yoneda (Y : OmegaSpectrum.{u}) :
    SSet.yonedaEquiv.symm (circleBKCoherentConePoint Y) =
      circleBKLiftedEndPoint Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) := by
  rw [circleBKCoherentConePoint, circleBKLiftedEndPoint, SSet.yonedaEquiv_symm_comp]

/-- 元の反転 BK 点を weighted nerve の普遍族で評価した切断。 -/
def circleBKConeWeightedPointSection (Y : OmegaSpectrum.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) (cotensor PointedSimplicialSet.circle Y) ⋙
          SSet.opFunctor)) :=
  inv (fst _ (Δ[0] : SSet.{u + 1})) ≫ (_ ◁ circleBKLiftedEndPoint Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor))

/-- 元の錐の正規化した切断は、元の反転 BK 点の weighted な評価の像そのもの。 -/
lemma circleBKCoherentCone_cosliceSection_weighted (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection (circleBKCoherentCone Y) ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w))
          (circleBKCoherentCone_vertex Y)) =
      circleBKConeWeightedPointSection Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison (pointLoopDiagram Y)
          (cotensor PointedSimplicialSet.circle Y) := by
  erw [circleBKCoherentCone_cosliceSection, circleBKCoherentConePoint_yoneda,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_uncurry]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
