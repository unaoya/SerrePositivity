module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitCoherentCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedConeEndPrecomposition

/-!
概要：構成した BF homotopy limit の coherent 錐の切断を、反転 end の元の点の評価へ戻す。
方針：固定頂点の全単射の評価式と、end の weighted nerve の普遍評価を合成する。
規約：元の錐の正規化した切断そのものの等式。使われ方：Hom 比較族の実際の制限の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance conePointSectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I]

/-- 元の反転 end の切断点を、持ち上げた end の零単体の射として表す。 -/
def homotopyLimitLiftedEndPoint (D : I ⥤ OmegaSpectrum.{u}) :
    (Δ[0] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor)) :=
  SSet.yonedaEquiv.symm (ULift.up (homotopyLimitReflectedEndPoint D))

/-- 元の coherent 錐の切断点の Yoneda 表示は、元の反転 end の点と比較の合成。 -/
lemma homotopyLimitCoherentConePoint_yoneda (D : I ⥤ OmegaSpectrum.{u}) :
    SSet.yonedaEquiv.symm (homotopyLimitCoherentConePoint D) =
      homotopyLimitLiftedEndPoint D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison D (homotopyLimit D) := by
  rw [homotopyLimitCoherentConePoint, homotopyLimitLiftedEndPoint,
    SSet.yonedaEquiv_symm_comp]

/-- 元の反転 end の点を weighted nerve で実際に評価した切断。 -/
def homotopyLimitConeWeightedPointSection (D : I ⥤ OmegaSpectrum.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor)) :=
  inv (fst _ (Δ[0] : SSet.{u + 1})) ≫ (_ ◁ homotopyLimitLiftedEndPoint D) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D (homotopyLimit D) ⋙ SSet.opFunctor))

/-- 元の錐の正規化した切断は、元の反転 end の点の weighted な切断の像。 -/
lemma homotopyLimitCoherentCone_cosliceSection_weighted (D : I ⥤ OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection (homotopyLimitCoherentCone D) ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w))
          (homotopyLimitCoherentCone_vertex D)) =
      homotopyLimitConeWeightedPointSection D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCosliceComparison D (homotopyLimit D) := by
  erw [homotopyLimitCoherentCone_cosliceSection, homotopyLimitCoherentConePoint_yoneda,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_uncurry]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
