module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightStraighteningFiberCocone
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredKanCocone

/-!
概要：元の strict right fibration 余錐の反転 fiber 余錐は同じ通常の余極限。
方針：元の fiber 余極限を反転し、同じ fiber 反転同型を図式と余錐の全脚で比較する。
規約：指定した同じ余錐を扱う。別の余錐の存在を使わない。
使われ方：元の right straightening 余錐の各評価の native な余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]
local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 元の同じ strict 余極限余錐の反転 fiber 余錐の台は通常の余極限。 -/
def strictOppositeFiberCocone_isColimit (F : I ⥤ RightFibrationObject B) (b : B _⦋0⦌) :
    IsColimit (kanObjectForget.mapCocone (rightFibrationOppositeFiberCocone
      (strictRightFibrationColimitCocone F) (SSet.opObjEquiv.symm b))) := by
  let c := rightFibrationOppositeFiberCocone
    (strictRightFibrationColimitCocone F) (SSet.opObjEquiv.symm b)
  let e := Functor.isoWhiskerRight (rightFibrationOppositeFiberDiagramIso F b) kanObjectForget
  apply (IsColimit.precomposeHomEquiv e (kanObjectForget.mapCocone c)).toFun
  apply IsColimit.ofIsoColimit
    (isColimitOfPreserves SSet.opFunctor (strictRightFibrationFiberColimitCocone_isColimit F b))
  refine Cocone.ext (vertexFiberOpIso (strictRightFibrationColimitProjection F) b) ?_
  intro i
  change SSet.opFunctor.map ((strictRightFibrationFiberColimitCocone F b).ι.app i) ≫
    (vertexFiberOpIso (strictRightFibrationColimitProjection F) b).hom =
      (vertexFiberOpIso (F.obj i).val.hom b).hom ≫
        (coherentEnrichedUnderlyingFunctor
          (leftFibrationFiberEvaluationEnriched (SSet.opObjEquiv.symm b))).map
            ((rightFibrationOppositeOrdinary B).map
              ((strictRightFibrationColimitCocone F).ι.app i))
  rw [strictRightFibrationFiberColimitCocone_ι, leftFiberEvaluation_underlying_map]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- 元の同じ反転 fiber 余錐は SpaceInfinity の native な余極限。 -/
lemma strictOppositeFiberNativeCocone_isColimit (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : IsColimitCone (strictNativeCocone (rightFibrationOppositeFiberCocone
      (strictRightFibrationColimitCocone F) (SSet.opObjEquiv.symm b))) :=
  strictNativeCocone_isColimit_of_filtered_forget _ (strictOppositeFiberCocone_isColimit F b)

end SerrePositivity.InfinityCategories.F2.Ind
