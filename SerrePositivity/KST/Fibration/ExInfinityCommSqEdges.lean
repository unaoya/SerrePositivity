module
public import SerrePositivity.KST.Fibration.KanCommSqEdges
public import SerrePositivity.KST.Fibration.KanClosedEvaluation

/-! # 元の通常四角形の Ex∞ coherent 表示の四辺は、同じ元の Ex∞ 射である -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction

namespace SerrePositivity.KST.Fibration

/-- 元の通常射の Ex∞ 像を、同じ実 Kan 値間の射として読む。 -/
def exInfinityKanMap {A B : SSet.{u}} (f : A ⟶ B) :
    exInfinityClosedKanEnrichedFunctor.obj ⟨A⟩ ⟶
      exInfinityClosedKanEnrichedFunctor.obj ⟨B⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map f

variable {P X Y Z : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (sq : CommSq a b f g)

/-- 元の右辺 g を同じ Ex∞ 射として厳密に回収する。 -/
theorem exInfinityCommSqInfinitySquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ exInfinityCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap g)).edge :=
  kanCommSqInfinitySquare_right (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq)

/-- 元の上辺 f を同じ Ex∞ 射として厳密に回収する。 -/
theorem exInfinityCommSqInfinitySquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ exInfinityCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap f)).edge :=
  kanCommSqInfinitySquare_top (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq)

/-- 元の下辺 b を同じ Ex∞ 射として厳密に回収する。 -/
theorem exInfinityCommSqInfinitySquare_bottom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ exInfinityCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap b)).edge :=
  kanCommSqInfinitySquare_bottom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq)

/-- 元の左辺 a を同じ Ex∞ 射として厳密に回収する。 -/
theorem exInfinityCommSqInfinitySquare_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ exInfinityCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap a)).edge :=
  kanCommSqInfinitySquare_left (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq sq)

/-- 同じ元の四角形の頂点を、元の Ex∞ Kan 値として回収する。 -/
theorem exInfinityCommSqInfinitySquare_apex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (exInfinityCommSqInfinitySquare sq) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨P⟩) := by
  have he : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ exInfinityCommSqInfinitySquare sq) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap b)).edge :=
    (congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} => SSet.yonedaEquiv t)
      (exInfinityCommSqInfinitySquare_bottom sq)).trans
        (SSet.yonedaEquiv.apply_symm_apply _)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source _).symm.trans
    ((congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).δ 1 t) he).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap b)).src_eq)

/-- 同じ元の四角形の頂点を、元の Ex∞ Kan 値として回収する。 -/
theorem exInfinityCommSqInfinitySquare_middle :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (exInfinityCommSqInfinitySquare sq) 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨Y⟩) := by
  have he : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ exInfinityCommSqInfinitySquare sq) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap b)).edge :=
    (congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} => SSet.yonedaEquiv t)
      (exInfinityCommSqInfinitySquare_bottom sq)).trans
        (SSet.yonedaEquiv.apply_symm_apply _)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target _).symm.trans
    ((congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).δ 0 t) he).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap b)).tgt_eq)

/-- 同じ元の四角形の頂点を、元の Ex∞ Kan 値として回収する。 -/
theorem exInfinityCommSqInfinitySquare_corner :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (exInfinityCommSqInfinitySquare sq) 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨X⟩) := by
  have he : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ exInfinityCommSqInfinitySquare sq) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap a)).edge :=
    (congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} => SSet.yonedaEquiv t)
      (exInfinityCommSqInfinitySquare_left sq)).trans
        (SSet.yonedaEquiv.apply_symm_apply _)
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target _).symm.trans
    ((congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).δ 0 t) he).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap a)).tgt_eq)

/-- 同じ元の四角形の頂点を、元の Ex∞ Kan 値として回収する。 -/
theorem exInfinityCommSqInfinitySquare_target :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (exInfinityCommSqInfinitySquare sq) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨Z⟩) := by
  have he : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ exInfinityCommSqInfinitySquare sq) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap g)).edge :=
    (congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} => SSet.yonedaEquiv t)
      (exInfinityCommSqInfinitySquare_right sq)).trans
        (SSet.yonedaEquiv.apply_symm_apply _)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target _).symm.trans
    ((congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).δ 0 t) he).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (exInfinityKanMap g)).tgt_eq)

end SerrePositivity.KST.Fibration
