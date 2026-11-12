module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionBKPoint
public import SerrePositivity.KST.Spectra.SpectrumCircleBKCoherentCone

/-!
概要：companion の元の BK 点を、頂点固定の coherent 錐の切断空間で元の BK 錐へ結ぶ。
方針：実際の BK 点の辺を共通 edgewise 解像と反転射影、共有の切断比較へ送る。
規約：元の固定図式と cotensor 頂点を保持。使われ方：元の評価錐の切断点との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionConePointSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance companionConePointHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の共通解像の右切断と左射影による、同じ Hom–BK end の反転への射。 -/
def circleCompanionBKReflection (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor) :=
  edgewiseEndRightSection _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y)))

/-- 元の companion の BK 点を、同じ共通解像経由で反転した点。 -/
def circleCompanionReflectedEndPoint (z : Sp.{u} _⦋0⦌) :=
  (circleCompanionBKReflection (nativeCotensorInput PointedSimplicialSet.circle z).val).app
    (Opposite.op ⦋0⦌) (circleCompanionBKEndPoint z)

/-- 元の BK 点の辺は、反転 end でも元の BK 錐の点への実際の辺を与える。 -/
def circleCompanionReflectedEndPointEdge (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) ⋙ SSet.opFunctor)).Edge
      (circleCompanionReflectedEndPoint z)
      (circleBKReflectedEndPoint (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  (circleCompanionBKEndPointEdge z).map
    (circleCompanionBKReflection (nativeCotensorInput PointedSimplicialSet.circle z).val)

/-- companion の元の BK 点から得られる、頂点固定の coherent 錐の切断点。 -/
def circleCompanionConeSectionPoint (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram
        (nativeCotensorInput PointedSimplicialSet.circle z).val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison
    (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val)).app _
        (ULift.up (circleCompanionReflectedEndPoint z))

/-- 同じ固定図式・同じ頂点の切断空間内で、元の BK 錐の点へ向かう実際の辺。 -/
def circleCompanionConeSectionPointEdge (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram
        (nativeCotensorInput PointedSimplicialSet.circle z).val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))).Edge
      (circleCompanionConeSectionPoint z)
      (circleBKCoherentConePoint (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  let e := circleCompanionReflectedEndPointEdge z
  let eu : ((SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
        (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val) ⋙ SSet.opFunctor))).Edge
      (ULift.up (circleCompanionReflectedEndPoint z))
      (ULift.up (circleBKReflectedEndPoint
        (nativeCotensorInput PointedSimplicialSet.circle z).val)) :=
    SSet.Edge.mk (ULift.up e.edge) (congrArg ULift.up e.src_eq) (congrArg ULift.up e.tgt_eq)
  exact eu.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison
    (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val))

end SerrePositivity.KST.Spectra.OmegaSpectrum
