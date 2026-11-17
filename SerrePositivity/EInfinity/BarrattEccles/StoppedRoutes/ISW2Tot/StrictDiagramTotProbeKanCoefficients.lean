module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeCoefficientsComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotFrameHomInfinity
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanUniversePoints
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanExInfinityUnit

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE TotのBK錐を全Hom∞比較の同じ第零係数へ送る。
方針：元の宇宙変更の指定射と同じEx∞単位を合成する。
規約：IS-W2 R02〜R03の既存の係数移送則。別のframeやprobeを選ばない。
使われ方：元の指定BK点を同じcoherentな分類図式へ運ぶ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeKanCoefficientsModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotProbeKanCoefficientsFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotProbeKanCoefficientsCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y

/-- 元の二重反対添字を、全frame比較と同じ大きさに持ち上げる全関手。 -/
def strictBETotProbeFrameIndex (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  AsSmall.down ⋙ (opOpEquivalence K).functor ⋙ F ⋙ AsSmall.up

/-- 同じraw係数の宇宙変更とEx∞は、既存の全Hom比較の第零図式そのもの。 -/
theorem strictBETotProbeKanCoefficients_eq (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y) ⋙
      exInfinity = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeFrameIndex A K F ⋙
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram
          ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
            (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0 ⋙ kanObjectForget := rfl

/-- 元の同じprobeのraw Hom係数のKan性。 -/
theorem strictBETotProbeRightHomDiagram_kanComplex (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    KanComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y).obj i) :=
  rightFrameHom_kanComplex (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) (F.obj i.unop.unop)

/-- 同じ宇宙変更済みの係数のKan性。 -/
theorem strictBETotProbeUniverseCoefficients_kanComplex (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex (((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y)).obj i) := by
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram_kanComplex A K F Y (AsSmall.down.obj i)
  change KanComplex ((SSet.uliftFunctor.{u+1,u}).obj
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y).obj (AsSmall.down.obj i)))
  infer_instance

/-- 同じ係数単位が誘導するBK切断写像はホモトピー同値。 -/
theorem strictBETotProbeBKExInfinityUnit_homotopyEquivalence
    (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsMap
      (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit (AsSmall.{u+1} Kᵒᵖᵒᵖ)
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y)))) := by
  have (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeUniverseCoefficients_kanComplex A K F Y i
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityUnit_homotopyEquivalence _ _

/-- 元の同じ普遍BK錐を、指定downと同じEx∞単位へ合成する。 -/
def strictBETotUniversalBKExInfinityCone (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶
      (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)) ⋙ exInfinity :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone Kᵒᵖᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F) ≫
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _

/-- 元の指定BK点は、同じ宇宙変更と係数単位により同じEx∞錐の零単体へ移る。 -/
theorem strictBETotUniversalBKExInfinityCone_point (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))))).app (op ⦋0⦌))
        (((bousfieldKanUniverseSectionsIso.{u,u+1} Kᵒᵖᵒᵖ
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))).hom).app (op ⦋0⦌)
            (ULift.up (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomPoint A K F))) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKExInfinityCone A K F) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomPoint, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseSectionsIso_point,
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityUnit_point]
  rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
