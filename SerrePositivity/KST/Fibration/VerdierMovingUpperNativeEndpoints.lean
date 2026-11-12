module
public import SerrePositivity.KST.Fibration.VerdierReadoutMovingLongInput

/-!
概要：動く上側の同じ実長 Hom 入力の両端を、元の全 native Hom へ戻す。
方針：同じ相対合成ホモトピーの両端を curry の頂点回収で評価する。
規約：同じ下側読出しと全 S• 比較を保持し、独立な端点を選ばない。
使われ方：K-6 c4 の指定有限端点の二胞体との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

variable
  (H : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
    (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (verdierNativeCompositePoint d 1)))
  (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (verdierReadoutUpperComparison d)
    (verdierLowerNativeReadoutHomotopy d L hL) H)
  (hT : T.diagram ≫ (pre verdierReadoutPathBoundary.{u}).app _ =
    curry (verdierReadoutBoundaryDiagram d L hL hfull))
include hT



/-- 概要：同じ動く上側入力の始端は元の実上側の全 native Hom。
方針：同じ相対合成の始端を curry の全 Hom 頂点へ戻す。
規約：直接辺や群作用だけの一致ではない。使われ方：指定上側始端の回収。 -/
theorem verdierReadoutMovingLongInput_first :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue (verdierReadoutMovingLongInput d L hL hfull H T hT)).app
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)) := by
  rw [verdierReadoutMovingLongInput_value, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.curry_app_vertex]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H.h₀

/-- 概要：同じ動く上側入力の終端は元の実包含・商の合成端の全定値 native Hom。
方針：同じ相対合成の終端を curry の全 Hom 頂点へ戻す。
規約：元の合成端を保持。使われ方：指定上側終端の回収。 -/
theorem verdierReadoutMovingLongInput_last :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue (verdierReadoutMovingLongInput d L hL hfull H T hT)).app
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const
        (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1)) := by
  rw [verdierReadoutMovingLongInput_value, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.curry_app_vertex]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H.h₁

/-- 概要：元の動く上側族の始端の全 native Hom は元の実上側のもの。
方針：同じ実入力の始端を canonical encoder の native 回収へ代入する。
規約：二胞体自体の厳密一致は別の有限端点照合。使われ方：その照合の長 Hom 条件。 -/
theorem verdierMovingUpperFamily_first_native :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
          (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have h := verdierMovingUpperFamily_native d
    (verdierReadoutMovingLongInput d L hL hfull H T hT)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  rw [verdierReadoutMovingLongInput_first] at h
  exact h

/-- 概要：元の動く上側族の終端の全 native Hom は元の実合成端の全定値族。
方針：同じ実入力の終端を canonical encoder の native 回収へ代入する。
規約：二胞体自体の同定は別工程。使われ方：指定終端の有限照合の長 Hom 条件。 -/
theorem verdierMovingUpperFamily_last_native :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const
        (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
          (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have h := verdierMovingUpperFamily_native d
    (verdierReadoutMovingLongInput d L hL hfull H T hT)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  rw [verdierReadoutMovingLongInput_last] at h
  exact h

end SerrePositivity.KST.Fibration
