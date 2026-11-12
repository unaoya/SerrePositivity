module
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalReadout
public import SerrePositivity.KST.Fibration.VerdierMovingSharedDiagonal

/-!
概要：全 native Hom を保持する同じ正規化下側と動く上側の全共有対角を接続する。
方針：元の同じ読出しを下側の実 encoder と上側の実相対合成へ同時に渡す。
規約：厳密切断を要求せず、全族の同じ直接端だけを厳密に貼る。
使われ方：K-6 c4 の両有限端点を保持した正規化四角柱。
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


/-- 概要：元の同じ読出しによる実上下族は全共有対角で厳密に一致する。
方針：実 canonical encoder の対角と同じ相対合成の指定直接端を照合する。
規約：下側の全 native Hom と元の族への可逆比較を保持したまま貼る。
使われ方：指定有限端点を残す正規化四角柱の実構成。 -/
theorem verdierMovingCanonicalSharedDiagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull) =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT) := by
  have hN := verdierLowerCanonicalFamily_diagonal d
    (verdierLowerCanonicalReadout d L hfull)
  rw [verdierLowerCanonicalReadout_value] at hN
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso_inv_first.{u, u + 1}).symm.trans
    (coherentTriangleInterval_up_first.{u})
  rw [hp] at hN
  have hlow : verdierLowerNativeLongHomTransport d Δ[1] L ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})) =
      (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))) ≫
        eqToHom (verdierLowerNativeLongHomTarget_eq d) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  have hd := verdierReadoutMovingLongInput_direct d L hL hfull H T hT
  have hF := verdierMovingUpperFamily_diagonal d
    (verdierReadoutMovingLongInput d L hL hfull H T hT)
  exact (hN.trans (verdierLowerNativeDiagonal_transport d Δ[1]
    (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}))))).trans
      ((congrArg (verdierNativeDiagonalFamily d Δ[1]) (hd.trans hlow).symm).trans hF.symm)

end SerrePositivity.KST.Fibration
