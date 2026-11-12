module
public import SerrePositivity.KST.Fibration.VerdierMovingCanonicalSquareIso
public import SerrePositivity.KST.Fibration.VerdierMovingUpperKernelTriangle
public import SerrePositivity.KST.Fibration.QuotientSKernelPositiveStages

/-!
概要：正規化四角柱の指定終端照合を、同じ実全 S• 商核へ接続する。
方針：二つの実終端二胞体を厳密回収し、同じ柱の全関手同型で引き戻し性を移す。
規約：有限端点照合と商比較の正段入力に条件付き。両入力の存在は主張しない。
使われ方：K-6 c4 の実全族構成から c5 の元の商実現比較への利用側。
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
open SerrePositivity.SimplicialModel
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


variable
  (hUpper : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
    (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex)
  (hLower : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
    (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull))
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)))

include hUpper hLower

/-- 概要：指定両終端二胞体の照合から同じ四角柱の終端を実商核へ厳密に戻す。
方針：同じ四角柱の両三角形制限と押し出しの外延性を使う。
規約：hUpper・hLower に条件付き。境界の一致だけで二胞体を代用しない。
使われ方：有限二胞体の実照合供給後の全四角形回収。 -/
theorem verdierMovingCanonicalSquareFamily_last_kernel :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      quotientSKernelFullInfinitySquare d.isVerdier := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingCanonicalSquareFamily_upper]
    exact hUpper.trans (verdierMovingUpperLastTriangle_kernel d)
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingCanonicalSquareFamily_lower]
    exact hLower.trans (quotientSKernelFullInfinitySquare_lower_maximalization d).symm

/-- 概要：指定終端照合と元の商の正段比較から、同じ四角柱の始端が引き戻し。
方針：同じ実商核の引き戻し性を、同じ柱から構成した全関手同型で移す。
規約：hUpper・hLower と各正段比較に条件付き。Sp 正本の局所化入力を無条件化しない。
使われ方：K-6 c4 の有限照合と c5 の商実現比較の実供給を分離する。 -/
theorem verdierMovingCanonicalSquareFamily_first_isPullback_of_positive_stages
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap d.projection (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  have hp := (quotientSKernelFullInfinitySquare_isPullback_iff d.isVerdier).mp
    (quotientSKernelInfinitySquare_isPullback_of_positive_stages
      d.inclusion d.projection d.isVerdier hq)
  have he := verdierMovingCanonicalSquareFamily_last_kernel d L hL hfull H T hT hUpper hLower
  have hp' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
      (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := he.symm ▸ hp
  exact hp'.of_functorIso (verdierMovingCanonicalSquareEndpointIso d L hL hfull H T hT).symm

end SerrePositivity.KST.Fibration
