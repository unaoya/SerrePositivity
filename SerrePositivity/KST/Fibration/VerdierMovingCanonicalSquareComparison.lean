module
public import SerrePositivity.KST.Fibration.VerdierMovingCanonicalKernelEndpoint
public import SerrePositivity.KST.Fibration.VerdierNativeControlledSquareIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：指定四有限端点の照合から、同じ実正規化四角柱を元の Verdier・商核四角形へ戻す。
方針：同じ実 (9b) の対角固定四角柱と正規化四角柱の全関手同型を合成する。
規約：四端点照合に条件付き。元の全族の存在・縦辺可逆性は実供給を使う。
使われ方：K-6 c4 の F1 有限外延性の消費後に c5 の商実現比較を代入する実入口。
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
  (hU₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
    (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1]) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
  (hN₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
    (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull))
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d))
include hU₀ hN₀

/-- 概要：同じ正規化四角柱の始端は元の実 (9b) 制御四角形へ厳密に戻る。
方針：実上下制限と指定二つの有限二胞体照合を使う。
規約：hU₀・hN₀ に条件付き。境界の等号だけで代用しない。
使われ方：同じ実対角固定三角柱への接続。 -/
theorem verdierMovingCanonicalSquareFamily_first_controlled :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      verdierNativeControlledSquare d (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingCanonicalSquareFamily_upper,
      verdierNativeControlledSquare_upper]
    exact hU₀
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex_precomp, verdierMovingCanonicalSquareFamily_lower,
      verdierNativeControlledSquare_lower]
    exact hN₀.trans (verdierFullSLowerSimplex_original d)

variable
  (hU₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
    (verdierMovingUpperFamily d (verdierReadoutMovingLongInput d L hL hfull H T hT))
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex)
  (hN₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
    (verdierLowerCanonicalFamily d (verdierLowerCanonicalReadout d L hfull))
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)))
include hU₁ hN₁

/-- 概要：四つの指定有限端点照合から元の Verdier 四角形と実全 S• 商核の全関手同型。
方針：同じ制御四角柱の逆と同じ正規化四角柱を、元の有限端点で合成する。
規約：hU₀・hN₀・hU₁・hN₁ に条件付き。新しい全族存在入力は取らない。
使われ方：F1 外延性の供給後に無条件化する c4 の実比較。 -/
def verdierMovingCanonicalFullKernelSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelFullInfinitySquare d.isVerdier) :=
  (verdierNativeControlledSquarePrismIso d (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (verdierMovingCanonicalSquareEndpointIso d L hL hfull H T hT)
      (verdierMovingCanonicalSquareFamily_first_controlled d L hL hfull H T hT hU₀ hN₀)
      (verdierMovingCanonicalSquareFamily_last_kernel d L hL hfull H T hT hU₁ hN₁)

/-- 概要：同じ四有限端点照合から元の Verdier 四角形を元の相対 S 商核へ比較する。
方針：同じ全 S• 零角同型の逆を末尾に合成する。
規約：四端点照合に条件付き。使われ方：c5 の元の実商比較への入力。 -/
def verdierMovingCanonicalKernelSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection) :=
  verdierMovingCanonicalFullKernelSquareIso d L hL hfull H T hT hU₀ hN₀ hU₁ hN₁ ≪≫
    (quotientSKernelFullSquareIso d.isVerdier).symm

/-- 概要：四端点照合と商の正段比較から元の Verdier 全 S• 四角形は引き戻し。
方針：元の実商核の引き戻し性を同じ全関手同型で移す。
規約：四端点照合と各正段比較に条件付き。局所化の存在を結論しない。
使われ方：K-6 c4 と c5 の実供給を同じ入力列へ接続する。 -/
theorem verdierMovingCanonicalSquare_isPullback_of_positive_stages
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap d.projection (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) := by
  exact (quotientSKernelInfinitySquare_isPullback_of_positive_stages
    d.inclusion d.projection d.isVerdier hq).of_functorIso
      (verdierMovingCanonicalKernelSquareIso d L hL hfull H T hT hU₀ hN₀ hU₁ hN₁).symm

end SerrePositivity.KST.Fibration
