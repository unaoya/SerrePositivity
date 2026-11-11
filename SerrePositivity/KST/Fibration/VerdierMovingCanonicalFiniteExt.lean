module
public import SerrePositivity.KST.Fibration.VerdierMovingCanonicalSquareComparison
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalFiniteFaces
public import SerrePositivity.KST.Fibration.VerdierMovingUpperLastComparison
public import SerrePositivity.InfinityCategories.Project.Entrypoints.NativeTriangleSupplyAll

/-!
概要：S-1 (a) の native 二単体外延性を四つの元の有限端点へ代入する。
方針：二短辺と全 native 長 Hom の既存照合で、上下両端の二単体を同定する。
規約：外延性の存在仮定を取らず、F1 正本の実証明を使う。
使われ方：K-6 c4 の正規化四角柱を元の Verdier・商核四角形へ接続する。
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
open SerrePositivity.KST.Fibration
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



/-- 概要：元の実読出しと相対合成から全四角形の関手同型を構成する。
方針：S-1 (a) を四有限端点へ代入し、既存の二つの四角柱を合成する。
規約：hExt や有限端点同定は引数に取らない。
使われ方：実読出し・相対合成の存在定理を使う c4 の無条件比較。 -/
def kbMovingCanonicalFiniteExtConsumer :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection) := by
  let ℓ := verdierReadoutMovingLongInput d L hL hfull H T hT
  let n := verdierLowerCanonicalReadout d L hfull
  have hU₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1]) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeTriangle_ext _ _ _ (verdierMovingUpperFamily_first_controlled_delta_zero d ℓ)
      (verdierMovingUpperFamily_first_controlled_delta_two d ℓ)
      (verdierMovingUpperFamily_first_controlled_native d L hL hfull H T hT)
  have hN₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d n)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) := by
    apply SSet.yonedaEquiv.injective
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeTriangle_ext _ _ _ (verdierLowerCanonicalFamily_first_delta_zero d n)
      (verdierLowerCanonicalFamily_first_delta_two d n)
      (verdierLowerCanonicalReadout_first_native d L hfull hL)).trans
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply _).symm
  have hU₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingUpperFamily d ℓ)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (verdierMovingUpperLastTriangle d).simplex := by
    apply SSet.yonedaEquiv.injective
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeTriangle_ext _ _ _ (verdierMovingUpperFamily_last_standard_delta_zero d ℓ)
      (verdierMovingUpperFamily_last_standard_delta_two d ℓ)
      (verdierMovingUpperFamily_last_standard_native d L hL hfull H T hT)).trans
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply _).symm
  have hN₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierLowerCanonicalFamily d n)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) := by
    apply SSet.yonedaEquiv.injective
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeTriangle_ext _ _ _ (verdierLowerCanonicalFamily_last_delta_zero d n)
      (verdierLowerCanonicalFamily_last_delta_two d n)
      (verdierLowerCanonicalReadout_last_native d L hfull hL)).trans
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).apply_symm_apply _).symm
  exact verdierMovingCanonicalKernelSquareIso d L hL hfull H T hT hU₀ hN₀ hU₁ hN₁


end SerrePositivity.KST.Fibration
