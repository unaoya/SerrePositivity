module
public import SerrePositivity.KST.Fibration.VerdierMovingCanonicalSquare
public import SerrePositivity.KST.Fibration.VerdierLowerCanonicalVerticalEdges
public import SerrePositivity.KST.Fibration.VerdierMovingUpperVerticalEdges

/-!
概要：同じ正規化四角柱の全縦辺の可逆性から、両端の全関手同型を構成する。
方針：元の上下三角柱の全制限を回収し、四頂点を覆う。
規約：指定有限端点との同定は分離し、新しい可逆性仮定を要求しない。
使われ方：K-6 c4 の有限二胞体照合後に元の四角形比較へ渡す実全関手同型。
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


/-- 概要：同じ正規化四角柱を、同じ両端四角形間の実ホモトピーとして読む。
方針：元の全族の二端点制限を使う。
規約：上下族を選び直さない。使われ方：全四頂点の縦辺判定。 -/
def verdierMovingCanonicalSquareHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) where
  h := verdierMovingCanonicalSquareFamily d L hL hfull H T hT
  h₀ := rfl
  h₁ := rfl
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：同じ正規化四角柱の四頂点すべての縦辺が可逆。
方針：同じ実上側と正規化下側の三頂点で四頂点を覆う。
規約：縦辺の可逆性に追加仮定なし。使われ方：両端の全関手同型。 -/
theorem verdierMovingCanonicalSquareHomotopy_pointwise :
    ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (verdierMovingCanonicalSquareHomotopy d L hL hfull H T hT) k).toTruncated := by
  have hu (a : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (verdierMovingCanonicalSquareHomotopy d L hL hfull H T hT)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app (Opposite.op ⦋0⦌) a)).toTruncated := by
    have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
      f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
      (verdierMovingCanonicalSquareFamily_upper d L hL hfull H T hT)
    change (verdierMovingCanonicalSquareFamily d L hL hfull H T hT).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 a),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at he
    rw [σ_naturality_apply] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
      (verdierMovingUpperHomotopy_pointwise d
        (verdierReadoutMovingLongInput d L hL hfull H T hT) a)
  have hl (a : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (verdierMovingCanonicalSquareHomotopy d L hL hfull H T hT)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1).app (Opposite.op ⦋0⦌) a)).toTruncated := by
    have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
      f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 a), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge))
      (verdierMovingCanonicalSquareFamily_lower d L hL hfull H T hT)
    change (verdierMovingCanonicalSquareFamily d L hL hfull H T hT).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 a),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _ at he
    rw [σ_naturality_apply] at he
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
      (verdierLowerCanonicalHomotopy_pointwise d (verdierLowerCanonicalReadout d L hfull) a)
  rintro ⟨k₀, k₁⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k₀
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k₁
  fin_cases i <;> fin_cases j
  · exact hu (stdSimplex.obj₀Equiv.symm 0)
  · exact hu (stdSimplex.obj₀Equiv.symm 1)
  · exact hl (stdSimplex.obj₀Equiv.symm 1)
  · exact hu (stdSimplex.obj₀Equiv.symm 2)

/-- 概要：同じ正規化四角柱の両端は実全関手同型で結ばれる。
方針：元の全四角柱の全縦辺可逆性を適用する。
規約：有限端点の旧四角形への同定はまだ仮定せず、新しい供給命題も要求しない。
使われ方：K-6 c4 の元の指定二胞体への照合後の引き戻し移送。 -/
def verdierMovingCanonicalSquareEndpointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierMovingCanonicalSquareFamily d L hL hfull H T hT)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _
    (verdierMovingCanonicalSquareHomotopy_pointwise d L hL hfull H T hT)

end SerrePositivity.KST.Fibration
