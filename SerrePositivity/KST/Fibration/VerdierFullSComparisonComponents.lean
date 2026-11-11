module
public import SerrePositivity.KST.Fibration.FixedRestrictionFunctorComponent
public import SerrePositivity.KST.Fibration.VerdierOriginalFullSHomFamily
public import SerrePositivity.KST.Fibration.VerdierLowerNativeReadoutHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：元の全 S• 比較と同じ実下側読出しから、指定境界合成の二つの実単位辺を回収する。
方針：直接端の固定制限と合成端の全時刻定値性を同じ成分評価へ渡す。
規約：元の比較・読出し・全長 Hom を保持し、新たな存在仮定を加えない。
使われ方：K-6 c4 の指定境界二単体の直接端・合成端の単位条件。
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

/-- 概要：同じ全 S• 比較の core 制限の直接端成分は元の実恒等辺。
方針：所有する固定部分比較の成分回収を同じ core 制限へ写す。
規約：別の core 比較を選ばず、実一単体を保持する。
使われ方：元の上下全長 Hom の合成の直接端側の単位。 -/
theorem verdierOriginalFullSCoreHomotopy_direct_edge
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierOriginalFullSCoreHomotopy d j k)
      (ComposableArrows.mk₀ coherentTriangleDirectPath)).edge =
      (Truncated.Edge.id (X := (truncation 2).obj (verdierOriginalNativeHomTarget d))
        ((verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentTriangleDirectPath))).edge := by
  let E := verdierOriginalFullSHomComparison d j k
  let p := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion
    (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj
  have hv : coherentTriangleDirectVertexMap.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
        ComposableArrows.mk₀ coherentTriangleDirectPath.{u} := by
    rw [coherentTriangleDirectVertexMap, SSet.yonedaEquiv_symm_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
      (ComposableArrows.mk₀ coherentTriangleDirectPath.{u}) 0 = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _
  have he := E.component_at (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [hv] at he
  have hi := congrArg Truncated.Edge.edge
    (Truncated.Edge.map_id
      ((verdierOriginalFullSHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath)) ((truncation 2).map p))
  have hp : p.app (Opposite.op ⦋0⦌)
      ((verdierOriginalFullSHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath)) =
      (verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath) :=
    congrArg (fun f => f.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleDirectPath)) (verdierOriginalFullSHomFamily_core d j)
  change p.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge E.edge)
      (ComposableArrows.mk₀ coherentTriangleDirectPath)).edge = _
  rw [he]
  change p.app (Opposite.op ⦋1⦌)
    (Truncated.Edge.id (X := (truncation 2).obj (SimplicialCategory.sHom
      (fullSRealizationKanObject d.left)
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))))
      ((verdierOriginalFullSHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath))).edge = _
  change _ = (Truncated.Edge.id (X := (truncation 2).obj (verdierOriginalNativeHomTarget d))
    (p.app (Opposite.op ⦋0⦌)
      ((verdierOriginalFullSHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath)))).edge at hi
  exact hi.trans (congrArg
    (fun v => (Truncated.Edge.id (X := (truncation 2).obj
      (verdierOriginalNativeHomTarget d)) v).edge) hp)

/-- 概要：宇宙を上げても同じ直接端の成分は元の実恒等辺。
方針：同じ成分回収をホモトピーの宇宙持ち上げへ送る。
規約：同じ元の比較と同じ指定点を保持する。
使われ方：K-6 c4 の大きい宇宙での指定境界単位二単体。 -/
theorem verdierOriginalFullSCoreHomotopy_up_direct_edge
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplicialHomotopy.{u, u + 1} (verdierOriginalFullSCoreHomotopy d j k))
      (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath))).edge =
      (Truncated.Edge.id (X := (truncation 2).obj (verdierNativeLongHomTarget d))
        (ULift.up ((verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentTriangleDirectPath)))).edge := by
  have h := congrArg Truncated.Edge.edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftSimplicialHomotopy_vertexEdge.{u, u + 1}
      (verdierOriginalFullSCoreHomotopy d j k)
      (ComposableArrows.mk₀ coherentTriangleDirectPath))
  exact h.trans (congrArg ULift.up (verdierOriginalFullSCoreHomotopy_direct_edge d j k))

/-- 概要：同じ実下側読出しの合成 path 成分は元の実合成端の恒等辺。
方針：全時刻定値性を元の実区間一単体で評価する。
規約：終端一点だけでなく元の全時刻条件を消費する。
使われ方：指定境界合成の合成端側の単位二単体。 -/
theorem verdierLowerNativeReadoutHomotopy_full_edge (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hL : VerdierLowerNativeReadoutRecovery d L)
    (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1]) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL)
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u}))).edge =
      (Truncated.Edge.id (X := (truncation 2).obj (verdierNativeLongHomTarget d))
        (verdierNativeCompositePoint d 1)).edge := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    (verdierLowerNativeReadoutHomotopy_full d L hL hfull)
  change (verdierLowerNativeReadoutHomotopy d L hL).h.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) 1,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (verdierNativeCompositePoint d 1) 1 at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] at h
  exact h

end SerrePositivity.KST.Fibration
