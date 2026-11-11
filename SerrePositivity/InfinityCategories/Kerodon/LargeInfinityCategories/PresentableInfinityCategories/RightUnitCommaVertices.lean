module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitVertices
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaUnitRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices

/-!
概要：固定右の coslice–comma 比較が同じ実単位の辺を保持することを検証する。
方針：固定した左関手上の fiber 比較を区間模型で計算する。
規約：単位の Hom 類だけでなく元の一次単体を照合する。
使われ方：普遍単位の comma 始対象性を元の coslice へ移す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：coslice–comma 比較の固定標的の辺は元の実単位の辺。
方針：fiber 比較の等式を頂点で読み、coslice の区間表示の往復を使う。
規約：任意の関手 G と元の coslice の頂点を扱う。
使われ方：比較後の単位の Hom 類と元の指定単位の同定。 -/
lemma cosliceCommaComparison_fiberArrow_edge {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) y _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCommaComparison G x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCommaComparison_projection G x) y).app (Opposite.op ⦋0⦌) v)).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge x ((pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (SSet.yonedaEquiv.symm x)) G).app (Opposite.op ⦋0⦌) v.val)).edge := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceCommaComparison_fiber G x y)
  refine (congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (X := X) z).edge) h).trans ?_
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x
    (G.app (Opposite.op ⦋0⦌) y)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
        (SSet.yonedaEquiv.symm x)) G y).hom.app (Opposite.op ⦋0⦌) v))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_vertex]
  exact congrArg (fun e : X.Edge x (G.app (Opposite.op ⦋0⦌) y) ↦ e.edge)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _)

/-- 概要：指定随伴単位の成分と同じ矢印を持つ comma の点は始対象。
方針：同じ Hom 類の頂点の同型と、単位条件による指定頂点の始対象性を使う。
規約：同じ標的の二重 fiber の中で単位の代表を照合する。
使われ方：実単位を保つ coslice 比較から始対象性を反映する。 -/
lemma commaTargetFiber_isInitial_of_unitComponent {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (x : X _⦋0⦌)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) (F.app (Opposite.op ⦋0⦌) x) _⦋0⦌)
    (hv : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x) v).toTruncated =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v.val := by
  let w := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η x
  have he := hv.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberArrow_hom η x).symm
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaTargetFiber_isInitial_iff_of_homMk_eq G x _ v w he).mpr
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff η).mp hη.unitCommaInitialCondition x)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
