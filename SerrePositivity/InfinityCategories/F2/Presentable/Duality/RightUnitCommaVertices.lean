module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitVertices
public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitRepresentative
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices

/-!
概要：固定右の coslice–comma 比較が同じ実単位の辺を保持することを検証する。
方針：固定した左関手上の fiber 比較を区間模型で計算する。
規約：単位の Hom 類だけでなく元の一次単体を照合する。
使われ方：普遍単位の comma 始対象性を元の coslice へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：coslice–comma 比較の固定標的の辺は元の実単位の辺。
方針：fiber 比較の等式を頂点で読み、coslice の区間表示の往復を使う。
規約：任意の関手 G と元の coslice の頂点を扱う。
使われ方：比較後の単位の Hom 類と元の指定単位の同定。 -/
lemma cosliceCommaComparison_fiberArrow_edge {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (v : vertexFiber (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) y _⦋0⦌) :
    (HomotopyLimits.commaTargetFiberArrow G x y
      ((vertexFiberMap (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)
        (F1B.unitCommaFiberProjection G x) (HomotopyLimits.cosliceCommaComparison G x)
        (HomotopyLimits.cosliceCommaComparison_projection G x) y).app (Opposite.op ⦋0⦌) v)).edge =
    (sliceUnderVertexEdge x ((pullback.fst (sliceUnderProjection
      (SSet.yonedaEquiv.symm x)) G).app (Opposite.op ⦋0⦌) v.val)).edge := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
    (HomotopyLimits.cosliceCommaComparison_fiber G x y)
  refine (congrArg (fun z ↦ (intervalMappingEdgeOfVertex (X := X) z).edge) h).trans ?_
  change (intervalMappingEdgeOfVertex ((cosliceFiberToIntervalMappingSpace x
    (G.app (Opposite.op ⦋0⦌) y)).app (Opposite.op ⦋0⦌)
      ((cofinalVertexFiberBaseChangeIso (sliceUnderProjection
        (SSet.yonedaEquiv.symm x)) G y).hom.app (Opposite.op ⦋0⦌) v))).edge = _
  rw [cosliceFiberToIntervalMappingSpace_vertex]
  exact congrArg (fun e : X.Edge x (G.app (Opposite.op ⦋0⦌) y) ↦ e.edge)
    ((intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _)

/-- 概要：指定随伴単位の成分と同じ矢印を持つ comma の点は始対象。
方針：同じ Hom 類の頂点の同型と、単位条件による指定頂点の始対象性を使う。
規約：同じ標的の二重 fiber の中で単位の代表を照合する。
使われ方：実単位を保つ coslice 比較から始対象性を反映する。 -/
lemma commaTargetFiber_isInitial_of_unitComponent {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (hη : UnitMappingSpaceCondition η) (x : X _⦋0⦌)
    (v : vertexFiber (F1B.unitCommaFiberProjection G x) (F.app (Opposite.op ⦋0⦌) x) _⦋0⦌)
    (hv : SSet.Truncated.HomotopyCategory.homMk
      (HomotopyLimits.commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x) v).toTruncated =
        qcatUnitComponent η x) : IsInitialVertex v.val := by
  let w := HomotopyLimits.unitCommaSectionTargetFiberVertex η x
  have he := hv.trans (HomotopyLimits.unitCommaSectionTargetFiberArrow_hom η x).symm
  exact (HomotopyLimits.unitCommaTargetFiber_isInitial_iff_of_homMk_eq G x _ v w he).mpr
    ((unitCommaInitialCondition_iff η).mp hη.unitCommaInitialCondition x)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
