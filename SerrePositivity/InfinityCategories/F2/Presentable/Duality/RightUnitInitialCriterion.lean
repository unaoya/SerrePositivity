module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitInitial

/-!
概要：固定右の実単位の随伴条件と、元の coslice 内での始対象性の同値。
方針：指定単位の後合成の随伴による局所判定と、始対象の同型一意性を組み合わせる。
規約：元の実単位の頂点ごとの条件を厳密に比較する。
使われ方：右ファイバーの普遍単位空間による可縮性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：任意の実単位の比較頂点を、その元の左関手上の comma fiber に保持する。
方針：標準の固定標的の fiber 比較を適用する。
規約：元の coslice の頂点を保持する。
使われ方：任意の実単位の始対象性を comma の判定で検証する。 -/
def rightUnitComparisonPoint {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} (v : RightUnitCoslice C D w _⦋0⦌) :
    vertexFiber (F1B.unitCommaFiberProjection ((ihom C.obj).map (rightVertexFunctor w))
      (functorVertex (𝟙 C.obj))) (functorVertex (rightUnitLeftFunctor v)) _⦋0⦌ :=
  (vertexFiberMap (pullback.snd (sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      ((ihom C.obj).map (rightVertexFunctor w)))
    (F1B.unitCommaFiberProjection ((ihom C.obj).map (rightVertexFunctor w))
      (functorVertex (𝟙 C.obj)))
    (HomotopyLimits.cosliceCommaComparison _ _)
    (HomotopyLimits.cosliceCommaComparison_projection _ _)
    (functorVertex (rightUnitLeftFunctor v))).app (Opposite.op ⦋0⦌)
      ⟨v, by rw [pinchedConstant_zero]; exact (rightUnitLeftFunctor_vertex v).symm⟩

/-- 概要：任意の実単位の比較後の矢印の Hom 類は元の単位。
方針：固定標的の比較による同じ辺の回収を Hom 類へ移す。
規約：元の指定単位の表す射を保つ。
使われ方：後合成の単位成分による始対象性の判定。 -/
lemma rightUnitComparisonPoint_hom {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} (v : RightUnitCoslice C D w _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
      (HomotopyLimits.commaTargetFiberArrow ((ihom C.obj).map (rightVertexFunctor w))
        (functorVertex (𝟙 C.obj)) (functorVertex (rightUnitLeftFunctor v))
        (rightUnitComparisonPoint v)).toTruncated = rightUnitHom v := by
  apply eq_of_heq
  exact edgeHom_heq _ _ (cosliceCommaComparison_fiberArrow_edge
    ((ihom C.obj).map (rightVertexFunctor w)) (functorVertex (𝟙 C.obj))
    (functorVertex (rightUnitLeftFunctor v))
    ⟨v, by rw [pinchedConstant_zero]; exact (rightUnitLeftFunctor_vertex v).symm⟩)

/-- 概要：指定単位の随伴条件を満たす固定右の coslice 頂点は始対象。
方針：同じ単位から後合成の随伴を作り、その恒等関手での成分で判定する。
規約：元の実単位の頂点そのものの始対象性を示す。
使われ方：随伴単位の空間を普遍単位の全部分空間へ送る。 -/
lemma rightUnit_isInitial_of_condition {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} (v : RightUnitCoslice C D w _⦋0⦌)
    (hv : UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v)) : IsInitialVertex v := by
  let H := functorHomHomotopy (rightUnitHom v)
  have hH : UnitMappingSpaceCondition
      (F := rightUnitLeftFunctor v) (G := rightVertexFunctor w)
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) := by
    rw [functorHomHomotopy_hom]
    exact hv
  let b := HomotopyLimits.postcompositionAdjunctionOfUnitHomotopy H hH C.obj
  let η := SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (HomotopyLimits.postcompositionUnitHomotopy H C.obj))
  have hη : UnitMappingSpaceCondition (F := (ihom C.obj).map (rightUnitLeftFunctor v))
      (G := (ihom C.obj).map (rightVertexFunctor w)) η := by
    have h := b.unitMappingSpaceCondition
    rw [HomotopyLimits.postcompositionAdjunctionOfUnitHomotopy_unitHom] at h
    exact h
  have hi := commaTargetFiber_isInitial_of_unitComponent η hη (functorVertex (𝟙 C.obj))
    (rightUnitComparisonPoint v) ((rightUnitComparisonPoint_hom v).trans
      ((postcompositionUnit_identity_component H).trans
        (functorHomHomotopy_hom (rightUnitHom v))).symm)
  exact ((rightUnitCosliceComparison_isQCatEquivalence C D w).choose.isInitialVertex_iff v).mpr hi

/-- 概要：固定右の coslice の始対象の単位は元の随伴の指定単位となる。
方針：d の随伴の基準頂点との始対象同型で同じ単位条件を移す。
規約：随伴の存在を追加仮定にはせず、presentable 性から構成する。
使われ方：普遍単位の空間から元の随伴条件を回収する。 -/
lemma rightUnit_condition_of_isInitial {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} (v : RightUnitCoslice C D w _⦋0⦌)
    (hv : IsInitialVertex v) :
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v) := by
  let a := chosenLeftAdjunction w
  exact rightUnitCondition_of_vertexIso (initialVertexIso (rightUnitVertex_isInitial a) hv)
    (rightUnitVertex_condition a)

/-- 概要：元の固定右 coslice の随伴単位条件は始対象性と同値。
方針：指定単位の局所判定と基準随伴の単位の始対象同型を組み合わせる。
規約：元の実単位の全部分複体を定める同じ頂点条件の同値。
使われ方：右射影のファイバーの可縮な普遍単位模型との比較。 -/
lemma rightUnit_condition_iff_isInitial {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} (v : RightUnitCoslice C D w _⦋0⦌) :
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v) ↔ IsInitialVertex v :=
  ⟨rightUnit_isInitial_of_condition v, rightUnit_condition_of_isInitial v⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
