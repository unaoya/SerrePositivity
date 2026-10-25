module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitInitial

/-!
概要：固定左の実単位の随伴条件と、元の coslice 内での始対象性の同値。
方針：指定単位の前合成の随伴による局所判定と、始対象の同型一意性を組み合わせる。
規約：元の実単位の頂点ごとの条件を厳密に比較する。
使われ方：左ファイバーの普遍単位空間による可縮性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：任意の実単位の比較頂点を、その元の右関手上の comma fiber に保持する。
方針：標準の固定標的の fiber 比較を適用する。
規約：元の coslice の頂点を保持する。
使われ方：任意の実単位の始対象性を comma の判定で検証する。 -/
def leftUnitComparisonPoint {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} (v : LeftUnitCoslice C D w _⦋0⦌) :
    vertexFiber (F1B.unitCommaFiberProjection ((pre (leftVertexFunctor w)).app C.obj)
      (functorVertex (𝟙 C.obj))) (functorVertex (leftUnitRightFunctor v)) _⦋0⦌ :=
  (vertexFiberMap (pullback.snd (sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      ((pre (leftVertexFunctor w)).app C.obj))
    (F1B.unitCommaFiberProjection ((pre (leftVertexFunctor w)).app C.obj)
      (functorVertex (𝟙 C.obj)))
    (HomotopyLimits.cosliceCommaComparison _ _)
    (HomotopyLimits.cosliceCommaComparison_projection _ _)
    (functorVertex (leftUnitRightFunctor v))).app (Opposite.op ⦋0⦌)
      ⟨v, by rw [pinchedConstant_zero]; exact (leftUnitRightFunctor_vertex v).symm⟩

/-- 概要：任意の実単位の比較後の矢印の Hom 類は元の単位。
方針：固定標的の比較による同じ辺の回収を Hom 類へ移す。
規約：元の指定単位の表す射を保つ。
使われ方：前合成の単位成分による始対象性の判定。 -/
lemma leftUnitComparisonPoint_hom {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} (v : LeftUnitCoslice C D w _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
      (HomotopyLimits.commaTargetFiberArrow ((pre (leftVertexFunctor w)).app C.obj)
        (functorVertex (𝟙 C.obj)) (functorVertex (leftUnitRightFunctor v))
        (leftUnitComparisonPoint v)).toTruncated = leftUnitHom v := by
  apply eq_of_heq
  exact edgeHom_heq _ _ (cosliceCommaComparison_fiberArrow_edge
    ((pre (leftVertexFunctor w)).app C.obj) (functorVertex (𝟙 C.obj))
    (functorVertex (leftUnitRightFunctor v))
    ⟨v, by rw [pinchedConstant_zero]; exact (leftUnitRightFunctor_vertex v).symm⟩)

/-- 概要：指定単位の随伴条件を満たす固定左の coslice 頂点は始対象。
方針：同じ単位から前合成の随伴を作り、その恒等関手での成分で判定する。
規約：元の実単位の頂点そのものの始対象性を示す。
使われ方：随伴単位の空間を普遍単位の全部分空間へ送る。 -/
lemma leftUnit_isInitial_of_condition {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} (v : LeftUnitCoslice C D w _⦋0⦌)
    (hv : UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v)) : IsInitialVertex v := by
  let a : QCatAdjunction (leftVertexFunctor w) (leftUnitRightFunctor v) :=
    qcatAdjunctionOfUnitMappingSpaceCondition (leftUnitHom v) hv
  let b := precompositionAdjunction (Z := C.obj) a
  have hu : a.unitHom = leftUnitHom v :=
    qcatAdjunctionOfUnitMappingSpaceCondition_unitHom (leftUnitHom v) hv
  have hc := (precompositionAdjunction_unitComponent_identity a).trans hu
  have hi := commaTargetFiber_isInitial_of_unitComponent b.unitHom b.unitMappingSpaceCondition
    (functorVertex (𝟙 C.obj)) (leftUnitComparisonPoint v)
    ((leftUnitComparisonPoint_hom v).trans hc.symm)
  exact ((leftUnitCosliceComparison_isQCatEquivalence C D w).choose.isInitialVertex_iff v).mpr hi

/-- 概要：固定左の coslice の始対象の単位は元の随伴の指定単位となる。
方針：d の随伴の基準頂点との始対象同型で同じ単位条件を移す。
規約：随伴の存在を追加仮定にはせず、presentable 性から構成する。
使われ方：普遍単位の空間から元の随伴条件を回収する。 -/
lemma leftUnit_condition_of_isInitial {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} (v : LeftUnitCoslice C D w _⦋0⦌)
    (hv : IsInitialVertex v) :
    UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v) := by
  let a := chosenRightAdjunction w
  exact leftUnitCondition_of_vertexIso (initialVertexIso (leftUnitVertex_isInitial a) hv)
    (leftUnitVertex_condition a)

/-- 概要：元の固定左 coslice の随伴単位条件は始対象性と同値。
方針：指定単位の局所判定と基準随伴の単位の始対象同型を組み合わせる。
規約：元の実単位の全部分複体を定める同じ頂点条件の同値。
使われ方：右射影のファイバーの可縮な普遍単位模型との比較。 -/
lemma leftUnit_condition_iff_isInitial {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} (v : LeftUnitCoslice C D w _⦋0⦌) :
    UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v) ↔ IsInitialVertex v :=
  ⟨leftUnit_isInitial_of_condition v, leftUnit_condition_of_isInitial v⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
