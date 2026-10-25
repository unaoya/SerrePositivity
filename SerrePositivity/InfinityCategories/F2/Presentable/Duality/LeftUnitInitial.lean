module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitVertices
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitCommaVertices
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PrecompositionUnitComponent

/-!
概要：元の随伴の実単位の coslice 頂点の始対象性。
方針：前合成の指定単位の成分を comma 内で比較し、標準同値で始対象性を反映する。
規約：単位の代表を比較した同じ頂点に対して始対象性を証明する。
使われ方：左ファイバーの像を普遍単位の全部分空間と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：指定随伴の coslice 頂点の比較を、元の右関手上の comma fiber に保持する。
方針：同じ頂点を固定標的の標準 fiber 比較へ入れる。
規約：左右の元の関手は変えない。
使われ方：元の単位と comma の矢印を照合する。 -/
def leftUnitComparisonVertex {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : QCatAdjunction (leftVertexFunctor w) R) :
    vertexFiber (F1B.unitCommaFiberProjection ((pre (leftVertexFunctor w)).app C.obj)
      (functorVertex (𝟙 C.obj))) (functorVertex R) _⦋0⦌ :=
  (vertexFiberMap (pullback.snd (sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      ((pre (leftVertexFunctor w)).app C.obj))
    (F1B.unitCommaFiberProjection ((pre (leftVertexFunctor w)).app C.obj)
      (functorVertex (𝟙 C.obj)))
    (HomotopyLimits.cosliceCommaComparison _ _)
    (HomotopyLimits.cosliceCommaComparison_projection _ _)
    (functorVertex R)).app (Opposite.op ⦋0⦌)
      ⟨leftUnitVertex a, by rw [pinchedConstant_zero]; exact leftUnitVertex_base a⟩

/-- 概要：指定随伴の比較頂点の comma の辺は元の指定単位の代表辺。
方針：固定標的の比較の辺の回収と、指定随伴の coslice 表示の回収を合成する。
規約：元の一次単体を変更しない。
使われ方：前合成の単位成分との Hom 類の一致。 -/
lemma leftUnitComparisonVertex_edge {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : QCatAdjunction (leftVertexFunctor w) R) :
    (HomotopyLimits.commaTargetFiberArrow ((pre (leftVertexFunctor w)).app C.obj)
      (functorVertex (𝟙 C.obj)) (functorVertex R) (leftUnitComparisonVertex a)).edge =
      (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom)).edge := by
  exact (cosliceCommaComparison_fiberArrow_edge ((pre (leftVertexFunctor w)).app C.obj)
    (functorVertex (𝟙 C.obj)) (functorVertex R)
    ⟨leftUnitVertex a, by rw [pinchedConstant_zero]; exact leftUnitVertex_base a⟩).trans
      (leftUnitVertex_edge a)

/-- 概要：指定随伴の比較頂点の comma の矢印の Hom 類は元の単位。
方針：同じ一次単体の表示と元の指定単位の回収を使う。
規約：h Fun 全体における単位の等式。
使われ方：comma の始対象条件を同じ実単位で証明する。 -/
lemma leftUnitComparisonVertex_hom {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : QCatAdjunction (leftVertexFunctor w) R) :
    SSet.Truncated.HomotopyCategory.homMk
      (HomotopyLimits.commaTargetFiberArrow ((pre (leftVertexFunctor w)).app C.obj)
        (functorVertex (𝟙 C.obj)) (functorVertex R) (leftUnitComparisonVertex a)).toTruncated =
      a.unitHom := by
  apply eq_of_heq
  exact (edgeHom_heq _ _ (leftUnitComparisonVertex_edge a)).trans
    (heq_of_eq (functorHomHomotopy_hom a.unitHom))

/-- 概要：元の随伴からの実単位の coslice 頂点は始対象。
方針：同じ指定単位を前合成の随伴の成分として認識し、標準比較で始対象性を反映する。
規約：元の指定単位の頂点を保ち、別の普遍単位の存在では代用しない。
使われ方：普遍単位の全部分空間と随伴単位の条件の同定。 -/
lemma leftUnitVertex_isInitial {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : QCatAdjunction (leftVertexFunctor w) R) : IsInitialVertex (leftUnitVertex a) := by
  let b := precompositionAdjunction (Z := C.obj) a
  have hi := commaTargetFiber_isInitial_of_unitComponent b.unitHom b.unitMappingSpaceCondition
    (functorVertex (𝟙 C.obj)) (leftUnitComparisonVertex a)
    ((leftUnitComparisonVertex_hom a).trans
      (precompositionAdjunction_unitComponent_identity a).symm)
  exact ((leftUnitCosliceComparison_isQCatEquivalence C D w).choose.isInitialVertex_iff
    (leftUnitVertex a)).mpr hi

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
