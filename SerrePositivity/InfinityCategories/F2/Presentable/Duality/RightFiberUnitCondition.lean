module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitContractible

/-!
概要：元の右射影の固定ファイバーの比較は指定単位の随伴条件を保つ。
方針：左右の関手と元の単位辺を回収し、同じ単位の条件を端点の等式で移す。
規約：元の実単位の高次単体を変更しない。
使われ方：元の右ファイバーと可縮な固定右単位空間の同型の順方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の右ファイバーの比較は左関手を保つ。
方針：全関手圏への第二射影の等式を関手頂点の表示の逆へ移す。
規約：元の単体集合の射としての左関手の等式。
使われ方：指定単位条件の左端点の照合。 -/
lemma rightFiberComparison_leftFunctor (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) (x : vertexFiber (adjointUnitRight C D) w _⦋0⦌) :
    rightUnitLeftFunctor ((adjointUnitRightFiberToCoslice C D w).app (Opposite.op ⦋0⦌) x) =
      unitLeftFunctor x.val.val.val := by
  exact congrArg (fun z ↦ (functorVertexEquiv C.obj D.obj).symm z)
    (congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
      (adjointUnitRightFiberToCoslice_left C D w))

/-- 概要：元の右ファイバーの右関手は固定した元の右関手。
方針：ファイバーの零次条件を右頂点の関手表示へ移す。
規約：右関手の厳密な等式。
使われ方：指定単位条件の右端点の照合。 -/
lemma rightFiberComparison_rightFunctor (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) (x : vertexFiber (adjointUnitRight C D) w _⦋0⦌) :
    unitRightFunctor x.val.val.val = rightVertexFunctor w.val := by
  have h : (adjointUnitRight C D).app (Opposite.op ⦋0⦌) x.val = w :=
    x.property.trans (pinchedConstant_zero w)
  exact congrArg (fun z : PrRMappingSpace D C _⦋0⦌ ↦ rightVertexFunctor z.val) h

/-- 概要：元の右ファイバーの比較は元の単位の一次単体を保つ。
方針：coslice 成分の保存を元の辺の回収に適用する。
規約：両端の正規化以外に単位を変更しない。
使われ方：元の指定単位の Hom 類を照合する。 -/
lemma rightFiberComparison_unitEdge (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) (x : vertexFiber (adjointUnitRight C D) w _⦋0⦌) :
    (rightUnitEdge ((adjointUnitRightFiberToCoslice C D w).app (Opposite.op ⦋0⦌) x)).edge =
      (unitCorrespondenceEdge x.val.val.val).edge := by
  exact congrArg (fun s ↦ (sliceUnderVertexEdge (functorVertex (𝟙 C.obj)) s).edge)
    (congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
      (adjointUnitRightFiberToCoslice_unit C D w))

/-- 概要：元の右ファイバーの比較後の実単位は同じ随伴条件を満たす。
方針：左右の元の関手の回収と同じ単位辺の Hom 類の回収で条件を移す。
規約：新たな随伴単位の存在を仮定しない。
使われ方：可縮な固定右単位空間への比較の持ち上げ。 -/
lemma rightFiberComparison_unitCondition (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) (x : vertexFiber (adjointUnitRight C D) w _⦋0⦌) :
    UnitMappingSpaceCondition
      (F := rightUnitLeftFunctor
        ((adjointUnitRightFiberToCoslice C D w).app (Opposite.op ⦋0⦌) x))
      (G := rightVertexFunctor w.val)
      (rightUnitHom ((adjointUnitRightFiberToCoslice C D w).app (Opposite.op ⦋0⦌) x)) := by
  have he := edgeHom_heq
    (rightUnitEdge ((adjointUnitRightFiberToCoslice C D w).app (Opposite.op ⦋0⦌) x))
    (unitCorrespondenceEdge x.val.val.val) (rightFiberComparison_unitEdge C D w x)
  exact (unitCondition_transport (rightFiberComparison_leftFunctor C D w x)
    (rightFiberComparison_rightFunctor C D w x).symm _ _ he).mpr
      (fullSubcomplexOnVertices_vertex x.val.val)

/-- 概要：元の右ファイバーから固定右の随伴単位の全部分空間への比較。
方針：元の coslice 比較を、同じ指定単位条件によって全部分複体へ持ち上げる。
規約：元の単位の全高次単体を保持する単体集合の射。
使われ方：固定右の可縮単位空間との同型の順方向。 -/
def rightFiberToAdjointUnitSubspace (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    vertexFiber (adjointUnitRight C D) w ⟶ RightAdjointUnitSubspace C D w.val :=
  fullSubcomplexLift _ (adjointUnitRightFiberToCoslice C D w)
    (rightFiberComparison_unitCondition C D w)

/-- 概要：元の右ファイバーから可縮な固定右単位の core への比較。
方針：Kan ファイバーの core 同型と、随伴単位の全部分空間への比較を使う。
規約：元の実単位の core 上の射であり、頂点の選択だけではない。
使われ方：固定右単位空間との同型の順方向。 -/
def rightFiberToAdjointUnitSpace (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    vertexFiber (adjointUnitRight C D) w ⟶ RightAdjointUnitSpace C D w.val :=
  (quasicategoryCoreIsoOfKan _).inv ≫ quasicategoryCoreMap (rightFiberToAdjointUnitSubspace C D w)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
