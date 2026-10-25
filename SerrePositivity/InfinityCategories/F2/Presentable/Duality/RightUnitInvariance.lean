module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitData

/-!
概要：固定右の実単位の随伴条件は coslice の可逆辺に沿って保たれる。
方針：元の二単体の合成関係を指定単位の左関手の同型移送と照合する。
規約：全関手圏の core 上での不変性であり、頂点ごとの任意の選択ではない。
使われ方：右ファイバーの像と普遍単位の全部分空間の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定右の実単位の間の辺は、正規化した元の単位の合成構造を与える。
方針：coslice の二単体を保持し、その底の辺を引き戻しの可換性で読む。
規約：元の一次・二次単体を選び直さない。
使われ方：指定単位の h Fun の可換三角形。 -/
def rightUnitCompStruct {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {v v' : RightUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RightUnitCoslice C D w)) v v') :
    SSet.Truncated.Edge.CompStruct (rightUnitEdge v)
      ((rightUnitLeftEdge e).map ((truncation 2).map ((ihom C.obj).map (rightVertexFunctor w))))
      (rightUnitEdge v') := by
  rcases cosliceUnitCompStruct (functorVertex (𝟙 C.obj))
      (e.map ((truncation 2).map (pullback.fst _ ((ihom C.obj).map (rightVertexFunctor w))))) with
    ⟨z, h₂, h₀, h₁⟩
  refine ⟨z, h₂, h₀.trans ?_, h₁⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (pullback.condition (f := sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))) (Opposite.op ⦋1⦌)) e.edge

/-- 概要：固定右の coslice の辺は元の h Fun で単位の三角形を可換にする。
方針：保持した二単体の合成関係を h に移す。
規約：元の単位と左比較の後合成の公式。
使われ方：随伴の移送後の単位を元の実単位と照合する。 -/
lemma rightUnitHom_comp {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {v v' : RightUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RightUnitCoslice C D w)) v v') :
    rightUnitHom v ≫ (hoFunctor.map ((ihom C.obj).map (rightVertexFunctor w))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (rightUnitLeftEdge e)) = rightUnitHom v' :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (rightUnitCompStruct e)

/-- 概要：固定右の coslice の可逆辺は左関手の同型を与える。
方針：底の射影による可逆性の保存を元の関手頂点に正規化する。
規約：元の全関手圏における FunctorIso。
使われ方：指定単位を持つ随伴の左関手を移送する。 -/
def rightUnitLeftIso {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {v v' : RightUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RightUnitCoslice C D w)) v v')
    (he : IsInvertibleEdge e) : FunctorIso (rightUnitLeftFunctor v) (rightUnitLeftFunctor v') := by
  have : IsInvertibleEdge (rightUnitLeftEdge e) :=
    (isInvertibleEdge_congr (e := e.map ((truncation 2).map
      (pullback.snd _ ((ihom C.obj).map (rightVertexFunctor w)))))
      (f := rightUnitLeftEdge e) rfl).mp (he.map _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (rightUnitLeftEdge e))

/-- 概要：固定右の実単位の随伴条件は可逆辺に沿って保たれる。
方針：左関手の同型で随伴を移送し、元の二単体の単位の可換性で同定する。
規約：実単位を任意の別の単位に置き換えない。
使われ方：普遍単位の空間との比較に用いる頂点条件の不変性。 -/
lemma rightUnitCondition_of_invertibleEdge {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {v v' : RightUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RightUnitCoslice C D w)) v v')
    (he : IsInvertibleEdge e)
    (hv : UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v)) :
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor v')
      (G := rightVertexFunctor w) (rightUnitHom v') := by
  have h := unitMappingSpaceCondition_changeLeft
    (C := C.obj) (D := D.obj) (η := rightUnitHom v)
    (L := rightUnitLeftFunctor v) (L' := rightUnitLeftFunctor v')
    (R := rightVertexFunctor w) hv (rightUnitLeftIso e he)
  change UnitMappingSpaceCondition (F := rightUnitLeftFunctor v')
    (G := rightVertexFunctor w) (rightUnitHom v ≫
    (hoFunctor.map ((ihom C.obj).map (rightVertexFunctor w))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (rightUnitLeftEdge e))) at h
  exact (congrArg (UnitMappingSpaceCondition (F := rightUnitLeftFunctor v')
    (G := rightVertexFunctor w)) (rightUnitHom_comp e)).mp h

/-- 概要：固定右の実単位の随伴条件は元の coslice の頂点同型に沿って保たれる。
方針：同型の代表可逆辺を取り、同じ実単位の可換三角形を使う。
規約：元の coslice の h における同型全体を扱う。
使われ方：始対象の一意性による単位条件の移送。 -/
lemma rightUnitCondition_of_vertexIso {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {v v' : RightUnitCoslice C D w _⦋0⦌}
    (i : VertexIso v v')
    (hv : UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v)) :
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor v')
      (G := rightVertexFunctor w) (rightUnitHom v') := by
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective (X := RightUnitCoslice C D w) v v' i.hom
  have hi : IsInvertibleEdge e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e)
    rw [he]
    infer_instance
  exact rightUnitCondition_of_invertibleEdge e hi hv

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
