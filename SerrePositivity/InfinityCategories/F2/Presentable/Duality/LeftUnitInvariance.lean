module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitData

/-!
概要：固定左の実単位の随伴条件は coslice の可逆辺に沿って保たれる。
方針：元の二単体の合成関係を指定単位の右関手の同型移送と照合する。
規約：全関手圏の core 上での不変性であり、頂点ごとの任意の選択ではない。
使われ方：左ファイバーの像と普遍単位の全部分空間の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定左の実単位の間の辺は、正規化した元の単位の合成構造を与える。
方針：coslice の二単体を保持し、その底の辺を引き戻しの可換性で読む。
規約：元の一次・二次単体を選び直さない。
使われ方：指定単位の h Fun の可換三角形。 -/
def leftUnitCompStruct {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {v v' : LeftUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (LeftUnitCoslice C D w)) v v') :
    SSet.Truncated.Edge.CompStruct (leftUnitEdge v)
      ((leftUnitRightEdge e).map ((truncation 2).map ((pre (leftVertexFunctor w)).app C.obj)))
      (leftUnitEdge v') := by
  rcases cosliceUnitCompStruct (functorVertex (𝟙 C.obj))
      (e.map ((truncation 2).map (pullback.fst _ ((pre (leftVertexFunctor w)).app C.obj)))) with
    ⟨z, h₂, h₀, h₁⟩
  refine ⟨z, h₂, h₀.trans ?_, h₁⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (pullback.condition (f := sliceUnderProjection
      (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))) (Opposite.op ⦋1⦌)) e.edge

/-- 概要：固定左の coslice の辺は元の h Fun で単位の三角形を可換にする。
方針：保持した二単体の合成関係を h に移す。
規約：元の単位と右比較の前合成の公式。
使われ方：随伴の移送後の単位を元の実単位と照合する。 -/
lemma leftUnitHom_comp {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {v v' : LeftUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (LeftUnitCoslice C D w)) v v') :
    leftUnitHom v ≫ (hoFunctor.map ((pre (leftVertexFunctor w)).app C.obj)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (leftUnitRightEdge e)) = leftUnitHom v' :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (leftUnitCompStruct e)

/-- 概要：固定左の coslice の可逆辺は右関手の同型を与える。
方針：底の射影による可逆性の保存を元の関手頂点に正規化する。
規約：元の全関手圏における FunctorIso。
使われ方：指定単位を持つ随伴の右関手を移送する。 -/
def leftUnitRightIso {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {v v' : LeftUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (LeftUnitCoslice C D w)) v v')
    (he : IsInvertibleEdge e) : FunctorIso (leftUnitRightFunctor v) (leftUnitRightFunctor v') := by
  have : IsInvertibleEdge (leftUnitRightEdge e) :=
    (isInvertibleEdge_congr (e := e.map ((truncation 2).map
      (pullback.snd _ ((pre (leftVertexFunctor w)).app C.obj))))
      (f := leftUnitRightEdge e) rfl).mp (he.map _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (leftUnitRightEdge e))

/-- 概要：固定左の実単位の随伴条件は可逆辺に沿って保たれる。
方針：右関手の同型で随伴を移送し、元の二単体の単位の可換性で同定する。
規約：実単位を任意の別の単位に置き換えない。
使われ方：普遍単位の空間との比較に用いる頂点条件の不変性。 -/
lemma leftUnitCondition_of_invertibleEdge {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {v v' : LeftUnitCoslice C D w _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (LeftUnitCoslice C D w)) v v')
    (he : IsInvertibleEdge e)
    (hv : UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v)) :
    UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v') (leftUnitHom v') := by
  have h := unitMappingSpaceCondition_changeRight
    (C := C.obj) (D := D.obj) (η := leftUnitHom v)
    (L := leftVertexFunctor w)
    (R := leftUnitRightFunctor v) (R' := leftUnitRightFunctor v') hv (leftUnitRightIso e he)
  change UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v') (leftUnitHom v ≫
    (hoFunctor.map ((pre (leftVertexFunctor w)).app C.obj)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (leftUnitRightEdge e))) at h
  exact (congrArg (UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v')) (leftUnitHom_comp e)).mp h

/-- 概要：固定左の実単位の随伴条件は元の coslice の頂点同型に沿って保たれる。
方針：同型の代表可逆辺を取り、同じ実単位の可換三角形を使う。
規約：元の coslice の h における同型全体を扱う。
使われ方：始対象の一意性による単位条件の移送。 -/
lemma leftUnitCondition_of_vertexIso {C D : PresentableInfinityObject.{u}}
    {w : PrLFunctorSpace C D _⦋0⦌} {v v' : LeftUnitCoslice C D w _⦋0⦌}
    (i : VertexIso v v')
    (hv : UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v) (leftUnitHom v)) :
    UnitMappingSpaceCondition (F := leftVertexFunctor w)
      (G := leftUnitRightFunctor v') (leftUnitHom v') := by
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective (X := LeftUnitCoslice C D w) v v' i.hom
  have hi : IsInvertibleEdge e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e)
    rw [he]
    infer_instance
  exact leftUnitCondition_of_invertibleEdge e hi hv

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
