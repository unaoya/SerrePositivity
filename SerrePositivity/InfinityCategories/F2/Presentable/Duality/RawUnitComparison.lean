module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitCompositionHom
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.UnitCosliceTriangle

/-!
概要：元の実単位の母空間の辺から、左右の関手の可逆比較を回収する。
方針：両関手の core への射影を元の全関手圏に含め、端点を正規化する。
規約：元の比較の一次単体を保持する。
使われ方：両関手が動く単位条件の不変性と射影の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の実単位の母空間の左関手の全族。
方針：底の第一成分を元の全関手圏に含める。
規約：元の高次の関手同値を保持する。
使われ方：母空間の辺の左比較。 -/
def rawUnitLeftUnderlying (C D : PresentableInfinityObject.{u}) :
    RawAdjointUnitSpace C D ⟶ (ihom C.obj).obj D.obj :=
  pullback.snd _ (unitComposition C D) ≫ fst _ _ ≫ leftMappingInclusion C D

/-- 概要：元の実単位の母空間の右関手の全族。
方針：底の第二成分を元の全関手圏に含める。
規約：元の高次の関手同値を保持する。
使われ方：母空間の辺の右比較。 -/
def rawUnitRightUnderlying (C D : PresentableInfinityObject.{u}) :
    RawAdjointUnitSpace C D ⟶ (ihom D.obj).obj C.obj :=
  pullback.snd _ (unitComposition C D) ≫ snd _ _ ≫ rightMappingInclusion D C

/-- 概要：母空間の左関手の頂点表示は元の底の左成分。
方針：元の関手頂点の表示の両逆を使う。
規約：零単体の厳密な等式。
使われ方：左比較辺の端点の正規化。 -/
lemma unitLeftFunctor_vertex {C D : PresentableInfinityObject.{u}}
    (v : RawAdjointUnitSpace C D _⦋0⦌) :
    functorVertex (unitLeftFunctor v) = (rawUnitLeftUnderlying C D).app (Opposite.op ⦋0⦌) v :=
  (functorVertexEquiv C.obj D.obj).apply_symm_apply _

/-- 概要：母空間の右関手の頂点表示は元の底の右成分。
方針：元の関手頂点の表示の両逆を使う。
規約：零単体の厳密な等式。
使われ方：右比較辺の端点の正規化。 -/
lemma unitRightFunctor_vertex {C D : PresentableInfinityObject.{u}}
    (v : RawAdjointUnitSpace C D _⦋0⦌) :
    functorVertex (unitRightFunctor v) = (rawUnitRightUnderlying C D).app (Opposite.op ⦋0⦌) v :=
  (functorVertexEquiv D.obj C.obj).apply_symm_apply _

/-- 概要：実単位の母空間の辺が与える元の左関手の比較辺。
方針：左射影に写し、両端を元の関手頂点に正規化する。
規約：比較の一次単体を保持する。
使われ方：指定単位の左関手の同型による移送。 -/
def rawUnitLeftEdge {C D : PresentableInfinityObject.{u}}
    {v v' : RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RawAdjointUnitSpace C D)) v v') :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj D.obj))
      (functorVertex (unitLeftFunctor v)) (functorVertex (unitLeftFunctor v')) where
  edge := (rawUnitLeftUnderlying C D).app (Opposite.op ⦋1⦌) e.edge
  src_eq := (e.map ((truncation 2).map (rawUnitLeftUnderlying C D))).src_eq.trans
    (unitLeftFunctor_vertex v).symm
  tgt_eq := (e.map ((truncation 2).map (rawUnitLeftUnderlying C D))).tgt_eq.trans
    (unitLeftFunctor_vertex v').symm

/-- 概要：実単位の母空間の辺が与える元の右関手の比較辺。
方針：右射影に写し、両端を元の関手頂点に正規化する。
規約：比較の一次単体を保持する。
使われ方：指定単位の右関手の同型による移送。 -/
def rawUnitRightEdge {C D : PresentableInfinityObject.{u}}
    {v v' : RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RawAdjointUnitSpace C D)) v v') :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom D.obj).obj C.obj))
      (functorVertex (unitRightFunctor v)) (functorVertex (unitRightFunctor v')) where
  edge := (rawUnitRightUnderlying C D).app (Opposite.op ⦋1⦌) e.edge
  src_eq := (e.map ((truncation 2).map (rawUnitRightUnderlying C D))).src_eq.trans
    (unitRightFunctor_vertex v).symm
  tgt_eq := (e.map ((truncation 2).map (rawUnitRightUnderlying C D))).tgt_eq.trans
    (unitRightFunctor_vertex v').symm

/-- 概要：実単位の母空間の辺の左比較は元の関手圏の同型。
方針：Kan 母空間の可逆辺の像を正規化する。
規約：元の全関手圏における FunctorIso。
使われ方：指定単位条件の左関手の同型移送。 -/
def rawUnitLeftIso {C D : PresentableInfinityObject.{u}}
    {v v' : RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RawAdjointUnitSpace C D)) v v') :
    FunctorIso (unitLeftFunctor v) (unitLeftFunctor v') := by
  have he : IsInvertibleEdge e :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (RawAdjointUnitSpace C D)) _
  have : IsInvertibleEdge (rawUnitLeftEdge e) :=
    (isInvertibleEdge_congr (e := e.map ((truncation 2).map (rawUnitLeftUnderlying C D)))
      (f := rawUnitLeftEdge e) rfl).mp (he.map _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (rawUnitLeftEdge e))

/-- 概要：実単位の母空間の辺の右比較は元の関手圏の同型。
方針：Kan 母空間の可逆辺の像を正規化する。
規約：元の全関手圏における FunctorIso。
使われ方：指定単位条件の右関手の同型移送。 -/
def rawUnitRightIso {C D : PresentableInfinityObject.{u}}
    {v v' : RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RawAdjointUnitSpace C D)) v v') :
    FunctorIso (unitRightFunctor v) (unitRightFunctor v') := by
  have he : IsInvertibleEdge e :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (RawAdjointUnitSpace C D)) _
  have : IsInvertibleEdge (rawUnitRightEdge e) :=
    (isInvertibleEdge_congr (e := e.map ((truncation 2).map (rawUnitRightUnderlying C D)))
      (f := rawUnitRightEdge e) rfl).mp (he.map _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (rawUnitRightEdge e))

/-- 概要：左比較の同型の順射は元の左比較辺の Hom 類。
方針：可逆辺からの同型の定義を読む。
規約：元の一次単体を保持する。
使われ方：左右同時の単位移送の式の正規化。 -/
lemma rawUnitLeftIso_hom {C D : PresentableInfinityObject.{u}}
    {v v' : RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RawAdjointUnitSpace C D)) v v') :
    (rawUnitLeftIso e).hom = SSet.Truncated.HomotopyCategory.homMk (rawUnitLeftEdge e) := rfl

/-- 概要：右比較の同型の順射は元の右比較辺の Hom 類。
方針：可逆辺からの同型の定義を読む。
規約：元の一次単体を保持する。
使われ方：左右同時の単位移送の式の正規化。 -/
lemma rawUnitRightIso_hom {C D : PresentableInfinityObject.{u}}
    {v v' : RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (RawAdjointUnitSpace C D)) v v') :
    (rawUnitRightIso e).hom = SSet.Truncated.HomotopyCategory.homMk (rawUnitRightEdge e) := rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
