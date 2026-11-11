module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawUnitComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitPairTransport

/-!
概要：両関手が動く元の実単位の母空間で、指定単位の随伴条件の不変性を証明する。
方針：元の coslice の三角形と、積の辺の二つの whisker への分解を同じ単位で照合する。
規約：全関手圏の core 上の比較であり、随伴の存在を追加仮定にしない。
使われ方：随伴単位の全部分空間の可逆辺の持ち上げ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の実単位の母空間の辺は、左右の比較の対角合成と単位の合成構造を与える。
方針：同じ coslice 二単体の底を、元の両関手の比較の積として読む。
規約：元の一次・二次単体を選び直さない。
使われ方：指定単位と二つの関手同型の移送の照合。 -/
def rawUnitCompStruct {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {v v' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)) v v') :
    SSet.Truncated.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceEdge v)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitLeftEdge e).tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitRightEdge e)).map
        ((truncation 2).map (MonoidalClosed.comp C.obj D.obj C.obj)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceEdge v') := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceUnitCompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))
      (e.map ((truncation 2).map (pullback.fst _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitComposition C D)))) with
    ⟨z, h₂, h₀, h₁⟩
  refine ⟨z, h₂, h₀.trans ?_, h₁⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))))) (Opposite.op ⦋1⦌)) e.edge

/-- 概要：元の実単位の母空間の辺は元の h Fun で単位の三角形を可換にする。
方針：保持した二単体の合成構造を h に移す。
規約：同じ単位と同じ両関手の比較を使う。
使われ方：随伴の移送後の単位を元の実単位と同定する。 -/
lemma rawUnitHom_comp {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {v v' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)) v v') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v ≫ SSet.Truncated.HomotopyCategory.homMk
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitLeftEdge e).tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitRightEdge e)).map
        ((truncation 2).map (MonoidalClosed.comp C.obj D.obj C.obj))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v' :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (rawUnitCompStruct e)

/-- 概要：元の実単位の随伴条件は、両関手が動く母空間の辺に沿って保たれる。
方針：左・右関手の同型に沿って順に随伴を移送し、元の単位の三角形で同定する。
規約：指定された元の実単位を別の単位へ取り替えない。
使われ方：全部分空間の辺の持ち上げの頂点条件。 -/
lemma rawUnitCondition_of_edge {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {v v' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)) v v')
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor v)
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor v')
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor v') (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v') := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitMappingSpaceCondition_changePair (C := C.obj) (D := D.obj)
    (η := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v) (η' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitLeftIso e) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitRightIso e) ?_ hv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitLeftIso_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitRightIso_hom]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v ≫ ·)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.internalHomComposition_tensorEdge_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitLeftEdge e) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rawUnitRightEdge e))).trans
        (rawUnitHom_comp e))

/-- 概要：元の実単位の随伴条件は母空間の頂点同型に沿って保たれる。
方針：同型の代表辺を取り、両関手が動く単位の不変性を使う。
規約：元の母空間の h における同型全体を扱う。
使われ方：全部分空間の可逆辺の終点指定の持ち上げ。 -/
lemma rawUnitCondition_of_vertexIso {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    {v v' : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D _⦋0⦌} (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso v v')
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor v)
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor v) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor v')
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor v') (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v') := by
  obtain ⟨e, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D) v v' i.hom
  exact rawUnitCondition_of_edge e hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
