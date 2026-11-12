module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-!
概要：Kan 複体の二頂点の Yoneda 族のホモトピーから実際の頂点同型を作る。
方針：標準零単体で評価した辺の類は Kan 性により可逆。
規約：指定した両頂点を保持する。
使われ方：余錐の比較ホモトピーを全空間の単位との同型へ移す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：頂点の Yoneda 族のホモトピーは元の両頂点の同型を与える。
方針：零単体での辺を取り、Kan ホモトピー圏の groupoid 性を使う。
規約：同型の存在だけでなく実際の同型。使われ方：指定単位の比較。 -/
def vertexIsoOfYonedaHomotopy {X : SSet.{u}} [KanComplex X] {x y : X _⦋0⦌}
    (H : SSet.Homotopy (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := X) x y := by
  let pt := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have eval (v : X _⦋0⦌) : (SSet.yonedaEquiv.symm v).app _ pt = v := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda (A := (Δ[0] : SSet.{u})) v)
        (Opposite.op ⦋0⦌)) pt
    change (SSet.yonedaEquiv.symm v).app _ pt = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 0 at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] at h
    exact h
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H pt).ofEq (eval x) (eval y)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj X) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
