module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeMappingVertexEdge
public import SerrePositivity.InfinityCategories.F2.Presentable.VertexIsoUniverseLift
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：厳密 dg 入力の native Hom 内の指定同型を、同じ辺の端点固定比較へ送る。
方針：二段の宇宙持ち上げの後、標準 coherent Hom／interval Hom 比較を適用する。
規約：懸垂作用の存在、又は固定商関手間の同型の存在は仮定から結論しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- native Hom の指定同型は、同じ通常の辺の端点固定 interval 比較を与える。 -/
def dgNativeVertexIsoToInterval
    {p q : (dgFunctorNativeMappingSpace R A B).obj (Opposite.op ⦋0⦌)}
    (e : VertexIso (X := dgFunctorNativeMappingSpace R A B) p q) :
    VertexIso
      (intervalMappingVertexOfEdge (dgNativeMappingVertexEdge R A B p))
      (intervalMappingVertexOfEdge (dgNativeMappingVertexEdge R A B q)) := by
  have h : VertexIso
      ((coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up p)))
      ((coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up q))) :=
    (F2.Presentable.liftVertexIso (F2.Presentable.liftVertexIso e)).map
      (coherentHomIntervalComparison A B)
  rw [coherentHomIntervalComparison_vertex, coherentHomIntervalComparison_vertex] at h
  exact h

/-- 元の二つの厳密 dg 射についての、同じ端点固定比較。 -/
def dgNativeInputMapIsoToInterval {f g : A ⟶ B}
    (e : VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down)) :
    VertexIso (intervalMappingVertexOfEdge (coherentNerveEdge f))
      (intervalMappingVertexOfEdge (coherentNerveEdge g)) := by
  have h := dgNativeVertexIsoToInterval R A B e
  rw [dgNativeMappingVertexEdge_vertex, dgNativeMappingVertexEdge_vertex] at h
  exact h

/-- 同じ端点の標準辺の interval 同型は、元の native Hom 内へ反映できる。 -/
def dgIntervalVertexIsoToNative
    {p q : (dgFunctorNativeMappingSpace R A B).obj (Opposite.op ⦋0⦌)}
    (e : VertexIso
      (intervalMappingVertexOfEdge (dgNativeMappingVertexEdge R A B p))
      (intervalMappingVertexOfEdge (dgNativeMappingVertexEdge R A B q))) :
    VertexIso (X := dgFunctorNativeMappingSpace R A B) p q := by
  have h : VertexIso
      ((coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up p)))
      ((coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up q))) := by
    rw [coherentHomIntervalComparison_vertex, coherentHomIntervalComparison_vertex]
    exact e
  have k := (coherentHomIntervalComparison_isQCatEquivalence A B).isFullyFaithful.preimageVertexIso h
  exact downVertexIso (downVertexIso k)

/-- 厳密 dg 射の標準辺の端点固定同型を、同じ二関手の native 頂点同型へ戻す。 -/
def dgIntervalInputMapIsoToNative {f g : A ⟶ B}
    (e : VertexIso (intervalMappingVertexOfEdge (coherentNerveEdge f))
      (intervalMappingVertexOfEdge (coherentNerveEdge g))) :
    VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down) := by
  apply dgIntervalVertexIsoToNative R A B
  rw [dgNativeMappingVertexEdge_vertex, dgNativeMappingVertexEdge_vertex]
  exact e

end SerrePositivity.InfinityCategories
