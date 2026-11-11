module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeMappingVertexEdge
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.VertexIsoUniverseLift
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：厳密 dg 入力の native Hom 内の指定同型を、同じ辺の端点固定比較へ送る。
方針：二段の宇宙持ち上げの後、標準 coherent Hom／interval Hom 比較を適用する。
規約：懸垂作用の存在、又は固定商関手間の同型の存在は仮定から結論しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- native Hom の指定同型は、同じ通常の辺の端点固定 interval 比較を与える。 -/
def dgNativeVertexIsoToInterval
    {p q : (dgFunctorNativeMappingSpace R A B).obj (Opposite.op ⦋0⦌)}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R A B) p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge R A B p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge R A B q)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up p)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up q))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.liftVertexIso e)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A B)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex] at h
  exact h

/-- 元の二つの厳密 dg 射についての、同じ端点固定比較。 -/
def dgNativeInputMapIsoToInterval {f g : A ⟶ B}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g)) := by
  have h := dgNativeVertexIsoToInterval R A B e
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge_vertex, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge_vertex] at h
  exact h

/-- 同じ端点の標準辺の interval 同型は、元の native Hom 内へ反映できる。 -/
def dgIntervalVertexIsoToNative
    {p q : (dgFunctorNativeMappingSpace R A B).obj (Opposite.op ⦋0⦌)}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge R A B p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge R A B q))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R A B) p q := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up p)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison A B).app (Opposite.op ⦋0⦌) (ULift.up (ULift.up q))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex]
    exact e
  have k := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_isQCatEquivalence A B).isFullyFaithful.preimageVertexIso h
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso k)

/-- 厳密 dg 射の標準辺の端点固定同型を、同じ二関手の native 頂点同型へ戻す。 -/
def dgIntervalInputMapIsoToNative {f g : A ⟶ B}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := dgFunctorNativeMappingSpace R A B)
      (dgFunctorNativeMappingVertex R A B f.down)
      (dgFunctorNativeMappingVertex R A B g.down) := by
  apply dgIntervalVertexIsoToNative R A B
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge_vertex, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgNativeMappingVertexEdge_vertex]
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
