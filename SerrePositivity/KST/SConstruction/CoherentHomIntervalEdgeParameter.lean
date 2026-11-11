module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-! # 元の豊穣 Hom の実辺と標準区間比較のパラメータ
概要：元の Hom 辺を持ち上げ、標準 coherent 区間比較の同じ入力として保持する。
方針：抽象的な辺の段階で Yoneda の自然性を計算し、具体的 dg データを展開しない。
規約：辺の射や充填を選び直さない。使われ方：固定 dg 入力の標準比較四角形。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
  (f g : X ⟶ Y)
  (d : (SimplicialCategory.sHom X Y).Edge
    (SimplicialCategory.homEquiv' X Y f) (SimplicialCategory.homEquiv' X Y g))

/-- 同じ Hom 辺を、標準 coherent 比較の同じ持ち上げた入力区間として読む。 -/
def coherentHomIntervalEdgeParameter : (Δ[1] : SSet.{max u v}) ⟶
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) :=
  SSet.yonedaEquiv.symm (ULift.up d.edge)

/-- 同じ元の Hom 辺を標準 coherent 区間 Hom に写し、元の通常射で端点を表示する。 -/
def coherentHomIntervalEdgeFromParameter :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g)) := by
  let a : ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).Edge
      (ULift.up (SimplicialCategory.homEquiv' X Y f))
      (ULift.up (SimplicialCategory.homEquiv' X Y g)) :=
    Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge d.toTruncated)
  exact (a.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y)).ofEq
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply])
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply])

/-- 元の区間 Hom 辺の Yoneda 族は、元の入力区間と標準比較の合成そのもの。 -/
lemma coherentHomIntervalEdge_parameter :
    SSet.yonedaEquiv.symm (coherentHomIntervalEdgeFromParameter f g d).edge =
      coherentHomIntervalEdgeParameter f g d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y := by
  have h : (coherentHomIntervalEdgeFromParameter f g d).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y).app _ (ULift.up d.edge) := rfl
  rw [h]
  exact (SSet.yonedaEquiv_symm_comp
    (X := (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))
    (n := ⦋1⦌) (ULift.up d.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y)).symm

end SerrePositivity.KST.SConstruction
