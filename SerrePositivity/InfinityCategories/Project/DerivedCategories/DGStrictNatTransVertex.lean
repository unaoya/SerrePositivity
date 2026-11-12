module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleExt
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedEdges
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-! # 厳密 dg 自然変換の実頂点成分

概要：dg 自然変換の nerve ホモトピーの頂点成分は指定した閉零射の辺。
方針：一次単体の二頂点と唯一の Hom 成分を計算する。
規約：実際の辺を同定する。使われ方：成分同型から全関手同型への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D E : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E}

/-- 厳密 dg 自然変換の実頂点辺は、その閉零成分から作った辺。 -/
lemma dgStrictNatTrans_homotopy_vertex_edge (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge η.homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj x)) (η.app x)).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex1_ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    change _root_.SerrePositivity.DifferentialGraded.compose A (η.app x).val ((F.map x x).f 0 (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val)
      (add_zero 0) = (η.app x).val
    rw [_root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement, _root_.SerrePositivity.DifferentialGraded.compose_unit]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
