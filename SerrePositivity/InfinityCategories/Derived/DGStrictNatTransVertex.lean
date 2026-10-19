module
public import SerrePositivity.InfinityCategories.DGNerve.NatTrans
public import SerrePositivity.InfinityCategories.Derived.TriangleExt
public import SerrePositivity.InfinityCategories.DGNerve.TruncatedEdges
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence

/-! # 厳密 dg 自然変換の実頂点成分

概要：dg 自然変換の nerve ホモトピーの頂点成分は指定した閉零射の辺。
方針：一次単体の二頂点と唯一の Hom 成分を計算する。
規約：実際の辺を同定する。使われ方：成分同型から全関手同型への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable {A : Type u} [CommRing A] {D E : Type v}
  [DGCategory A D] [DGCategory A E] {F G : DGFunctor A D E}

/-- 厳密 dg 自然変換の実頂点辺は、その閉零成分から作った辺。 -/
lemma dgStrictNatTrans_homotopy_vertex_edge (η : StrictNatTrans F G) (x : D) :
    (simplicialHomotopyVertexEdge η.homotopy (Simplex.vertex x)).edge =
      (edgeOfCycle (x := Simplex.vertex (F.obj x))
        (y := Simplex.vertex (G.obj x)) (η.app x)).edge := by
  apply dgSimplex1_ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    change compose A (η.app x).val ((F.map x x).f 0 (unitElement A x).val)
      (add_zero 0) = (η.app x).val
    rw [DGFunctor.map_unitElement, compose_unit]

end SerrePositivity.InfinityCategories
