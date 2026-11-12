module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFirstEdge
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningFamilyOfPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedZeroFaceComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.HomotopyTriangleEdges

/-!
概要：第零面の可変初期値を、第一辺の元の指定変換に対する実現証拠へ接続する。
方針：元の実第一辺の終点を回収し、既存の同じ指定始域比較を全選択で使う。
規約：元の prism と指定比較の値を保持。使われ方：第零面の前合成の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)

/-- 元の全三単体の実第一辺から回収した、同じ標的全空間への全族の射。 -/
def coherentColimitUnitPointedFirstEdgeEndpoint :=
  unstraighteningFamilyPrismEndpoint F Q (SSet.const (coherentVertexOfHomotopy H))
    (coherentColimitUnitPointedFirstEdge B T k)
    (coherentColimitUnitPointedFirstEdge_projection B T k H he)

/-- 元の実第一辺から回収した終点射は、元の底の射影を厳密に保持する。 -/
lemma coherentColimitUnitPointedFirstEdgeEndpoint_projection :
    coherentColimitUnitPointedFirstEdgeEndpoint B T k H he ≫ leftUnstraighteningProjection Q =
      fst (leftUnstraightening F) (coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        leftUnstraighteningProjection F :=
  unstraighteningFamilyPrismEndpoint_projection _ _ _ _ _

/-- 元の実第一辺とその元の実終点は、元の指定変換の全族の証拠を与える。 -/
def coherentColimitUnitPointedFirstEdgeWitness :
    UnstraighteningFamilyWitness F Q (SSet.const (coherentVertexOfHomotopy H))
      (coherentColimitUnitPointedFirstEdgeEndpoint B T k H he) :=
  unstraighteningFamilyOfPrism F Q (SSet.const (coherentVertexOfHomotopy H))
    (coherentColimitUnitPointedFirstEdge B T k)
    (coherentColimitUnitPointedFirstEdge_projection B T k H he)
    (coherentColimitUnitPointedFirstEdge_source B T k)

/-- 第一辺の実終点への比較は、既存の同じ指定始域比較を全選択へ適用したもの。 -/
def coherentColimitUnitPointedFirstEdgeComparison :=
  unstraighteningFamilyOfPrism_comparison F Q (SSet.const (coherentVertexOfHomotopy H))
    (coherentColimitUnitPointedFirstEdge B T k)
    (coherentColimitUnitPointedFirstEdge_projection B T k H he)
    (coherentColimitUnitPointedFirstEdge_source B T k)

/-- 第零面の可変初期値は、同じ元の第一辺の実終点の pointed 成分に厳密に一致。 -/
lemma coherentColimitUnitPointedZeroFace_boundary_endpoint :
    (coherentColimitUnitPointedZeroFaceFamily B T k).boundary =
      (snd (Δ[0] : SSet.{u + 1}) (leftUnstraightening F) ▷
        coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      coherentColimitUnitPointedFirstEdgeEndpoint B T k H he ≫
        pullback.fst pointedSpaceProjection Q := by
  rw [coherentColimitUnitPointedZeroFace_boundary_firstEdge]
  change ((stdSimplex.δ (0 : Fin 2) ▷ leftUnstraightening F) ▷ _) ≫
    (coherentColimitUnitPointedFirstEdgeWitness B T k H he).prism = _
  rw [intervalVertex_one_tensor, comp_whiskerRight, Category.assoc,
    (coherentColimitUnitPointedFirstEdgeWitness B T k H he).target]

end SerrePositivity.InfinityCategories.F2
