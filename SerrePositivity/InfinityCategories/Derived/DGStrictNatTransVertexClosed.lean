module
public import SerrePositivity.InfinityCategories.DGNerve.EdgeHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransVertex
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTrans
/-!
概要：同じ実ホモトピーの頂点辺を回収し、全関手射の可逆性へ接続する。
方針：元の閉射・実出力分解・関手空間の点ごとの判定を使う。
規約：出力の射影性と始域の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
open DGNerve.HomotopyComparison
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgStrictNatTrans_homotopy_vertex_cycle
    (A : Type u) [CommRing A] (C E : Type v) [DGCategory A C] [DGCategory A E]
    {F G : DGFunctor A C E} (η : StrictNatTrans F G) (x : C) :
    edgeCycle (simplicialHomotopyVertexEdge η.homotopy (Simplex.vertex x)).toTruncated =
      η.app x := by
  have he : (simplicialHomotopyVertexEdge η.homotopy (Simplex.vertex x)).toTruncated =
      (edgeOfCycle (x := (dgNerve.map F).app (Opposite.op ⦋0⦌) (Simplex.vertex x))
        (y := (dgNerve.map G).app (Opposite.op ⦋0⦌) (Simplex.vertex x)) (η.app x)) := by
    apply Truncated.Edge.ext
    exact dgStrictNatTrans_homotopy_vertex_edge η x
  rw [he, edgeCycle_edgeOfCycle]
lemma dgModuleStrictNatTrans_homotopy_vertex_closed
    (A : Type u) [CommRing A] (C : Type (max (u + 1) v)) (E : Type v)
    [DGCategory A C] [DGCategory A E] [Small.{u} E]
    {F G : DGFunctor A C (RightModule A E)}
    (a : ∀ x, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
      ForgetEnrichment.of (Complex A) (G.obj x))
    (ha : ∀ x y, F.map x y ≫ moduleHomPostcompose A E _ _ _ (a y) =
      G.map x y ≫ moduleHomPrecompose A E _ _ _ (a x)) (x : C) :
    edgeClosed (simplicialHomotopyVertexEdge
      (dgModuleStrictNatTransOfHomNaturality A E a ha).homotopy
        (Simplex.vertex x)).toTruncated = a x := by
  apply (closedHomEquiv A (RightModule A E) _ _).injective
  rw [edgeClosed_cycle, dgStrictNatTrans_homotopy_vertex_cycle]
  rfl
end
end SerrePositivity.InfinityCategories
