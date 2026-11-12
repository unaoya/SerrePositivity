module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdgeHomEquality

/-!
概要：図式上で定値な全錐円柱の成分と対角を元の恒等射・図式射へ同定する。
方針：円柱の図式制限を零・一次単体で評価する。
規約：ホモトピー類ではなく射の厳密な式。使われ方：全空間錐の整合式の簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F : I ⥤ KanObject.{u}}
  {c d : JoinCone (kanDiagramCoherentNerve F)} (T : SSet.Homotopy c.val d.val)
  (hD : (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ T.h =
    CartesianMonoidalCategory.fst _ (Δ[1] : SSet.{u + 1}) ≫ kanDiagramCoherentNerve F)

include hD

/-- 概要：定値な図式円柱の成分は元の対象の恒等射。
方針：元の頂点辺を評価。規約：厳密な式。使われ方：各脚の比較の始域の簡約。 -/
lemma kanConeDiagramComponent_eq_id (i : I) : kanConeDiagramComponent T i = 𝟙 (F.obj i) := by
  have hv := (kanDiagramCoherentNerve_vertex F i).trans (spaceInfinityVertex_eq_coherent _)
  have he : (coherentNerveEdge (kanConeDiagramComponent T i)).edge =
      (coherentNerveEdge (𝟙 (F.obj i))).edge := by
    rw [kanConeDiagramComponent_edge]
    have h := homotopyVertexEdge_constant T (joinInr _ _) (kanDiagramCoherentNerve F) hD
      (ULift.up (ComposableArrows.mk₀ i))
    calc
      _ = _ := h
      _ = PinchedHom.constant (coherentNerveVertex (F.obj i)) 1 :=
        congrArg (fun v => PinchedHom.constant v 1) hv
      _ = _ := by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl
  exact eq_of_heq ((heq_of_eq (coherentEdgeHom_edge (kanConeDiagramComponent T i))).symm.trans
    (coherentEdgeHom_of_edge_eq he))

/-- 概要：定値な図式円柱の対角は元の図式射。
方針：図式制限の一次単体と辺の逆対応。規約：厳密な式。使われ方：二次の比較の簡約。 -/
lemma kanConeDiagramDiagonal_eq_map {i j : I} (f : i ⟶ j) :
    kanConeDiagramDiagonal T f = F.map f := by
  have he : (coherentNerveEdge (kanConeDiagramDiagonal T f)).edge =
      (coherentNerveEdge (F.map f)).edge := by
    rw [kanConeDiagramDiagonal_edge]
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hD (Opposite.op ⦋1⦌))
      (show (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) ⊗ Δ[1]) _⦋1⦌ from
        (ULift.up (nerve.edgeMk f).edge, SSet.yonedaEquiv (𝟙 Δ[1])))
    change T.h.app (Opposite.op ⦋1⦌)
      ((joinInr _ _).app (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge),
        SSet.yonedaEquiv (𝟙 Δ[1])) = _ at h
    change T.h.app (Opposite.op ⦋1⦌)
      ((joinInr _ _).app (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge),
        homotopyIntervalEdge.edge) = _
    rw [homotopyIntervalEdge_simplex]
    exact h.trans (strictCoherentDiagram_edge F f)
  exact eq_of_heq ((heq_of_eq (coherentEdgeHom_edge (kanConeDiagramDiagonal T f))).symm.trans
    (coherentEdgeHom_of_edge_eq he))

end SerrePositivity.InfinityCategories.F2
