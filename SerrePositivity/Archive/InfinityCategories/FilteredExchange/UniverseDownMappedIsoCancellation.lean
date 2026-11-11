module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseHomotopyDownNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：縮小・宇宙下降・後合成の指定像を、後合成して持ち上げた同じ指定像の下降へ揃える。
方針：下降の自然性と表示同型の往復を、頂点等式を明示して指定同型へ適用する。
規約：端点等式と指定類を保持。使われ方：旧 prism 出力関手と明示的な fiber 評価の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 下降後の後合成は、同じ後合成と表示同型を持ち上げた指定像を戻して下降する操作。 -/
lemma downVertexIso_map_iso_cancel {R T : SSet.{u}} [Quasicategory R] [Quasicategory T]
    {X U : SSet.{max u v}} (g : X ⟶ (SSet.uliftFunctor.{v, u}).obj R) (Q : R ⟶ T)
    (E : (SSet.uliftFunctor.{v, u}).obj T ≅ U) {x y : X _⦋0⦌} (e : VertexIso x y) :
    HEq (VertexIso.map (downVertexIso (VertexIso.map e g)) Q)
      (downVertexIso (VertexIso.map
        (VertexIso.map e (g ≫ (SSet.uliftFunctor.{v, u}).map Q ≫ E.hom)) E.inv)) := by
  let f := g ≫ (SSet.uliftFunctor.{v, u}).map Q ≫ E.hom
  have hc : f ≫ E.inv = g ≫ (SSet.uliftFunctor.{v, u}).map Q := by
    simp only [f, Category.assoc, E.hom_inv_id, Category.comp_id]
  have hm : HEq (VertexIso.map (VertexIso.map e g) ((SSet.uliftFunctor.{v, u}).map Q))
      (VertexIso.map (VertexIso.map e f) E.inv) :=
    (heq_of_eq (vertexIso_map_comp e g _)).trans
      ((vertexIso_map_heq e hc.symm).trans
        (heq_of_eq (vertexIso_map_comp e f E.inv).symm))
  have hx : ((SSet.uliftFunctor.{v, u}).map Q).app (Opposite.op ⦋0⦌)
      (g.app (Opposite.op ⦋0⦌) x) = E.inv.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) x) :=
    congrArg (fun k : X ⟶ (SSet.uliftFunctor.{v, u}).obj T => k.app (Opposite.op ⦋0⦌) x) hc.symm
  have hy : ((SSet.uliftFunctor.{v, u}).map Q).app (Opposite.op ⦋0⦌)
      (g.app (Opposite.op ⦋0⦌) y) = E.inv.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) y) :=
    congrArg (fun k : X ⟶ (SSet.uliftFunctor.{v, u}).obj T => k.app (Opposite.op ⦋0⦌) y) hc.symm
  exact (heq_of_eq (downVertexIso_map (VertexIso.map e g) Q)).trans
    (downVertexIso_heq_of_heq _ _ hx hy hm)

end SerrePositivity.InfinityCategories.F2
