module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseHomotopyDownNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：同じ合成射の二表示による指定同型の像は宇宙下降後も HEq で一致する。
方針：指定像の合成則と射の等式を保ち、両端を揃えて下降する。
規約：指定同型の値を保持。使われ方：底の表示移送後の局所三角形比較の下降。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ合成射の二表示で指定像を作ると、同じ指定同型の下降を与える。 -/
lemma downVertexIso_map_comp_heq {X Y Z : SSet.{max u v}} {T : SSet.{u}} [Quasicategory T]
    {x y : X _⦋0⦌} (e : VertexIso x y)
    (f : X ⟶ Y) (g : Y ⟶ (SSet.uliftFunctor.{v, u}).obj T)
    (f' : X ⟶ Z) (g' : Z ⟶ (SSet.uliftFunctor.{v, u}).obj T)
    (h : f ≫ g = f' ≫ g') :
    HEq (downVertexIso (VertexIso.map (VertexIso.map e f) g))
      (downVertexIso (VertexIso.map (VertexIso.map e f') g')) := by
  have h₁ := congrArg (fun a => downVertexIso a) (vertexIso_map_comp e f g)
  have h₂ := congrArg (fun a => downVertexIso a) (vertexIso_map_comp e f' g')
  have hx := congrArg (fun k => k.app (Opposite.op ⦋0⦌) x) h
  have hy := congrArg (fun k => k.app (Opposite.op ⦋0⦌) y) h
  exact (heq_of_eq h₁).trans
    ((downVertexIso_heq_of_heq _ _ hx hy (vertexIso_map_heq e h)).trans (heq_of_eq h₂).symm)

end SerrePositivity.InfinityCategories.F2
