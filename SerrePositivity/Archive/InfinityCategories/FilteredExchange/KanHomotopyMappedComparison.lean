module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：元の指定同型の代表辺の像を持つ実ホモトピーは、同じ指定同型の像を表す。
方針：実際の辺の一致で端点も回収し、ホモトピー圏の辺の類を照合する。
規約：代表辺の像を明示。使われ方：元の対角輸送の始点同型作用の関手性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

private lemma truncatedEdgeIso_heq_of_edge_eq {V : SSet.{u}}
    {x y x' y' : V _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj V) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj V) x' y')
    [IsIso (SSet.Truncated.HomotopyCategory.homMk e)]
    [IsIso (SSet.Truncated.HomotopyCategory.homMk e')]
    (h : e.edge = e'.edge) :
    HEq (asIso (SSet.Truncated.HomotopyCategory.homMk e))
      (asIso (SSet.Truncated.HomotopyCategory.homMk e')) := by
  obtain rfl : x = x' := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : y = y' := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  have he : e = e' := by apply SSet.Truncated.Edge.ext; exact h
  cases he
  rfl

/-- 元の代表辺の像を持つ実ホモトピーの同型は、元の指定同型の同じ関手像。 -/
lemma functorIsoOfSimplicialHomotopy_heq_map_of_edge
    {P A B : SSet.{u}} [KanComplex A] [KanComplex B]
    {f g : P ⟶ A} {f' g' : P ⟶ B} (e : FunctorIso f g)
    (q : (ihom P).obj A ⟶ (ihom P).obj B) (H : SSet.Homotopy f' g')
    (h : (functorEdgeOfSimplicialHomotopy H).edge =
      q.app (Opposite.op ⦋1⦌) (FunctorIso.edge e).edge) :
    HEq (functorIsoOfSimplicialHomotopy H) (VertexIso.map e q) := by
  let t := (FunctorIso.edge e).map ((truncation 2).map q)
  haveI ht : IsIso (SSet.Truncated.HomotopyCategory.homMk t) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj ((ihom P).obj B)) _
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy H)) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj ((ihom P).obj B)) _
  have hm : VertexIso.map e q = asIso (SSet.Truncated.HomotopyCategory.homMk t) := by
    apply Iso.ext
    change (SSet.Truncated.mapHomotopyCategory ((truncation 2).map q)).map e.hom = _
    rw [← FunctorIso.edge_homMk e]
    rfl
  rw [hm]
  exact truncatedEdgeIso_heq_of_edge_eq (functorEdgeOfSimplicialHomotopy H) t h

end SerrePositivity.InfinityCategories.F2
