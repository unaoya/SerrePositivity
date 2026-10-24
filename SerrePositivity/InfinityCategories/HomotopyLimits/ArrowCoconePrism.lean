module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitPrismTotalCocone
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalPrismRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute

/-!
概要：矢印圏内の元の余錐を、同じ両端と頂点辺を持つ prism と照合する。
方針：元の余錐の評価・prism・全 Hom の普遍性を、厳密な射と同型で照合する。
規約：F2 は読み取り専用。使われ方：HTT 5.5.4.5・5.5.4.11 の強飽和性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 矢印圏の元の頂点が表す、対象圏の元の一次単体。 -/
def arrowVertexEdge {X : SSet.{u}} (a : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    X _⦋1⦌ := SSet.yonedaEquiv ((functorVertexEquiv Δ[1] X).symm a)

/-- 元の関手の頂点が表す辺は、uncurry した prism の同じ頂点評価と一致。 -/
lemma uncurry_vertex_prismEvaluation {A X : SSet.{u}}
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (a : A _⦋0⦌) :
    (functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) a) =
      prismVertexEvaluation (uncurry f) a := by
  have he := curry_vertex_prismEvaluation (uncurry f) a
  rw [curry_uncurry] at he
  exact (congrArg (functorVertexEquiv Δ[1] X).symm he).trans
    ((functorVertexEquiv Δ[1] X).symm_apply_apply _)

/-- 元の矢印圏の余錐の prism の底図式は、元の図式の uncurry。 -/
lemma arrowCocone_prism_diagram {K X : SSet.{u}}
    {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCocone r) :
    colimitPrismDiagram (uncurry c.val) = uncurry r := by
  change ((Δ[1] : SSet.{u}) ◁ joinInl K Δ[0]) ≫ uncurry c.val = uncurry r
  rw [← uncurry_natural_left, c.property]

/-- 元の矢印圏の余錐の指定端点評価は、prism の端点余錐と全射で一致。 -/
lemma arrowCocone_endpoint_val {K X : SSet.{u}}
    {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCocone r) (j : Fin 2) :
    (colimitPrismEndpoint (uncurry c.val) j).val =
      (F1B.kanPostcomposeCocone (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)) c).val := by
  change prismEndpoint j (join K Δ[0]) ≫ uncurry c.val =
    c.val ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j)
  have he := curry_evaluateFunctorAt_vertex (uncurry c.val) (stdSimplex.obj₀Equiv.symm j)
  simpa only [curry_uncurry, prismEndpoint] using he.symm

/-- 元の余錐の頂点が表す辺は、その prism の元の頂点辺。 -/
lemma arrowCocone_vertex_prismEdge {K X : SSet.{u}}
    {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCocone r) :
    arrowVertexEdge c.vertex = SSet.yonedaEquiv
      (prismVertexEvaluation (uncurry c.val) (SSet.yonedaEquiv (joinInr K Δ[0]))) := by
  rw [JoinCocone.vertex_eq, SSet.yonedaEquiv_comp]
  exact congrArg SSet.yonedaEquiv
    (uncurry_vertex_prismEvaluation c.val (SSet.yonedaEquiv (joinInr K Δ[0])))

end SerrePositivity.InfinityCategories.HomotopyLimits
