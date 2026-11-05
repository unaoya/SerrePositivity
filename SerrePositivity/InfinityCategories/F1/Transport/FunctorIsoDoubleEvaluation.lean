module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoValueCurry
public import SerrePositivity.InfinityCategories.F1B.IsoEndpointNormalization

/-! # 指定された同じ同型の二段階評価を、一つの評価写像による像として保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 対象と添字での二段階評価を、同じ関手空間上の一つの射として固定する。 -/
def doubleFunctorEvaluation {K A Y : SSet.{u}} (x : K _⦋0⦌) (a : A _⦋0⦌) :
    (ihom K).obj ((ihom A).obj Y) ⟶ Y :=
  evaluateFunctorAt x ≫ evaluateFunctorAt a

/-- 同じ二段階評価の頂点は、元の対象値を指定添字で評価した値。 -/
theorem doubleFunctorEvaluation_vertex {K A Y : SSet.{u}} (F : K ⟶ (ihom A).obj Y)
    (x : K _⦋0⦌) (a : A _⦋0⦌) :
    (doubleFunctorEvaluation (Y := Y) x a).app (Opposite.op ⦋0⦌) (functorVertex F) =
      (evaluateFunctorAt a).app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) x) := by
  change (evaluateFunctorAt a).app (Opposite.op ⦋0⦌)
    ((evaluateFunctorAt x).app (Opposite.op ⦋0⦌) (functorVertex F)) = _
  rw [evaluateFunctorAt_functorVertex]

/-- 元の同じ同型を二段階評価した値は、一つの評価写像による同じ像と HEq。 -/
theorem functorIsoDoubleValue_heq_map {K A Y : SSet.{u}}
    {F G : K ⟶ (ihom A).obj Y} (e : FunctorIso F G) (x : K _⦋0⦌) (a : A _⦋0⦌) :
    HEq (VertexIso.map (functorIsoValue e x) (evaluateFunctorAt a))
      (VertexIso.map e (doubleFunctorEvaluation (Y := Y) x a)) := by
  have h := F2.vertexIso_map_heq_of_heq (functorIsoValue e x)
    (VertexIso.map e (evaluateFunctorAt x))
    (evaluateFunctorAt_functorVertex x F).symm (evaluateFunctorAt_functorVertex x G).symm
    (functorIsoValue_heq_map e x) (evaluateFunctorAt a)
  exact h.trans (heq_of_eq (F2.vertexIso_map_comp e (evaluateFunctorAt x) (evaluateFunctorAt a)))

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.doubleFunctorEvaluation := _root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.doubleFunctorEvaluation_vertex := _root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoDoubleValue_heq_map := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoDoubleValue_heq_map
