module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafEvaluationCoconeComparison

/-!
概要：前層圏の指定余錐の頂点関手を、同じ余錐の全評価頂点として厳密に回収する。
方針：後合成余錐の頂点と関手頂点の評価を計算する。
規約：元の指定余錐と頂点を選び直さない。
使われ方：元の前層余極限頂点で写した全錐の極限性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全余錐を後合成してから頂点を取ると、元の同じ頂点の像になる。 -/
lemma simplicialPostcomposeCocone_vertex {K X Y : SSet.{u}} {r : K ⟶ X}
    (q : JoinCocone r) (f : X ⟶ Y) :
    (F1B.kanPostcomposeCocone f q).vertex = f.app (Opposite.op ⦋0⦌) q.vertex := by
  change SSet.yonedaEquiv (joinInr K Δ[0] ≫ (q.val ≫ f)) =
    f.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (joinInr K Δ[0] ≫ q.val))
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

variable {B C : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C}
  (q : JoinCocone r)

/-- 元の指定前層余錐の頂点が表す、元の反変空間値関手。 -/
def presheafCoconeVertexFunctor :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u} :=
  (presheafInfinityObjectEquiv C).symm q.vertex

/-- 元の全評価余錐の頂点は、同じ元の頂点関手の値そのもの。 -/
lemma presheafCoconeEvaluation_vertex
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌) :
    (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q).vertex =
      (presheafCoconeVertexFunctor q).app (Opposite.op ⦋0⦌) x := by
  rw [simplicialPostcomposeCocone_vertex]
  have h : functorVertex (presheafCoconeVertexFunctor q) = q.vertex :=
    (presheafInfinityObjectEquiv C).apply_symm_apply q.vertex
  rw [← h, evaluateFunctorAt_functorVertex]

/-- 元の同じ coslice 比較は、実際の頂点関手の値を標準全空間余極限頂点へ写す。 -/
def presheafCoconeVertexEvaluationIso
    (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
      IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌) :
    VertexIso ((presheafCoconeVertexFunctor q).app (Opposite.op ⦋0⦌) x)
      (F2.coherentDiagramTotalVertex (r ≫ evaluateFunctorAt x)) := by
  have e := presheafEvaluationColimitVertexIso r q hq x
  rw [presheafCoconeEvaluation_vertex] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
