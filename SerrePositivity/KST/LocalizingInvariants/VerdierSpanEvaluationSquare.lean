module

public import SerrePositivity.KST.LocalizingInvariants.FractionEvaluationSquare
public import SerrePositivity.KST.LocalizingInvariants.VerdierSpanCanonicalEdges

/-!
概要：元の実分母族に、同じ分数評価の指定比較四角形を適用する。
方針：標準 span 比較の左右辺の厳密回収を元の評価三角形へ代入する。
規約：分母経路・次辺・元の評価辺を全パラメータで保持する。
使われ方：前段の指定最終経路と、次辺の商比較の経路の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 元の実分母族の上の、同じ次辺から分数評価への比較四角形。 -/
def verdierSpanEvaluationSquare : verdierDenominatorSpanFamily i x y ⟶
    (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj C.obj :=
  verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedMarkedSpanInclusion B.obj (weakEquivalences i) x y ≫
      fractionEvaluationSquare q.hom (weakEquivalences i) h.inverts

/-- 比較の下辺は、回収した同じ実次辺の全族の商像。 -/
lemma verdierSpanEvaluationSquare_bottom : verdierSpanEvaluationSquare h x y ≫
    (pre squareBottomEdge).app C.obj =
      verdierDenominatorSpanNumerator i x y ≫
        F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm y) ≫
          (ihom (Δ[1] : SSet.{u})).map q.hom := by
  rw [verdierSpanEvaluationSquare]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_bottom, (pre horn₂₀.ι₀₂).naturality q.hom]
  have he := congrArg (fun f => f ≫ (ihom (Δ[1] : SSet.{u})).map q.hom)
    (verdierDenominatorSpanCanonicalComparison_numerator i x y)
  simpa only [Category.assoc] using he

/-- 比較の上辺は、同じ元の実分数評価。 -/
lemma verdierSpanEvaluationSquare_top : verdierSpanEvaluationSquare h x y ≫
    (pre squareTopEdge).app C.obj =
      verdierDenominatorSpanCanonicalComparison i x y ≫
        fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y ≫
          vertexFiberι ((pre (boundary 1).ι).app C.obj)
            (functorVertex (intervalMappingBoundary
              (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y))) := by
  rw [verdierSpanEvaluationSquare]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_top, fixedFractionEvaluation_inclusion]

/-- 比較の左辺は、前段へ渡す同じ元の実分母の商像。 -/
lemma verdierSpanEvaluationSquare_left : verdierSpanEvaluationSquare h x y ≫
    (pre squareLeftEdge).app C.obj =
      verdierDenominatorSpanProjection i x y ≫ (verdierDenominatorOver i x).ι ≫
        F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) ≫
          (ihom (Δ[1] : SSet.{u})).map q.hom := by
  rw [verdierSpanEvaluationSquare]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_left, (pre horn₂₀.ι₀₁).naturality q.hom]
  have he := congrArg (fun f => f ≫ (ihom (Δ[1] : SSet.{u})).map q.hom)
    (verdierDenominatorSpanCanonicalComparison_denominator i x y)
  simpa only [Category.assoc] using he

/-- 共通実分母の fiber 上で、比較の左辺は同じ一つの実分母の商像に定値。 -/
lemma verdierSpanEvaluationSquare_fiber_left
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
      verdierSpanEvaluationSquare h x y ≫ (pre squareLeftEdge).app C.obj =
    SSet.const (((verdierDenominatorOver i x).ι ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) ≫
      (ihom (Δ[1] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌) d) := by
  rw [verdierSpanEvaluationSquare_left, ← Category.assoc, vertexFiberι_comp, SSet.const_comp]

end SerrePositivity.KST.LocalizingInvariants
