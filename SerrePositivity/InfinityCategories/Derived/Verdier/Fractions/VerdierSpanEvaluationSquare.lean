module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.FractionEvaluationSquare
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanCanonicalEdges

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 元の実分母族の上の、同じ次辺から分数評価への比較四角形。 -/
def verdierSpanEvaluationSquare : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y ⟶
    (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj C.obj :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ≫
      fractionEvaluationSquare q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts

/-- 比較の下辺は、回収した同じ実次辺の全族の商像。 -/
lemma verdierSpanEvaluationSquare_bottom : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h x y ≫
    (pre squareBottomEdge).app C.obj =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator i x y ≫
        F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm y) ≫
          (ihom (Δ[1] : SSet.{u})).map q.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_bottom, (pre horn₂₀.ι₀₂).naturality q.hom]
  have he := congrArg (fun f => f ≫ (ihom (Δ[1] : SSet.{u})).map q.hom)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_numerator i x y)
  simpa only [Category.assoc] using he

/-- 比較の上辺は、同じ元の実分数評価。 -/
lemma verdierSpanEvaluationSquare_top : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h x y ≫
    (pre squareTopEdge).app C.obj =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
        fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y ≫
          vertexFiberι ((pre (boundary 1).ι).app C.obj)
            (functorVertex (intervalMappingBoundary
              (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_top, fixedFractionEvaluation_inclusion]

/-- 比較の左辺は、前段へ渡す同じ元の実分母の商像。 -/
lemma verdierSpanEvaluationSquare_left : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h x y ≫
    (pre squareLeftEdge).app C.obj =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y ≫ (verdierDenominatorOver i x).ι ≫
        F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) ≫
          (ihom (Δ[1] : SSet.{u})).map q.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_left, (pre horn₂₀.ι₀₁).naturality q.hom]
  have he := congrArg (fun f => f ≫ (ihom (Δ[1] : SSet.{u})).map q.hom)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_denominator i x y)
  simpa only [Category.assoc] using he

/-- 共通実分母の fiber 上で、比較の左辺は同じ一つの実分母の商像に定値。 -/
lemma verdierSpanEvaluationSquare_fiber_left
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h x y ≫ (pre squareLeftEdge).app C.obj =
    SSet.const (((verdierDenominatorOver i x).ι ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x) ≫
      (ihom (Δ[1] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌) d) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_left, ← Category.assoc, vertexFiberι_comp, SSet.const_comp]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluationSquare := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluationSquare_bottom := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluationSquare_fiber_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_fiber_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluationSquare_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluationSquare_top := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluationSquare.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare.eq_1
