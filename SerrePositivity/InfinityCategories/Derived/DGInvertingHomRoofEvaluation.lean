module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingHomActionFamily
public import SerrePositivity.InfinityCategories.Derived.DGQuotientHomRoofRepresentation
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofEvaluationEdge
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentEvaluation

/-! # 実屋根表示による商 Hom 作用の全高次の評価比較

概要：商 Hom の指定頂点での作用を、実屋根の指定評価値と選択空間全体上で比較する。
方針：商側の実比較辺と任意標的の実評価辺を、降下の普遍比較へ同時に渡す。
規約：Hom 作用の各選択点でホモトピーを選び直さない。三対象の合成の全高次整合性は別工程。
使われ方：任意反転関手の局所化延長と実屋根計算の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商 Hom の実屋根表示に沿う評価は、全降下選択空間上で実評価値と比較される。 -/
def dgInvertingHomActionFamilyRoofEvaluationIso (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (v : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) _⦋0⦌)
    (R : DGQuotientHomRoofRepresentation A D P x y v) (E : ActualRoofEvaluation F R.roof) :
    FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ evaluateFunctorAt v)
      (SSet.const ((pinchedHomVertexEquiv _ _).symm E.value)) :=
  weakRoofDescentActionEvaluationIso (dgRoofCorrespondenceMap A D P x y)
    (dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F) (dgQuotientFixedHomRoofMap A D P x y)
    (dgActualRoofSpanVertex A D P x y R.roof) v ((pinchedHomVertexEquiv _ _).symm E.value)
    R.comparison (dgActualRoofEvaluationTargetEdge A D P x y F R.roof E)

/-- 任意反転関手の商 Hom 作用の各値は、実屋根の評価と全選択空間上で比較できる。 -/
theorem dgInvertingHomActionFamily_eval_exists (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (v : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) _⦋0⦌) :
    ∃ r : DGActualRoofSpan A D P x y, ∃ E : ActualRoofEvaluation F r,
      Nonempty (FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ evaluateFunctorAt v)
        (SSet.const ((pinchedHomVertexEquiv _ _).symm E.value))) := by
  obtain ⟨R⟩ := dgQuotientHomRoofRepresentation_nonempty A D P hP x y v
  obtain ⟨E⟩ := actualRoofEvaluation_nonempty F hF R.roof
  exact ⟨R.roof, E, ⟨dgInvertingHomActionFamilyRoofEvaluationIso A D P x y F v R E⟩⟩

end SerrePositivity.InfinityCategories
