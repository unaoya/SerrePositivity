module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGInvertingHomActionFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientHomRoofRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofEvaluationEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.WeakRoofDescentEvaluation

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商 Hom の実屋根表示に沿う評価は、全降下選択空間上で実評価値と比較される。 -/
def dgInvertingHomActionFamilyRoofEvaluationIso (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋0⦌)
    (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientHomRoofRepresentation A D P x y v) (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofEvaluation F R.roof) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)
      (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm E.value)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentActionEvaluationIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanVertex A D P x y R.roof) v ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm E.value)
    R.comparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofEvaluationTargetEdge A D P x y F R.roof E)

/-- 任意反転関手の商 Hom 作用の各値は、実屋根の評価と全選択空間上で比較できる。 -/
theorem dgInvertingHomActionFamily_eval_exists (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋0⦌) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y, ∃ E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofEvaluation F r,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)
        (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm E.value))) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientHomRoofRepresentation_nonempty A D P hP x y v
  obtain ⟨E⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.actualRoofEvaluation_nonempty F hF R.roof
  exact ⟨R.roof, E, ⟨dgInvertingHomActionFamilyRoofEvaluationIso A D P x y F v R E⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
