module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFiberEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorInitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparisonIso

/-!
概要：任意の底上の切断空間の頂点評価を全 left fibrations 上で coherent に実現する。
方針：既存の豊穣な相対 Hom 評価と fiber 評価を豊穣自然な比較で結ぶ。
規約：通常の射に限らず、全ての相対 Hom の高次単体で自然性を保つ。
使われ方：全対象を同時に動かす高次 transport の始点の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：相対切断の頂点での評価は全 left fibrations に関して豊穣自然。
方針：二つの順の評価を各次数で計算し、fiber の包含後に一致させる。
規約：底と切断の定義域の充填性は不要。
使われ方：切断による transport を全対象上の coherent な変換にする。 -/
def relativeFunctorEvaluationComparison {A B : SSet.{u}} (a : A ⟶ B) (v : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationFiberEvaluationEnriched (a.app (Opposite.op ⦋0⦌) v)) := by
  refine ⟨fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p.val.hom a v, ?_⟩
  intro p q
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, f⟩
  apply Subtype.ext
  rfl

/-- 概要：切断空間の評価は全対象を同時に動かす二つの関手間の実際の辺。
方針：豊穣自然な頂点評価を coherent nerve の関手空間へ実現する。
規約：始点は全切断、終点は実際の fiber の評価。
使われ方：一般の底の単体に沿う大域的な transport の比較。 -/
def relativeFunctorEvaluationComparisonEdge {A B : SSet.{u}}
    (a : A ⟶ B) (v : A _⦋0⦌) :
    SSet.Edge (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk a))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation (a.app (Opposite.op ⦋0⦌) v))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonEdge (relativeFunctorEvaluationComparison a v)

/-- 概要：left anodyne な点からの切断評価は全対象上で大域的な関手同型。
方針：各対象の実際の評価の trivial Kan 性を豊穣比較の同型判定に入れる。
規約：対象ごとの逆写像を独立に選ぶ構成は使わない。
使われ方：単体の始点で fiber と切断の二つの評価を coherent に同一視する。 -/
def relativeFunctorEvaluationComparisonIso {A B : SSet.{u}} (a : A ⟶ B)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk a)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation
        (a.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso (relativeFunctorEvaluationComparison a _)
  intro p
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p.val.hom a
    (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_trivialKanFibration_of_pointMap p.val.hom a i hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
