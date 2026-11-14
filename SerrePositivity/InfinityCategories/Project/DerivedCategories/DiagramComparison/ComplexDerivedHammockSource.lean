module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedEvaluation
public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockSource

/-!
概要：指定された複体の実評価と、既存の全複体hammockの導来源を照合する。
方針：同じ閉零射と一点半自由評価を展開し、既存の局所化の指定全関手同型を運ぶ。
規約：元の評価を変更せず、全単体上で同じ射を比較する。
使われ方：HTT 4.2.4.4の加群版での、値の写像空間の比較への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.EInfinity.PowerOperation
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- 同じ閉零射と半自由評価を使う、二つの通常導来源の全単体上の等式。 -/
lemma complexDerivedEvaluation_eq_ordinarySource :
    complexDerivedEvaluation A = complexOrdinaryDerivedSource A := by
  rfl

/-- 元の複体hammockの比較は、指定された同じ実評価へ全関手同型で戻る。 -/
def complexDerivedEvaluation_hammockSourceIso :
    FunctorIso (complexHammockSource A ≫ complexHammockDerivedComparison A)
      (complexRelativeNerveDown A ≫ complexDerivedEvaluation A) := by
  rw [complexDerivedEvaluation_eq_ordinarySource]
  exact complexHammockDerivedComparison_sourceIso A

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
