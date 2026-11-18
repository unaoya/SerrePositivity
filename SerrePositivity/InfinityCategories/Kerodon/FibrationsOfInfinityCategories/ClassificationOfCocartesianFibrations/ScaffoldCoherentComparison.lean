module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationSpanRestrictionWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan

/-!
概要：元のscaffoldを保持する指定spanと、そこでの制限同型を含めてcoherent比較を選ぶ。
方針：既存のscaffoldTransportComparisonSpanと、厳密化の証明に含まれる同じ相対同型を使う。
規約：Kerodon Corollary 5.6.0.6（Tag 028T）、HTT §3.3.2の既存構成の制限の法則。
使われ方：S8の復元比較の選択条件を補う案。既存の比較射の本文はこのファイルでは変更しない。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : Type u} [Category.{u} C] {E : SSet.{u}}
  (p : E ⟶ nerve C) [LeftFibration p]

/-- 元のscaffoldを保持する同じspanに沿って、制限同型も結論に保持する。 -/
lemma exists_scaffoldCoherentComparison :
    let s := (scaffoldTransportComparisonSpan p).toStrictTransportComparisonSpan
    let q := leftUnstraighteningProjection (leftCoherentTransport p)
    ∃ (f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶
        leftUnstraightening (leftCoherentTransport p))
      (hf : f ≫ q = (SSet.uliftFunctor.{u + 1, u}).map p),
      IsPrecompositionEquivalence f ∧ Nonempty (VertexIso
        ((relativeFunctorOverPre q
          (show Over.mk s.coherentBase ⟶ Over.mk ((SSet.uliftFunctor.{u + 1, u}).map p)
            from Over.homMk s.coherentSource s.coherentSource_over)).app (Opposite.op ⦋0⦌)
          (relativeFunctorVertex q ((SSet.uliftFunctor.{u + 1, u}).map p) f hf))
        (relativeFunctorVertex q s.coherentBase s.coherentTarget s.coherentTarget_over)) := by
  dsimp only
  let s := (scaffoldTransportComparisonSpan p).toStrictTransportComparisonSpan
  exact exists_leftFibration_comparison_of_span_with_restriction
    ((SSet.uliftFunctor.{u + 1, u}).map p)
    (leftUnstraighteningProjection (leftCoherentTransport p))
    s.coherentBase s.coherentSource s.coherentTarget
    s.coherentSource_over s.coherentTarget_over
    s.coherentSource_equivalence s.coherentTarget_equivalence

/-- 指定された同じscaffoldの制限条件を含めて選んだcoherent比較射。 -/
def scaffoldCoherentComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ leftUnstraightening (leftCoherentTransport p) :=
  (exists_scaffoldCoherentComparison p).choose

/-- 指定scaffoldに沿う比較射も、元の底を厳密に保つ。 -/
lemma scaffoldCoherentComparison_projection :
    scaffoldCoherentComparison p ≫ leftUnstraighteningProjection (leftCoherentTransport p) =
      (SSet.uliftFunctor.{u + 1, u}).map p :=
  (exists_scaffoldCoherentComparison p).choose_spec.choose

/-- 指定scaffoldに沿う比較射は、元の前合成同値性も保つ。 -/
lemma scaffoldCoherentComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (scaffoldCoherentComparison p) :=
  (exists_scaffoldCoherentComparison p).choose_spec.choose_spec.1

/-- 選択した比較は、同じscaffoldのtarget脚に相対同型で一致する。 -/
def scaffoldCoherentComparison_restrictionIso :
    let s := (scaffoldTransportComparisonSpan p).toStrictTransportComparisonSpan
    let q := leftUnstraighteningProjection (leftCoherentTransport p)
    VertexIso
      ((relativeFunctorOverPre q
        (show Over.mk s.coherentBase ⟶ Over.mk ((SSet.uliftFunctor.{u + 1, u}).map p)
          from Over.homMk s.coherentSource s.coherentSource_over)).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex q ((SSet.uliftFunctor.{u + 1, u}).map p)
          (scaffoldCoherentComparison p) (scaffoldCoherentComparison_projection p)))
      (relativeFunctorVertex q s.coherentBase s.coherentTarget s.coherentTarget_over) :=
  Classical.choice (exists_scaffoldCoherentComparison p).choose_spec.choose_spec.2

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
