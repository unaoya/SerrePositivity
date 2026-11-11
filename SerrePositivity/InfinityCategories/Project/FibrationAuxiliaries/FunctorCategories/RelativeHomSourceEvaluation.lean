module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairLeftInclusion
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverTestFamily

/-!
概要：標準 Hom の反変な族を固定したテスト標的で評価する。
方針：共同評価を積の第一の因子へ制限し、curry の頂点評価を使う。
規約：評価の等式は始域の全対象・全高次を保つ厳密な等式。
使われ方：strict 比較空間から実際の coherent 変換空間への比較の評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- テスト標的を固定した、始域に反変な相対 Hom の豊穣評価。 -/
def relativeHomSourceEvaluationEnriched {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverObject B)) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    EnrichedFunctor SSet.{u} Cᵒᵖ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairLeftInclusion Cᵒᵖ r).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestBifunctor F)

/-- Hom 関手の族をテスト標的で評価すると、始域に反変な相対 Hom の共同評価。 -/
lemma simplicialOverTestFamily_evaluate {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialOverObject B)) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex r) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (relativeHomSourceEvaluationEnriched F r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverTestFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  change (lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex r)) (𝟙 (SimplicialNerve Cᵒᵖ)) ≫
    (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) (SimplicialNerve Cᵒᵖ)).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom Cᵒᵖ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialOverJointTest F = _
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity]
  rw [lift_braiding_hom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom_left]
  rfl

/-- 標準 Hom の族の評価も、同じ相対 Hom の実際の豊穣作用を回収する。 -/
lemma leftFibrationHomTestFamily_evaluate {B : SSet.{u}} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex r) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) r) :=
  simplicialOverTestFamily_evaluate (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) r

/-- 固定標的の豊穣作用は、相対射の族による実際の前合成の同時評価。 -/
lemma relativeHomSourceEvaluationEnriched_map {B : SSet.{u}}
    (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    uncurry ((relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) r).map
      (Opposite.op q) (Opposite.op a)) =
    (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r.val.hom q.val.hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a.val q.val r.val := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨g, f⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a.val r.val r.val).app n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a.val q.val r.val).app n (f, g),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity r.val).app n PUnit.unit) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a.val q.val r.val).app n (f, g)
  exact congrArg (fun k ↦ k.app n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a.val q.val r.val).app n (f, g)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_id a.val r.val)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
