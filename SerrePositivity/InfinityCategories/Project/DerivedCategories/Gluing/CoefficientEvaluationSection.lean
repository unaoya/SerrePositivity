module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ResolvedCoefficientAugmentationSquare

/-! 同じ係数 augmentation の自明 Kan fibration と、全単体上の厳密な切断。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

lemma dgGluingResolvedCoefficientEvaluation_surjective (k : ℤ) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N).f k) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation_degree_surjective R (RightModule R C) C
    (DGFunctor.id (RightModule R C)) N c k

lemma dgGluingCoefficientEvaluation_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation_quasiIso R C c N
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration _
    (dgGluingResolvedCoefficientEvaluation_surjective R C c N)

def dgGluingCoefficientEvaluationSection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, w} (N.obj (Opposite.op c)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, w} ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val.obj (Opposite.op c)) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)) :=
    dgGluingCoefficientEvaluation_trivialKanFibration R C c N
  exact Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)))

lemma dgGluingCoefficientEvaluationSection_augmentation :
    dgGluingCoefficientEvaluationSection.{u, v, w} R C c N ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N) = 𝟙 _ := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)) :=
    dgGluingCoefficientEvaluation_trivialKanFibration R C c N
  exact Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)))

lemma dgGluingCoefficientEvaluationSection_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingCoefficientEvaluationSection.{u, v, w} R C c N) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)) :=
    dgGluingCoefficientEvaluation_trivialKanFibration R C c N
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply he.cancel_right
  rw [dgGluingCoefficientEvaluationSection_augmentation]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
