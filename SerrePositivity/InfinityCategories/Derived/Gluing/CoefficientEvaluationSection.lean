module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolvedCoefficientAugmentationSquare

/-! 同じ係数 augmentation の自明 Kan fibration と、全単体上の厳密な切断。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

lemma dgGluingResolvedCoefficientEvaluation_surjective (k : ℤ) :
    Function.Surjective ((dgGluingResolvedCoefficientEvaluation R C c N).f k) :=
  dgModuleOutputResolutionAugmentation_degree_surjective R (RightModule R C) C
    (DGFunctor.id (RightModule R C)) N c k

lemma dgGluingCoefficientEvaluation_trivialKanFibration :
    TrivialKanFibration (complexPinchedMap.{u, w}
      (dgGluingResolvedCoefficientEvaluation R C c N)) := by
  let : QuasiIso (dgGluingResolvedCoefficientEvaluation R C c N) :=
    dgGluingResolvedCoefficientEvaluation_quasiIso R C c N
  exact complexPinchedMap_trivialKanFibration _
    (dgGluingResolvedCoefficientEvaluation_surjective R C c N)

def dgGluingCoefficientEvaluationSection :
    complexPinchedSpace.{u, w} (N.obj (Opposite.op c)) ⟶
      complexPinchedSpace.{u, w} ((dgGluingResolvedModule R C N).val.obj (Opposite.op c)) := by
  let : TrivialKanFibration (complexPinchedMap.{u, w}
      (dgGluingResolvedCoefficientEvaluation R C c N)) :=
    dgGluingCoefficientEvaluation_trivialKanFibration R C c N
  exact Classical.choose (trivialKanFibration_exists_section
    (complexPinchedMap.{u, w} (dgGluingResolvedCoefficientEvaluation R C c N)))

lemma dgGluingCoefficientEvaluationSection_augmentation :
    dgGluingCoefficientEvaluationSection.{u, v, w} R C c N ≫
      complexPinchedMap.{u, w} (dgGluingResolvedCoefficientEvaluation R C c N) = 𝟙 _ := by
  let : TrivialKanFibration (complexPinchedMap.{u, w}
      (dgGluingResolvedCoefficientEvaluation R C c N)) :=
    dgGluingCoefficientEvaluation_trivialKanFibration R C c N
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (complexPinchedMap.{u, w} (dgGluingResolvedCoefficientEvaluation R C c N)))

lemma dgGluingCoefficientEvaluationSection_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingCoefficientEvaluationSection.{u, v, w} R C c N) := by
  let : TrivialKanFibration (complexPinchedMap.{u, w}
      (dgGluingResolvedCoefficientEvaluation R C c N)) :=
    dgGluingCoefficientEvaluation_trivialKanFibration R C c N
  have he := isQCatEquivalence_of_trivialKanFibration
    (complexPinchedMap.{u, w} (dgGluingResolvedCoefficientEvaluation R C c N))
  apply IsQCatEquivalence.isSimplicialHomotopyEquivalence
  apply he.cancel_right
  rw [dgGluingCoefficientEvaluationSection_augmentation]
  exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence

end SerrePositivity.InfinityCategories
