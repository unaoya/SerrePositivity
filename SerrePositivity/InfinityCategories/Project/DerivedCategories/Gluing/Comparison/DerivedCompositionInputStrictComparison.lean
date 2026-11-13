module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomDerivedCompositionInputPathPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.StrictPathPullbackMap

/-! 元 Hom 入力上の厳密な合成対角引き戻しと、その同じ定値 path 比較。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedCompositionInputStrictPullback (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)

def dgGluingDerivedCompositionInputStrictPathComparison (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPullback R C D M X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap _ _

lemma dgGluingDerivedCompositionInputStrictPathComparison_path
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConstantIntervalPath _ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap_path _ _

lemma dgGluingDerivedCompositionInputStrictPathComparison_inputs
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y ≫ pullback.snd _ _ =
      lift (pullback.fst _ _) (pullback.snd _ _) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStrictPathPullbackMap_inputs _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
