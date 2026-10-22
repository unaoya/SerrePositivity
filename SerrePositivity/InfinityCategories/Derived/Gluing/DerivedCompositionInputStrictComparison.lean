module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionInputPathPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.StrictPathPullbackMap

/-! 元 Hom 入力上の厳密な合成対角引き戻しと、その同じ定値 path 比較。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedCompositionInputStrictPullback (X Y : DGGluingObject R C D M) :=
  pullback (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)

def dgGluingDerivedCompositionInputStrictPathComparison (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPullback R C D M X Y ⟶
      dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  dgGluingStrictPathPullbackMap _ _

lemma dgGluingDerivedCompositionInputStrictPathComparison_path
    (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ≫
        dgGluingConstantIntervalPath _ :=
  dgGluingStrictPathPullbackMap_path _ _

lemma dgGluingDerivedCompositionInputStrictPathComparison_inputs
    (X Y : DGGluingObject R C D M) :
    dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y ≫ pullback.snd _ _ =
      lift (pullback.fst _ _) (pullback.snd _ _) :=
  dgGluingStrictPathPullbackMap_inputs _ _

end SerrePositivity.InfinityCategories
