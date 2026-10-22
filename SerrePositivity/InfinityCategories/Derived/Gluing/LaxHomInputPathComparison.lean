module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputStrictForget

/-! 主比較の同じ共通対角を定値全 path として保存済みの入力付き path 模型へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomInputPathComparison (X Y : DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
      dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  dgGluingLaxHomInputStrictComparison R C D M X Y ≫
    dgGluingDerivedCompositionInputStrictPathComparison R C D M X Y

lemma dgGluingLaxHomInputPathComparison_path (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomInputPathComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y ≫
          dgGluingConstantIntervalPath _ := by
  rw [dgGluingLaxHomInputPathComparison, Category.assoc,
    dgGluingDerivedCompositionInputStrictPathComparison_path R C D M X Y,
    ← Category.assoc, dgGluingLaxHomInputStrictComparison_last R C D M X Y]

lemma dgGluingLaxHomInputPathComparison_compositions (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomInputPathComparison R C D M X Y ≫ pullback.snd _ _ =
      lift (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
        (dgGluingLaxHomFirstCompositionInputLift R C D M X Y) := by
  rw [dgGluingLaxHomInputPathComparison, Category.assoc,
    dgGluingDerivedCompositionInputStrictPathComparison_inputs R C D M X Y, comp_lift,
    dgGluingLaxHomInputStrictComparison_last R C D M X Y,
    dgGluingLaxHomInputStrictComparison_first R C D M X Y]

lemma dgGluingLaxHomInputPathComparison_raw (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomInputPathComparison R C D M X Y ≫ pullback.snd _ _ ≫
      (dgGluingDerivedLastCompositionInputProjection R C D M X Y ⊗ₘ
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y) =
      lift
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  rw [← Category.assoc, dgGluingLaxHomInputPathComparison_compositions R C D M X Y]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst]
    exact dgGluingLaxHomLastCompositionInputLift_input R C D M X Y
  · simp only [Category.assoc, tensorHom_snd, lift_snd]
    exact dgGluingLaxHomFirstCompositionInputLift_input R C D M X Y

end SerrePositivity.InfinityCategories
