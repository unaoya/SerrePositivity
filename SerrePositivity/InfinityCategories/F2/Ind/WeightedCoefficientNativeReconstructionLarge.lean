module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeReconstruction
public import SerrePositivity.InfinityCategories.F2.Ind.CoherentMapRealizationLarge

/-!
概要：同じ native 評価復元の大きい全空間への像と、元の共同実現射との合成を計算する。
方針：小さい復元の厳密な制限公式と、小さい unstraightening 比較の自然性を使う。
規約：元の native 評価図式と復元射を保持。使われ方：元の全評価の相対同型との合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 同じ native 評価復元の大きい全空間への像は、元の全復元の同じ制限。 -/
lemma weightedCoefficientNativeReconstruction_largeMap :
    (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientNativeReconstruction κ F i x) ≫
      (smallLeftUnstraighteningIso D).hom ≫ leftUnstraighteningMap D H k
        (weightedCoefficientNativeEvaluationBase_source κ F i x) =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceIntoTotal F i x) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (twistedElementsReconstruction (weightedDensityProjection F)) ≫
            (smallLeftUnstraighteningIso H).hom := by
  rw [← smallLeftUnstraighteningMap_naturality, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, weightedCoefficientNativeReconstruction_map,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- 同じ native 評価復元と共同実現射の合成は、元の全評価同型の始域の同じ射。 -/
lemma weightedCoefficientNativeReconstruction_realization :
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientNativeReconstruction κ F i x) ≫
      (smallLeftUnstraighteningIso D).hom) ≫ leftUnstraighteningMap D H k
        (weightedCoefficientNativeEvaluationBase_source κ F i x) ≫
          coherentRealizationLargeMap H G (weightedDensityTransformation F).map =
      (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceIntoTotal F i x) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (twistedElementsReconstruction (weightedDensityProjection F) ≫
            (weightedDensityTransformation F).map) ≫ (smallLeftUnstraighteningIso G).hom := by
  rw [← Category.assoc, Category.assoc
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientNativeReconstruction κ F i x)),
    weightedCoefficientNativeReconstruction_largeMap]
  simp only [coherentRealizationLargeMap, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
